(in-package "ACL2S")

(acl2::program)

(defun make-defunbc-body/logic (name formals ic oc body wrld make-staticp)
  (b* ((with-ic-body
        (if (or (equal ic 't) (equal ic ''t))
            body
          `(if ,ic
               ,body
             (defunbc-undefined (quote ,name) (list ,@formals))))))
      (if make-staticp
          with-ic-body
        (add-output-contract-check with-ic-body oc name formals wrld))))

(defun make-generic-typed-defunbc-events
    (name formals ic oc decls body kwd-alist wrld make-staticp)
  "Generate events which simulate a typed ACL2s language."
  (b* ((recursivep (defdata::get1 :recursivep kwd-alist))
       (lbody (make-defunbc-body/logic name formals ic oc body wrld make-staticp))
       (ebody (make-defun-body/exec name formals oc body wrld make-staticp))
       (fun-ind-name (make-sym name 'induction-scheme-from-definition))
       (ind-scheme-name (make-sym name 'induction-scheme)))
      (append
       (and recursivep
            `((defun ,fun-ind-name ,formals
                ,@decls
                ,(replace-in-term name fun-ind-name lbody))))
       (and recursivep
            `((defthm ,ind-scheme-name
                t
                :rule-classes ((:induction :pattern ,(cons name formals)
                                           :condition ,ic
                                           :scheme ,(cons fun-ind-name formals))))))
       `((with-output
          :stack :push :off :all
          (make-event
           (let ((controller-alist (acl2::controller-alist ',name (w state))))
             `(with-output
               :stack :pop
               (defthm ,(make-sym ',name 'definition-rule)
                 (implies ,',ic
                          (equal ,(cons ',name ',formals)
                                 ,',ebody))
                 :hints (("Goal" :use ,',name :in-theory nil))
                 :rule-classes ((:definition
                                 ,@(if ,recursivep
                                       `(:controller-alist
                                         ((,',name ,@controller-alist)))
                                     nil)))))))))
       `((in-theory (disable (:definition ,name)
                             ,@(and recursivep
                                    `((:induction ,name)
                                      (:definition ,fun-ind-name)))))))))

(acl2::logic)

(encapsulate
 ((defunbc-undefined (x y) t :guard (and (symbolp x) (true-listp y))))
 (local (defun defunbc-undefined (x y) (declare (ignorable x y)) nil))
 (defthm defunbc-undefined-booleanp
   (booleanp (defunbc-undefined x y))
   :rule-classes ((:type-prescription) (:rewrite))))

(defun defunbc-undefined-attached (name args)
  (declare (xargs :guard (and (symbolp name) 
                              (true-listp args))))
  (cw "~|**Input contract violation**: ~x0 ~%" `(,name ,@args))
)

(defun defunbc-undefined-attached-nil (name args)
  (declare (xargs :guard (and (symbolp name) 
                              (true-listp args))))
  (declare (ignorable name args))
  nil)

(make-event
 (if *print-contract-violations*
     '(defattach defunbc-undefined defunbc-undefined-attached)
   '(defattach defunbc-undefined defunbc-undefined-attached-nil))
 :check-expansion t)

(defun make-defunbc-no-guard-ev (name formals ic oc decls body wrld make-staticp)
  (declare (xargs :mode :program))
  (b* ((lbody (make-defunbc-body/logic name formals ic oc body wrld make-staticp))
       (ebody (make-defun-body/exec name formals oc body wrld make-staticp))
       (decls (update-xargs-decls decls :guard ic)))
      (list* 'ACL2::DEFUN name formals
             (append decls (list (list 'ACL2::MBE :logic lbody :exec ebody))))))

(defun make-contractbc-defthm (name oc kwd-alist)
  (b* ((instructions (defdata::get1 :instructions kwd-alist))
       (otf-flg (defdata::get1 :otf-flg kwd-alist))
       (hints (defdata::get1 :function-contract-hints kwd-alist))
       (rule-classes (defdata::get1 :rule-classes kwd-alist))
   ;;; (body (if (or (equal ic 't) (equal ic ''t)) oc `(implies ,ic ,oc)))
   ;;; Not the above since I know I always get a boolean
       )
    `(DEFTHM ,(make-sym name 'CONTRACT)
       ,oc
       ,@(and hints `(:HINTS ,hints))
       ,@(and rule-classes `(:RULE-CLASSES ,rule-classes))
       ,@(and otf-flg `(:OTF-FLG ,otf-flg))
       ,@(and instructions `(:INSTRUCTIONS ,instructions)))))

(defun make-contractbc-ev (name formals oc kwd-alist make-staticp)
  (b* ((function-contract-strictp (defdata::get1 :function-contract-strictp kwd-alist))
       (contract-name (make-sym name 'CONTRACT))
       (recursivep (defdata::get1 :recursivep kwd-alist))
 ;;;   (body (if (or (equal ic 't) (equal ic ''t)) oc `(implies ,ic ,oc)))
 ;;;   always get a boolean
       (try-first-with-induct-and-tp 
        `(DEFTHM ,contract-name
           ,oc
           ,@(and recursivep `(:hints (("Goal" :induct ,(cons name formals)))))
           :rule-classes (:rewrite
                          :type-prescription
                          ;; Let ACL2 decide the typed-term
                          ;;(:type-prescription :typed-term ,(cons name formals))
                          )))
       (try-with-induct
        `(DEFTHM ,contract-name
           ,oc
           :hints (("Goal" :induct ,(cons name formals)))))
       (final-contract-defthm (make-contractbc-defthm name oc kwd-alist)))
    (if (or make-staticp function-contract-strictp)
       `(MAKE-EVENT 
         '(:OR 
           ,try-first-with-induct-and-tp
           ,@(and recursivep (list try-with-induct))
           ,final-contract-defthm))
      ;;else
      `(MAKE-EVENT 
        '(:OR ,try-first-with-induct-and-tp
              ,@(and recursivep (list try-with-induct))
              ,final-contract-defthm
              (value-triple :CONTRACT-FAILED))))))

(defun defunbc-events-with-staticp-flag
    (name formals ic oc decls body kwd-alist wrld make-staticp)
  "Depending on flag make-staticp, we generate either events with static contract or with dynamic contract (run-time checking)."
  (declare (xargs :mode :program))
  (if (defdata::get1 :program-mode-p kwd-alist)
      '(mv t nil state) ;skip/abort
    (b* ((defun/ng (make-defunbc-no-guard-ev name formals ic oc decls body wrld make-staticp))
         (contract-defthm (make-contractbc-ev name formals oc kwd-alist make-staticp))
         (verify-guards-ev (make-verify-guards-ev name kwd-alist))
         (timeout-secs (defdata::get1 :timeout kwd-alist))
         (test-subgoals-p (eq t (defdata::get1 :testing-enabled kwd-alist))))
        `(with-prover-time-limit
          ,timeout-secs
          (encapsulate 
           nil
           (abort-this-event-sequence
            ,(defdata::get1 :start-time kwd-alist)
            ,timeout-secs
            ,(defdata::get1 :debug kwd-alist))
           ,@(and test-subgoals-p '((local (acl2s-defaults :set testing-enabled nil))))
           (local (acl2s-defaults :set print-cgen-summary nil))
           (with-output
            :off :all
            (make-event (er-progn
                         (assign defunc-failure-reason :termination)
                         (value '(value-triple :invisible)))))
           (with-output :on (summary) :summary (acl2::form acl2::time)
                        (with-prover-time-limit ,(* 4/5 timeout-secs) ,defun/ng))
           (with-output
            :off :all
            (make-event (er-progn
                         (assign defunc-failure-reason :contract)
                         (value '(value-triple :invisible)))))
           ,@(and test-subgoals-p '((local (acl2s-defaults :set testing-enabled t)))) 
           ,@(and contract-defthm 
                  `((with-output
                     :on (summary) :summary (acl2::form acl2::time) 
                     (with-prover-time-limit ,(* 1/3 timeout-secs) ,contract-defthm))))
           ,@(and test-subgoals-p '((local (acl2s-defaults :set testing-enabled nil))))
           (with-output
            :off :all
            (make-event (er-progn
                         (assign defunc-failure-reason :guards)
                         (value '(value-triple :invisible)))))
           (with-output
            :on (summary) :summary (acl2::form acl2::time) 
            (with-prover-time-limit ,(* 1/3 timeout-secs) ,verify-guards-ev))
           (with-output
            :off :all
            (make-event (er-progn
                         (assign defunc-failure-reason :generic-ev)
                         (value '(value-triple :invisible)))))
           ,@(make-generic-typed-defunbc-events
              name formals ic oc decls body kwd-alist wrld make-staticp)
           (with-output
            :off :all
            (make-event (er-progn
                         (assign defunc-failure-reason :none)
                         (value '(value-triple :invisible)))))
           ,(print-summary-ev name oc kwd-alist))))))

(defun program-mode-defunbc-events (name formals ic oc decls body kwd-alist wrld)
  (declare (xargs :mode :program))
  (b* ((dynamic-body (make-defunbc-body/logic name formals ic oc body wrld nil))
       (decls (update-xargs-decls decls :guard ic :mode :program)))
      `(with-output 
        :on (summary) :summary (acl2::form)
        (PROGN
         (defun ,name ,formals
           ,@decls
           ,dynamic-body)
         ,(print-summary-ev name oc kwd-alist)))))

(defun eventsrc-seen-list (parsed wrld make-staticp)
  (declare (xargs :mode :program))
  (b* (((list name formals ic oc decls body kwd-alist) parsed)
       (defun/ng (make-defunbc-no-guard-ev name formals ic oc decls body wrld make-staticp))
       (contract-defthm (make-contractbc-defthm name oc kwd-alist))
       (verify-guards-ev (make-verify-guards-ev name kwd-alist))
       (function-contract-strictp (defdata::get1 :function-contract-strictp kwd-alist))
       (body-contracts-strictp (defdata::get1 :body-contracts-strictp kwd-alist)))
    (append (list defun/ng)
            (and function-contract-strictp contract-defthm (list contract-defthm))
            (and body-contracts-strictp (list verify-guards-ev)))))

(defun defunbc-events (parsed state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (((list name formals ic oc decls body kwd-alist) parsed)
       (wrld (w state))
       ((mv start state) (acl2::read-run-time state))
       (kwd-alist (put-assoc :start-time start kwd-alist))
       ((er &) (assign defunc-failure-reason :none))
       (static-defunc-ev
        (defunbc-events-with-staticp-flag name formals ic oc decls body kwd-alist wrld t))
       (dynamic-defunc-ev
        (defunbc-events-with-staticp-flag name formals ic oc decls body kwd-alist wrld nil))
       (program-mode-defunc-ev
        (program-mode-defunbc-events name formals ic oc decls body kwd-alist wrld))
       (termination-strictp
        (and (defdata::get1 :termination-strictp kwd-alist)
             (not (defdata::get1 :program-mode-p kwd-alist))))
       (function-contract-strictp (defdata::get1 :function-contract-strictp kwd-alist)))
      (value
       (cond
        ((and termination-strictp function-contract-strictp)
         `(:OR ,static-defunc-ev
               ,(make-show-failure-msg-ev start kwd-alist
                                          (eventsrc-seen-list parsed wrld t))))
        (termination-strictp
         `(:OR ,static-defunc-ev
               ,dynamic-defunc-ev
               ,(make-show-failure-msg-ev start kwd-alist
                                          (eventsrc-seen-list parsed wrld nil))))
        (t `(:OR ,static-defunc-ev
                 ,dynamic-defunc-ev
                 ,program-mode-defunc-ev
                 ,(make-show-failure-msg-ev
                   start kwd-alist 
                   (list (make-defunbc-no-guard-ev name formals ic oc decls body wrld t)))))))))

(defun parse-defunbc (name args wrld)
  (declare (xargs :mode :program))
  (declare (ignorable wrld))
  (b*
   ((ctx 'defunc)
    ((unless (or (proper-symbolp name) 
                 (and (symbolp name) (equal "*" (symbol-name name))))) 
     (er hard? ctx "~| Function name ~x0 expected to be a proper symbol.~%" name))
    (defaults-alst (table-alist 'defunc-defaults-table wrld))
    (defaults-alst
      (defdata::delete-assoc-eq-lst (filter-keywords args) defaults-alst))
    (defaults-alst
      (put-assoc :testing-enabled
                 (get-acl2s-defaults 'testing-enabled wrld) defaults-alst))
    (defaults-alst
      (put-assoc :cgen-timeout
                 (get-acl2s-defaults 'cgen-timeout wrld) defaults-alst))
    ((mv kwd-alist defun-rest)
     (defdata::extract-keywords ctx *defunc-keywords* args defaults-alst))
    (formals (car defun-rest))
    (decls/docs (butlast (cdr defun-rest) 1))
    (body (car (last defun-rest)))
    (full-input-contract (assoc-equal :input-contract kwd-alist))
    (full-output-contract (assoc-equal :output-contract kwd-alist))
    ((unless full-input-contract)
     (er hard ctx "~|Defunbc is missing the input contract. ~%" ))
    ((when full-output-contract)
     (er hard ctx "~|Defunbc does not accept an output contract. ~%" ))
    (input-contract (defdata::get1 :input-contract kwd-alist ))
    (output-contract `(booleanp ,(cons name formals)))
    ((unless (simple-termp input-contract))
     (er hard ctx "~|The input contract has to be a term. ~x0 is not.~%" input-contract))
    (recp (in-termp name body))
    (kwd-alist (put-assoc :recursivep recp kwd-alist))
    (docs (filter-strings decls/docs))
    ((when (consp (cdr docs))) 
     (er hard ctx "~|Multiple doc strings unexpected!~%" docs))
    (doc-strings (and (consp docs) (list (car docs))))
    (decls (set-difference-equal decls/docs docs))
    (decls (squeeze-multiple-xarg-decls decls))
    (decls (append doc-strings decls))
    (program-mode-p (program-mode-p name formals body decls wrld))
    (kwd-alist (put-assoc :program-mode-p program-mode-p kwd-alist)))
   (list name formals input-contract output-contract decls body kwd-alist)))

(defmacro defunbc (name &rest args)
  (b* ((verbosep (let ((lst (member :verbose args)))
                   (and lst (cadr lst))))
       (verbosep (or verbosep
                     (let ((lst (member :debug args)))
                   (and lst (cadr lst))))))
    `(with-output ,@(and (not verbosep) '(:off :all))
                  :gag-mode ,(not verbosep)
                  :stack :push
       (make-event
        (er-progn
        (test?-phase (parse-defunbc ',name ',args (w state)) state)
        (defunbc-events (parse-defunbc ',name ',args (w state)) state))))))

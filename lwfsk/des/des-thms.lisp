(in-package "ACL2S")
(include-book "string-order" :ttags :all)
(include-book "defunbc" :ttags :all)
(include-book "higher-order" :ttags :all)

;; Data definitions for DES, a Discrete-Event Simulation system

;; Time is an integer
(defdata time nat)

;; An event is a string (any type will do)
(defdata event string)

;; A timed-event is record consisting of a time and an event.
(defdata timed-event
  (record (tm . time)
          (ev . event)))

;; A list of timed-events
(defdata lo-te (listof timed-event))

;; A memory maps a global variable (var) to a value (integer)
(defdata memory (alistof var integer))

;; A state of the DES consists of the current time, the list of
;; timed-events to execute and the memory.
(defdata des-state
  (record (tm . time)
          (tevs . lo-te)
          (mem . memory)))

;; To avoid having to type acl2:: in front of set-equiv
(defabbrev set-equiv (a b)
  (acl2::set-equiv a b))

(add-macro-fn set-equiv acl2::set-equiv)

;; The definition of des-state equality. The timed events are a set,
;; so we have to compare them using set equality. The memory is also a
;; set of variable, value pairs, so we also treat it as a set.
(defunbc des-state-equal (s w)
  :input-contract t
  (or (equal s w)
      (and (des-statep s)
           (des-statep w)
           (equal (des-state-tm s)
                  (des-state-tm w))
           (set-equiv (des-state-mem s)
                      (des-state-mem w))
           (set-equiv (des-state-tevs s)
                      (des-state-tevs w)))))

(defequiv des-state-equal)

(defcong des-state-equal equal (des-state-tm x) 1)
(defcong des-state-equal set-equiv (des-state-tevs x) 1)
(defcong des-state-equal set-equiv (des-state-mem x) 1)

(defdata lob (listof boolean))
(create-reduce* and booleanp lobp)
(create-reduce* or booleanp lobp)

(create-map* (lambda (te tm) (>= (timed-event-tm te) tm))
             lo-tep
             lobp
             (:fixed-vars ((timep tm))))

(defunbc valid-lo-tevs-high (tevs time)
  "Checks if the list of timed events is valid: all events in tevs are
   scheduled to execute at a time >= to time" 
  :input-contract (and (lo-tep tevs) (timep time))
  (reduce* and t
           (map* (lambda (te tm) (>= (timed-event-tm te) tm)) tevs time)))

(defunbc valid-lo-tevs (tevs time)
  "Checks if the list of timed events is valid: all events in tevs are
   scheduled to execute at a time >= to time" 
  :input-contract (and (lo-tep tevs) (timep time))
  (if (endp tevs)
      t
    (and (>= (timed-event-tm (car tevs)) time)
         (valid-lo-tevs (cdr tevs) time))))

(defthmd valid-lo-tevs-equiv
  (implies (and (lo-tep tevs) (timep time))
           (equal (valid-lo-tevs tevs time)
                  (valid-lo-tevs-high tevs time))))

;; The execution of an event is modeled as an uninterpreted function
;; execute-event. It takes the current time and the current memory as
;; input and returns an updated memory and a list of new events that
;; are scheduled to be executed at some time > tm. The new events are
;; added into Sch.

(encapsulate
 (((step-events * * *) => *)
  ((step-memory  * * *) => *))
 
 (local (defun step-events (ev tm mem)
          (declare (ignore ev tm mem))
          nil))

 (local (defun step-memory (ev tm mem)
          (declare (ignore ev tm mem))
          nil))

 (defthm step-events-contract
   (implies (and (eventp ev)
                 (timep tm)
                 (memoryp mem))
            (and (lo-tep (step-events ev tm mem))
                 (valid-lo-tevs (step-events ev tm mem)
                               (1+ tm)))))
 
 (defthm step-memory-contract
   (implies (and (eventp ev)
                 (timep tm)
                 (memoryp mem))
            (memoryp (step-memory ev tm mem))))

 ;; needs a loop-stopper bad rewrite
 (defthmd step-events-congruence
   (implies (and (memoryp mem)
                 (memoryp mem-equiv)
                 (eventp ev)
                 (timep tm)
                 (set-equiv (double-rewrite mem) (double-rewrite mem-equiv)))
            (set-equiv (step-events ev tm mem)
                       (step-events ev tm mem-equiv))))

 (defthmd step-memory-congruence
   (implies (and (memoryp mem)
                 (memoryp mem-equiv)
                 (eventp ev)
                 (timep tm)
                 (set-equiv (double-rewrite mem) (double-rewrite mem-equiv)))
            (set-equiv (step-memory ev tm mem)
                       (step-memory ev tm mem-equiv))))
 )

(create-filter*
 (lambda (tev tm) (equal (timed-event-tm tev) tm))
 lo-tep
 (:fixed-vars ((timep tm))))

(defunc events-at-tm-high (tevs tm)
  "Returns the sublist of timed-events in tevs that are scheduled 
   to execute at time = tm"
  :input-contract (and (lo-tep tevs) (timep tm))
  :output-contract (lo-tep (events-at-tm-high Tevs tm))
  (filter* (lambda (tev tm) (equal (timed-event-tm tev) tm))
           tevs tm))

(defunc events-at-tm (tevs tm)
  "Returns the sublist of timed-events in tevs that are scheduled 
   to execute at time = tm"
  :input-contract (and (lo-tep tevs) (timep tm))
  :output-contract (lo-tep (events-at-tm Tevs tm))
  (if (endp tevs)
      nil
    (if (equal (timed-event-tm (car tevs)) tm)
        (cons (car tevs) (events-at-tm (cdr tevs) tm))
      (events-at-tm (cdr tevs) tm))))

(defthmd events-at-tm-equiv
  (implies (and (lo-tep tevs) (timep tm))
           (equal (events-at-tm tevs tm)
                  (events-at-tm-high tevs tm))))

(create-filter*
 (lambda (e1 e2) (not (equal e1 e2)))
 lo-tep
 (:fixed-vars ((timed-eventp e2))))

(defunc remove-ev-high (tevs ev)
  "Removes all occurrences of ev in tevs"
  :input-contract (and (lo-tep tevs) (timed-eventp ev))
  :output-contract (lo-tep (remove-ev-high tevs ev))
  (filter* (lambda (e1 e2) (not (equal e1 e2))) tevs ev))

(defunc remove-ev (tevs ev)
  "Removes all occurrences of ev in tevs"
  :input-contract (and (lo-tep tevs) (timed-eventp ev))
  :output-contract (lo-tep (remove-ev tevs ev))
  (if (endp tevs)
      nil
    (if (equal (car tevs) ev)
        (remove-ev (cdr tevs) ev)
      (cons (car tevs) (remove-ev (cdr tevs) ev)))))

(defthmd remove-ev-equiv
  (implies (and (lo-tep tevs) (timed-eventp ev))
           (equal (remove-ev tevs ev)
                  (remove-ev-high tevs ev))))

(defthm remove-ev-member-equal
  (implies (and (timed-eventp ev)
                (lo-tep tevs))
           (not (member-equal ev (remove-ev tevs ev)))))

(in-theory
 (disable des-state des-statep des-state-tm
          des-state-tevs des-state-mem))

(defun-sk spec-ev-transp (w v)
  (exists tev
    (let ((tm (des-state-tm w))
          (tevs (des-state-tevs w))
          (mem (des-state-mem w)))
      (and (timed-eventp tev)
           (equal (timed-event-tm tev) tm)
           (member-equal tev tevs)
           (let* ((ev (timed-event-ev tev))
                  (new-evs (step-events ev tm mem))
                  (new-mem (step-memory ev tm mem))
                  (new-tevs (remove-ev tevs tev))
                  (new-tevs (append new-evs new-tevs)))
             (des-state-equal v (des-state tm new-tevs new-mem))))))
  :witness-dcls ((declare (xargs :guard (and (des-statep w) (des-statep v))
                                 :verify-guards nil))))

(verify-guards spec-ev-transp)

(defunbc spec-transp (w v)
  :input-contract (and (des-statep w) (des-statep v))
  (let ((w-tm (des-state-tm w))
        (w-tevs (des-state-tevs w))
        (w-mem (des-state-mem w)))
    (if (not (events-at-tm w-tevs w-tm))
        (des-state-equal v (des-state (1+ w-tm) w-tevs w-mem))
      (spec-ev-transp w v))))


;; OptDES

(defunbc event-< (e1 e2)
  :input-contract (and (eventp e1) (eventp e2))
  (and (string< e1 e2) t))

(defunbc te-< (te1 te2)
  "An ordering on event timed-events"
  :input-contract (and (timed-eventp te1) (timed-eventp te2))
  (let ((t1 (timed-event-tm te1))
        (e1 (timed-event-ev te1))
        (t2 (timed-event-tm te2))
        (e2 (timed-event-ev te2)))
    (or (< t1 t2)
        (and (equal t1 t2) (event-< e1 e2)))))

;; te-< is a total order
(defthm te-<-transitive
  (implies (and (timed-eventp te1) (timed-eventp te2) (timed-eventp p3)
                (te-< te1 te2)
                (te-< te2 p3))
           (te-< te1 p3)))

(defthm te-<-irreflexive
  (implies  (timed-eventp p)
            (not (te-< p p))))

(defthm te-<-asymmetric
  (implies (and (timed-eventp te1) (timed-eventp te2)
                 (te-< te1 te2))
            (not (te-< te2 te1))))
 
(defthm te-<-trichotomy
  (implies (and (timed-eventp te1)
                (timed-eventp te2)
                (not (te-< te1 te2)))
           (equal (te-< te2 te1)
                  (not (equal te1 te2)))))

(in-theory (disable te-< te-<-definition-rule))

(defunbc ordered-lo-tep (l)
  "Check if a list of event-timed-events, l, is ordered"
  :input-contract (lo-tep l)
  (cond ((endp l) t)
        ((endp (cdr l)) t)
        (t (and (te-< (car l) (second l))
                (ordered-lo-tep (cdr l))))))

(defunbc o-lo-tep (l)
  "An OptDES schedule recognizer"
  :input-contract t
  (and (lo-tep l)
       (ordered-lo-tep l)))

(register-type o-lo-te :predicate o-lo-tep :enumerator nth-lo-te)

(defunc insert-tev (tev otevs)
  "Insert timed-event tev into otevs"
  :input-contract (and (timed-eventp tev) (o-lo-tep otevs))
  :output-contract (o-lo-tep (insert-tev tev otevs))
  (if (endp otevs)
      (list tev)
    (cond ((equal tev (car otevs))
           otevs)
          ((te-< tev (car otevs))
           (cons tev otevs))
          (t (cons (car otevs) (insert-tev tev (cdr otevs)))))))

(defunc insert-otevs (l otevs)
  "Insert timed-events in l in otevs"
  :input-contract (and (lo-tep l) (o-lo-tep otevs))
  :output-contract (o-lo-tep (insert-otevs l otevs))
  (if (endp l)
      otevs
    (insert-tev (car l) (insert-otevs (cdr l) otevs))))

;; The following two theorem are proved by tau but if not provided as
;; rewrite rules some other theorems fail. ???

(defthm o-lo-tep-cdr
  (implies (and (o-lo-tep l) (consp l))
           (o-lo-tep (cdr l)))
  :hints (("goal" :in-theory (enable o-lo-tep))))

(defthm o-lo-tep-car
  (implies (and (o-lo-tep l) (consp l))
           (timed-eventp (car l))))

(defthm o-lo-tep=>lo-tep
   (implies (o-lo-tep l)
            (lo-tep l))
   :rule-classes (:rewrite :forward-chaining))

;; State of OptDES
(defdata odes-state
  (record (tm . time)
          (otevs . o-lo-te)
          (mem . memory)))

(defunbc odes-state-equal (s w)
  :input-contract t
  (or (equal s w)
      (and (odes-statep s)
           (odes-statep w)
           (equal (odes-state-tm s)
                  (odes-state-tm w))
           (equal (odes-state-otevs s)
                  (odes-state-otevs w))
           (set-equiv (odes-state-mem s)
                            (odes-state-mem w)))))

(defequiv odes-state-equal)

(in-theory (disable timep o-lo-tep-definition-rule odes-state
                    odes-state-otevs odes-state-tm odes-state-mem
                    timed-event-ev timed-event-tm))

(defunc odes-transf (s)
  "transition function for the implementation"
  :input-contract (odes-statep s)
  :output-contract (odes-statep (odes-transf s))
  (let ((tm (odes-state-tm s))
        (otevs (odes-state-otevs s))
        (mem (odes-state-mem s)))
    (if (endp otevs)
        (odes-state (1+ tm) otevs mem)
      (b* ((tev (car otevs))
           (ev (timed-event-ev tev))
           (et (timed-event-tm tev))
           (new-tevs (step-events ev et mem))
           (new-mem (step-memory ev et mem))
           (new-otevs (cdr otevs))
           (new-otevs (insert-otevs new-tevs new-otevs))
           (new-tm (timed-event-tm tev)))
        (odes-state new-tm new-otevs new-mem)))))

;; We next describe an HoptDES machine obtained by augumenting a state
;; of OptDES machine with a history component. The transition function
;; of HoptDES is defined by modifying the transition function of
;; OptDES such that the history variable records the past information.

(defdata history
  (record (valid . boolean)
          (tm . time)
          (otevs . o-lo-te)
          (mem . memory)))

(defdata hstate
  (record (tm . time)
          (otevs . o-lo-te)
          (mem . memory)
          (h . history)))

(defunbc hstate-equal (s w)
  :input-contract t
  (or (equal s w)
      (and (hstatep s)
           (hstatep w)
           (equal (hstate-tm s)
                  (hstate-tm w))
           (equal (hstate-otevs s)
                  (hstate-otevs w))
           (set-equiv (hstate-mem s)
                      (hstate-mem w))
           (if (history-valid (hstate-h s))
               (and (history-valid (hstate-h w))
                    (equal (history-tm (hstate-h s))
                           (history-tm (hstate-h w)))
                    (equal (history-otevs (hstate-h s))
                           (history-otevs (hstate-h w)))
                    (set-equiv (history-mem (hstate-h s))
                                     (history-mem (hstate-h w))))
             (not (history-valid (hstate-h w)))))))
                
(defequiv hstate-equal)
(defcong hstate-equal equal (hstate-tm x) 1)
(defcong hstate-equal equal (hstate-otevs x) 1)
(defcong hstate-equal set-equiv (hstate-mem x) 1)

(in-theory (disable hstate hstate-otevs hstate-tm hstate-mem hstate-h
                   history history-valid history-otevs history-mem
                   history-tm des-state))

(defunc hodes-transf (s)
  "transition function for HoptDES"
  :input-contract (hstatep s)
  :output-contract (hstatep (hodes-transf s))
  (let* ((tm (hstate-tm s))
         (otevs (hstate-otevs s))
         (mem (hstate-mem s))
         (hist (history t tm otevs mem)))
    (if (endp otevs)
        (hstate (1+ tm) otevs mem hist)
      (let* ((tev (car otevs))
             (ev (timed-event-ev tev))
             (et (timed-event-tm tev))
             (new-tevs (step-events ev et mem))
             (new-mem (step-memory ev et mem))
             (new-otevs (cdr otevs))
             (new-otevs (insert-otevs new-tevs new-otevs))
             (new-tm (timed-event-tm tev)))
        (hstate new-tm new-otevs new-mem hist)))))


;; OptDES refines HoptDES under a refinement map P
(defunc P (s)
  :input-contract (odes-statep s)
  :output-contract (hstatep (P s))
  (let ((tm (odes-state-tm s))
        (otevs (odes-state-otevs s))
        (mem (odes-state-mem s)))
    (hstate tm otevs mem (history nil 0 nil nil))))

(defunbc good-odes-statep (s)
  "good odes state recognizer"
  :input-contract t
  (and (odes-statep s)
       (valid-lo-tevs (odes-state-otevs s) (odes-state-tm s))))

(defunbc good-histp (s)
  "Checks if the history component of an Hstate is good"
  :input-contract (hstatep s)
  (let* ((hist (hstate-h s))
         (h-tm (history-tm hist))
         (h-valid (history-valid hist))
         (h-otevs (history-otevs hist))
         (h-mem (history-mem hist))
         (hst (hstate h-tm h-otevs h-mem
                      (history nil 0 nil nil)))
         (sh (hodes-transf hst)))
    (implies h-valid
             (and (hstate-equal sh s)
                  (valid-lo-tevs h-otevs (hstate-tm s))))))

(defunbc good-hstatep (s)
  :input-contract t
  (and (hstatep s)
       (valid-lo-tevs (hstate-otevs s) (hstate-tm s))
       (good-histp s)))

(defthm good-hstate-is-hstate-fw
  (implies (good-hstatep x)
           (hstatep x))
  :rule-classes (:rewrite :forward-chaining))

(defunbc A (s w)
  "SKS/STS relation between OptDES and HoptDES"
  :input-contract t
  (and (good-odes-statep s)
       (good-hstatep w)
       (let* ((ps (P s))
              (ps-tm (hstate-tm ps))
              (ps-otevs (hstate-otevs ps))
              (ps-mem (hstate-mem ps))
              (w-tm (hstate-tm w))
              (w-otevs (hstate-otevs w))
              (w-mem (hstate-mem w)))
         (and (equal ps-tm w-tm)
              (equal ps-otevs w-otevs)
              (set-equiv ps-mem w-mem)))))

(defthm P-good
  (implies (good-odes-statep s)
           (A s (P s))))

(defthm no-events-at-tm-top-of-queue-1
  (implies (and (o-lo-tep E) (timep tm)
                (valid-lo-tevs E tm)
                (not (equal (timed-event-tm (car E)) tm)))
           (not (events-at-tm E tm)))
  :hints (("goal" :in-theory (e/d (te-<-definition-rule
                                   ordered-lo-tep timep
                                   o-lo-tep) (timed-event))
           :induct (ordered-lo-tep E))))

(defthm no-events-at-tm-top-of-queue-2
  (implies (and (o-lo-tep E)
                (consp E)
                (timep tm)
                (not (events-at-tm E tm))
                (valid-lo-tevs E tm))
           (> (timed-event-tm (car E)) tm))
  :hints (("goal" :in-theory (e/d (ordered-lo-tep) (timed-event-tm))))
  :rule-classes (:rewrite :linear))

(defthm valid-lo-tevs->=-tm
  (implies (and (lo-tep E) (timep t1) (timep t2)
                (>= t1 t2)
                (valid-lo-tevs E t1))
           (valid-lo-tevs E t2)))

(defthm valid-lo-tevs-o-lo-tep
  (implies (and (o-lo-tep E)
                (consp E))
           (valid-lo-tevs E (timed-event-tm (car E))))
  :hints (("goal" :in-theory (e/d (te-<-definition-rule
                                   ordered-lo-tep timep
                                   o-lo-tep) (timed-event))
           :induct (ordered-lo-tep E))))

(encapsulate
 nil

 (local (defthm valid-lo-tevs-member
          (implies (and (lo-tep l)  (timep tm)
                        (timed-eventp tev)
                        (member-equal tev l)
                        (valid-lo-tevs l tm))
                   (>= (timed-event-tm tev) tm))
          :hints (("goal" :in-theory (e/d (acl2::member-equal))))))

 (local (defthm valid-lo-tevs-subsetp
          (implies (and (lo-tep l1) (lo-tep l2) (timep tm)
                        (acl2::subsetp-equal l1 l2)
                        (valid-lo-tevs l2 tm))
                   (valid-lo-tevs l1 tm))
          :hints (("goal" :in-theory (enable acl2::subsetp-equal)))))
 
 (defthm valid-lo-tevs-setequiv
   (implies (and (lo-tep l1) (lo-tep l2) (timep tm)
                 (set-equiv l1 l2)
                 (valid-lo-tevs l2 tm))
            (valid-lo-tevs l1 tm))
   :hints (("goal" :in-theory (enable set-equiv))))
 )

(encapsulate
 nil
 (local (defthm cons-setequiv-insert
          (implies (and (o-lo-tep l) (timed-eventp tev))
                   (set-equiv (insert-tev tev l)
                              (cons tev l)))
          :hints (("goal" :in-theory (enable set-equiv)))))

 (defthm append-setequiv-insert-tevs
   (implies (and (o-lo-tep l) (lo-tep x))
            (set-equiv (insert-otevs x l)
                       (append x l)))
   :hints (("goal" :in-theory (enable set-equiv))))
 
 (local (defthm valid-lo-tevs-append
          (implies (and (lo-tep l1) (lo-tep l2)
                        (timep tm1) (timep tm2)
                        (>= tm2 tm1)
                        (valid-lo-tevs l1 tm1)
                        (valid-lo-tevs l2 tm2))
                   (valid-lo-tevs (append l1 l2) tm1))))
 
 (defthm valid-lo-tevs-insert-otevs
          (implies (and (o-lo-tep l1) (lo-tep l2)
                        (timep tm1) (timep tm2)
                        (>= tm2 tm1)
                        (valid-lo-tevs l1 tm1)
                        (valid-lo-tevs l2 tm2))
                   (valid-lo-tevs (insert-otevs l2 l1) tm1))
          :hints (("goal" :use ((:instance valid-lo-tevs-append)
                                (:instance append-setequiv-insert-tevs
                                           (x l2) (l l1))
                                (:instance valid-lo-tevs-setequiv
                                           (l2 (append l1 l2))
                                           (l1 (insert-otevs l2 l1))
                                           (tm tm1)))
                   :in-theory (disable valid-lo-tevs-append
                                       valid-lo-tevs-setequiv
                                       append-setequiv-insert-tevs)
                   :do-not-induct t)))
 
 (local (defthmd fw1
          (implies (and (o-lo-tep l) (consp l))
                   (o-lo-tep (cdr l)))))

 (local (defthm l1
          (implies (and (lo-tep x) (timed-eventp tev)
                        (o-lo-tep (cons tev l))
                        (timep tm) 
                        (valid-lo-tevs l (timed-event-tm tev))               
                        (valid-lo-tevs x tm)
                        (> tm (timed-event-tm tev)))
                   (valid-lo-tevs (insert-otevs x l)
                                  (timed-event-tm tev)))
          :hints (("goal" :in-theory (disable valid-lo-tevs-insert-otevs
                                              insert-otevs-definition-rule
                                              valid-lo-tevs-o-lo-tep timed-event
                                              VALID-LO-TEVS->=-TM fw1)
                   :use ((:instance fw1 (l (cons tev l)))
                         (:instance valid-lo-tevs-insert-otevs
                                    (l1 l) (l2 x)
                                    (tm1 (timed-event-tm tev))
                                    (tm2 tm)))
                   :do-not-induct t))))

 (local (defthm l2
          (implies (and (lo-tep x) (timed-eventp tev)
                        (o-lo-tep (cons tev l))
                        (timep tm) 
                        (valid-lo-tevs l (timed-event-tm tev))               
                        (valid-lo-tevs x (1+ (timed-event-tm tev))))
                   (valid-lo-tevs (insert-otevs x l)
                                  (timed-event-tm tev)))
          :hints (("goal" :in-theory (disable valid-lo-tevs-insert-otevs
                                              insert-otevs-definition-rule
                                              valid-lo-tevs-o-lo-tep timed-event
                                              VALID-LO-TEVS->=-TM fw1 l1)
                   :use ((:instance l1 (tm (1+ (timed-event-tm tev)))))))))

 (local (defthm l3
          (implies (and (o-lo-tep (cons tev l))
                        (timed-eventp tev) (timep tm)
                        (valid-lo-tevs (cons tev l) tm))
                   (valid-lo-tevs l tm))))

 (local (defthm l4
          (implies (and (o-lo-tep (cons tev l)) (timep tm)
                        (timed-eventp tev))
                   (valid-lo-tevs (cons tev l) (timed-event-tm tev)))
          :hints (("Goal" :in-theory (disable valid-lo-tevs-o-lo-tep
                                              valid-lo-tevs-definition-rule)
                   :use ((:instance valid-lo-tevs-o-lo-tep
                                    (E (cons tev l))))))))

 (local (defthm l5
          (implies (and (o-lo-tep (cons tev l)) (timep tm)
                        (timed-eventp tev))
                   (valid-lo-tevs l (timed-event-tm tev)))))

  (local (defthm lemma
           (implies (and (lo-tep x)
                         (timed-eventp tev)
                         (o-lo-tep (cons tev l))
                         (timep tm)
                         (>= (timed-event-tm tev) tm)
                         (valid-lo-tevs l tm)
                         (valid-lo-tevs x (1+ (timed-event-tm tev))))
                    (valid-lo-tevs (insert-otevs x l)
                                   (timed-event-tm tev)))))
 
 (local (defthm lemma-1
          (implies (and (odes-statep s)
                        (valid-lo-tevs (odes-state-otevs s)
                                       (odes-state-tm s))
                        (consp (odes-state-otevs s)))
                   (valid-lo-tevs
                    (insert-otevs (step-events
                                   (timed-event-ev (car (odes-state-otevs s)))
                                   (timed-event-tm (car (odes-state-otevs s)))
                                   (odes-state-mem s))
                                  (cdr (odes-state-otevs s)))
                    (timed-event-tm (car (odes-state-otevs s)))))
        :hints (("Goal" :in-theory (disable valid-lo-tevs->=-tm
                                            no-events-at-tm-top-of-queue-1
                                            no-events-at-tm-top-of-queue-2)))))
 
 (defthm good-odes-inductive
   (implies (good-odes-statep s)
            (good-odes-statep (odes-transf s)))
   :rule-classes (:forward-chaining :rewrite))

 (local (defthm lemma-2
          (implies (and (hstatep s)
                        (valid-lo-tevs (hstate-otevs s)
                                       (hstate-tm s))
                        (consp (hstate-otevs s)))
                   (valid-lo-tevs
                    (insert-otevs (step-events
                                   (timed-event-ev (car (hstate-otevs s)))
                                   (timed-event-tm (car (hstate-otevs s)))
                                   (hstate-mem s))
                                  (cdr (hstate-otevs s)))
                    (timed-event-tm (car (hstate-otevs s)))))
          :hints (("Goal" :in-theory (disable valid-lo-tevs->=-tm
                                              no-events-at-tm-top-of-queue-1
                                              no-events-at-tm-top-of-queue-2)))))
 
 (defthm good-hstate-inductive
   (implies (good-hstatep s)
            (good-hstatep (hodes-transf s)))
   :hints (("Goal" :in-theory (disable
                               no-events-at-tm-top-of-queue-1
                               no-events-at-tm-top-of-queue-2)))
   :rule-classes (:forward-chaining :rewrite))

 )



(encapsulate
 nil
 (local (include-book "oset-set-equiv-equal" :ttags :all))

 (local (defthmd insert-otevs-l-equiv-is-set-eqiuv
          (implies (and (o-lo-tep otevs)
                        (lo-tep l)
                        (lo-tep l-equiv)
                        (set-equiv l l-equiv))
                   (set-equiv (insert-otevs l otevs)
                              (insert-otevs l-equiv otevs)))))

 (local (defthm insert-otevs-l-equiv-is-equal
          (implies (and (o-lo-tep otevs)
                        (lo-tep l)
                        (lo-tep l-equiv)
                        (set-equiv l l-equiv))
                   (equal (insert-otevs l otevs)
                          (insert-otevs l-equiv otevs)))
          :hints (("Goal"
                   :use ((:instance insert-otevs-l-equiv-is-set-eqiuv)
                         (:instance o-lo-tep-set-equiv-is-equal (x (insert-otevs l otevs))
                                    (y (insert-otevs l-equiv otevs))))))))

 ;; Not sure if it is useful here and/or there might be a better place for
 ;; this congruence relation
 ;; (defthm hodes-transf-congruence
 ;;   (implies (hstate-equal s w)
 ;;            (hstate-equal (hodes-transf s)
 ;;                          (hodes-transf w)))
 ;;   :hints (("goal" :in-theory (disable insert-otevs-l-equiv-is-equal)
 ;;            :use ((:instance step-events-congruence
 ;;                             (ev (timed-event-ev (car (hstate-otevs s))))
 ;;                             (tm (timed-event-tm (car (hstate-otevs s))))
 ;;                             (mem (hstate-mem s))
 ;;                             (mem-equiv (hstate-mem w)))
 ;;                  (:instance step-memory-congruence
 ;;                             (ev (timed-event-ev (car (hstate-otevs s))))
 ;;                             (tm (timed-event-tm (car (hstate-otevs s))))
 ;;                             (mem (hstate-mem s))
 ;;                             (mem-equiv (hstate-mem w)))
 ;;                  (:instance insert-otevs-l-equiv-is-equal
 ;;                             (otevs (cdr (hstate-otevs s)))
 ;;                             (l (step-events (timed-event-ev (car (hstate-otevs s)))
 ;;                                             (timed-event-tm (car (hstate-otevs s)))
 ;;                                             (hstate-mem s)))
 ;;                             (l-equiv (step-events (timed-event-ev (car (hstate-otevs s)))
 ;;                                                   (timed-event-tm (car (hstate-otevs s)))
 ;;                                                   (hstate-mem w)))))))
 ;;   :rule-classes (:congruence))
 
 (local (defthm A-proof-1
          (implies (and (A s w)
                        (good-hstatep (hodes-transf w))
                        (good-odes-statep (odes-transf s)))                
                   (A (odes-transf s)
                      (hodes-transf w)))
          :hints (("Goal" :in-theory (disable good-odes-statep good-hstatep
                                              good-hstate-inductive
                                              good-odes-inductive
                                              valid-lo-tevs->=-tm
                                              no-events-at-tm-top-of-queue-1
                                              no-events-at-tm-top-of-queue-2)
                   :use ((:instance step-events-congruence
                                    (ev (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W))))
                                    (tm (TIMED-EVENT-tm (CAR (HSTATE-OTEVS W))))
                                    (mem-equiv (ODES-STATE-MEM S))
                                    (mem (HSTATE-MEM W)))
                         (:instance step-memory-congruence
                                    (ev (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W))))
                                    (tm (TIMED-EVENT-tm (CAR (HSTATE-OTEVS W))))
                                    (mem-equiv (ODES-STATE-MEM S))
                                    (mem (HSTATE-MEM W)))))
                  ("Subgoal 3'"
                   :use ((:instance step-events-congruence
                                    (ev (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W))))
                                    (tm (TIMED-EVENT-tm (CAR (HSTATE-OTEVS W))))
                                    (mem-equiv (ODES-STATE-MEM S))
                                    (mem (HSTATE-MEM W)))
                         (:instance insert-otevs-l-equiv-is-equal
                                    (otevs (CDR (HSTATE-OTEVS W)))
                                    (l (STEP-EVENTS (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W)))
                                                    (TIMED-EVENT-TM (CAR (HSTATE-OTEVS W)))
                                                    (ODES-STATE-MEM S)))
                                    (l-equiv (STEP-EVENTS (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W)))
                                                          (TIMED-EVENT-TM (CAR (HSTATE-OTEVS W)))
                                                          (HSTATE-MEM W)))))
                   :in-theory (disable INSERT-OTEVS-L-EQUIV-IS-EQUAL))
                  ("Subgoal 2'"
                   :use ((:instance step-events-congruence
                                    (ev (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W))))
                                    (tm (TIMED-EVENT-tm (CAR (HSTATE-OTEVS W))))
                                    (mem-equiv (ODES-STATE-MEM S))
                                    (mem (HSTATE-MEM W)))
                         (:instance insert-otevs-l-equiv-is-equal
                                    (otevs (CDR (HSTATE-OTEVS W)))
                                    (l (STEP-EVENTS (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W)))
                                                    (TIMED-EVENT-TM (CAR (HSTATE-OTEVS W)))
                                                    (ODES-STATE-MEM S)))
                                    (l-equiv (STEP-EVENTS (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W)))
                                                          (TIMED-EVENT-TM (CAR (HSTATE-OTEVS W)))
                                                          (HSTATE-MEM W)))))
                   :in-theory (disable INSERT-OTEVS-L-EQUIV-IS-EQUAL))
                  ("Subgoal 1"
                   :use ((:instance step-events-congruence
                                    (ev (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W))))
                                    (tm (TIMED-EVENT-tm (CAR (HSTATE-OTEVS W))))
                                    (mem-equiv (ODES-STATE-MEM S))
                                    (mem (HSTATE-MEM W)))
                         (:instance insert-otevs-l-equiv-is-equal
                                    (otevs (CDR (HSTATE-OTEVS W)))
                                    (l (STEP-EVENTS (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W)))
                                                    (TIMED-EVENT-TM (CAR (HSTATE-OTEVS W)))
                                                    (ODES-STATE-MEM S)))
                                    (l-equiv (STEP-EVENTS (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W)))
                                                          (TIMED-EVENT-TM (CAR (HSTATE-OTEVS W)))
                                                          (HSTATE-MEM W)))))))))

 (local (defthm A-implies-good-states
          (implies (A s w)
                   (and (good-odes-statep s)
                        (good-hstatep w)))
          :hints (("Goal" :in-theory (disable p-definition-rule
                                              good-hstatep-definition-rule
                                              good-odes-statep-definition-rule)))))
 
 (defthmd A-is-a-bisimulation
   (implies (and (A s w))
            (A (odes-transf s)
               (hodes-transf w)))
   :hints (("Goal" :in-theory (disable A-definition-rule
                                       hodes-transf-definition-rule
                                       good-odes-statep-definition-rule
                                       good-hstatep-definition-rule))))

 )

;; HoptDES refines DES

(defunc R (s)
  "A refinement map from an OptDES state to a DES state"
  :input-contract (hstatep s)
  :output-contract (des-statep (R s))
  (des-state (hstate-tm s) (hstate-otevs s) (hstate-mem s)))

(defunbc good-des-statep (s)
  :input-contract t
  (and (des-statep s)
       (valid-lo-tevs (des-state-tevs s) (des-state-tm s))))

(defthm good-des-state-is-des-state-fw
  (implies (good-des-statep x)
           (des-statep x))
  :rule-classes (:rewrite :forward-chaining))

(defunbc B (s w)
  "SKS relation between an OptDES state and a DES state"
  :input-contract t
  (and (good-hstatep s)
       (good-des-statep w)
       (des-state-equal (R s) w)))

(defthm B-implies-good-states
  (implies (B s w)
           (and (good-hstatep s) (good-des-statep w)))
  :rule-classes (:forward-chaining))

(defthm R-good
  (implies (good-hstatep s)
           (B s (R s))))

;; Not sure if it will be useful
(defcong hstate-equal des-state-equal (R x) 1)

;; LWFSK witness

(defunbc C (x y)
  :input-contract t
  (and (good-hstatep x)
       (good-des-statep y)
       (or (B x y)
           (and (history-valid (hstate-h x))
                (consp (history-otevs (hstate-h x)))
                (<= (des-state-tm y) (hstate-tm x))
                (set-equiv (des-state-tevs y)
                                 (history-otevs (hstate-h x)))
                (set-equiv (des-state-mem y)
                           (history-mem (hstate-h x)))))))

(defthm C-implies-good-state-fw
  (implies (C x y)
           (and (good-hstatep x)
                (good-des-statep y)))
  :hints (("Goal" :in-theory (disable good-des-statep-definition-rule
                                      good-hstatep-definition-rule))))

(defunc rankls (y x)
  :input-contract (and (des-statep y) (hstatep x))
  :output-contract (natp (rankls y x))
  (nfix (- (+ (hstate-tm x)
              (len (events-at-tm (des-state-tevs y) (hstate-tm x))))
           (des-state-tm y))))

#|
(defunc rankls (y x)
  :input-contract (and (des-statep y) (hstatep x))
  :output-contract (natp (rankls y x))
  (nfix (- (1+ (hstate-tm x)) (des-state-tm y))))

Consider the following 
x = < 10, <>, m', <t, {(e,10)}, m>
y  = < 10, {(e,10)}, m>

where execution e modifies m to m'.

x is a good-hstatep y is good-des-statep

xCy holds

xBy does not hold

Hence we have to show that there is a z such that y --> z /\ xCz /\
rankls(z,x) < rankls(y,x).

rankls (y,x) = (- (1+ 10) 10) = 1

y --> z 
where z = <10, <>, mem'> 
xCz since xBz holds.

rankls(z,x)  = (- (1+ 10) 10) = 1

Rankls(z,x) = rankls(y,x) and does not decrease.

|#

(encapsulate
  nil
  ;; remove-ev on ordererd list

  (local (defthm o-lo-tep-member-equal
    (implies (o-lo-tep (cons x l))
             (not (member-equal x l)))
    :hints (("goal" :in-theory (enable te-<-definition-rule o-lo-tep member-equal)))))
                     
  (local  (defthm o-lo-tep-noduplicates
    (implies (o-lo-tep x)
             (no-duplicatesp-equal x))
    :hints (("goal" :in-theory (enable te-<-definition-rule no-duplicatesp-equal o-lo-tep)))))

  (local (defthm remove-ev-not-member
    (implies (and (o-lo-tep x) (timed-eventp tev)
                  (not (member-equal tev x)))
             (equal (remove-ev x tev)
                    x))))

  (defthm remove-ev-o-lo-tep
    (implies (and (o-lo-tep x) (consp x))
             (equal (remove-ev x (car x))
                    (cdr x))))
  )

 (encapsulate
  nil
  (local (defthm remove-ev-member-1
           (implies (and (lo-tep l) (timed-eventp tev)
                         (not (equal x tev))
                         (member-equal x l))
                    (member-equal x (remove-ev l tev)))))
                    
  (local (defthm remove-ev-preserves-subset
           (implies (and (lo-tep x) (lo-tep y) (timed-eventp tev)
                         (subsetp-equal (double-rewrite x) (double-rewrite y)))
                    (subsetp-equal (remove-ev x tev)
                                   (remove-ev y tev)))
           :hints (("goal" :in-theory (enable  subsetp-equal)))))

  (defthmd remove-ev-preserves-set-equiv
           (implies (and (lo-tep x) (lo-tep y) (timed-eventp tev)
                         (set-equiv  x y))
                    (set-equiv (remove-ev x tev)
                               (remove-ev y tev)))
           :hints (("goal" :in-theory (e/d (set-equiv)))))

  )

(encapsulate
  nil
  (local (defthm l1
           (implies (and (lo-tep l) (timed-eventp tev) (timep tm)
                         (member-equal tev l)
                         (equal (timed-event-tm tev) tm))
                    (member-equal tev (events-at-tm l tm)))
           :hints (("goal" :in-theory (enable member-equal)))))

  (local (defthm  events-at-tm-l-subsetp
           (implies (and (lo-tep x) (lo-tep y) (timep tm)
                         (subsetp-equal x y))
                    (subsetp-equal (events-at-tm x tm)
                                   (events-at-tm y tm)))
           :hints (("goal" :in-theory (enable subsetp-equal)))))

  (defthm  events-at-tm-l-set-equiv
    (implies (and (lo-tep x) (lo-tep y) (timep tm)
                  (set-equiv x y))
             (set-equiv (events-at-tm x tm)
                        (events-at-tm y tm)))
    :hints (("goal" :in-theory (enable set-equiv))))
  )

(defthm new-tevs-append-insert-lemma
   (implies (and (lo-tep l)
                 (o-lo-tep x) (consp x)
                 (lo-tep y) (set-equiv x y))
            (set-equiv (append l (remove-ev y (car x)))
                       (insert-otevs l (cdr x))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance remove-ev-preserves-set-equiv
                             (x y) (y x)
                             (tev (car x))))
            :in-theory (disable remove-ev-definition-rule
                                remove-ev-preserves-set-equiv))))

(encapsulate
 nil
 ;; Case when there is an event to be picked (the first one) in
 ;; HoptDES at current time. In this case , we show that (R
 ;; (hodes-transf s)) is a witness for lwfsk2a.

 (local (in-theory (disable eventp valid-lo-tevs->=-tm
                            no-events-at-tm-top-of-queue-1
                            no-events-at-tm-top-of-queue-2)))
 
 (local (defthmd lwfsk2a-B
          (implies (B s w)
                   (B (hodes-transf s)
                      (R (hodes-transf s))))
          :hints (("goal" :in-theory (disable good-des-statep
                                              good-hstatep
                                              hodes-transf
                                              r-definition-rule)
                   :use ((:instance good-hstate-inductive))))))

 (local (in-theory (disable good-histp-definition-rule)))

 (local (defthm lwfsk2a-l1-empty
          (implies (and (B s w)
                        (endp (hstate-otevs s)))
                   (and (spec-transp w (R (hodes-transf s)))
                        (B (hodes-transf s) (R (hodes-transf s)))))
          :hints (("Goal" :in-theory (e/d (valid-lo-tevs-definition-rule
                                           good-histp-definition-rule) ())))))


 ;; TODO: why this intermediate lemma is needed for lwfsk2a-spec-step
 (local (defthm e1
          (implies (and (B s w)
                        (consp (hstate-otevs s))
                        (equal (hstate-tm s)
                               (timed-event-tm (car (hstate-otevs s)))))
                   (and (equal (timed-event-tm (car (hstate-otevs s))) (des-state-tm w))
                        (timed-eventp (car (hstate-otevs s)))
                        (member-equal (car (hstate-otevs s)) (des-state-tevs w))
                        (equal (hstate-tm s) (des-state-tm w))
                        (set-equiv
                         (insert-otevs (step-events (timed-event-ev (car (hstate-otevs s)))
                                                    (hstate-tm s)
                                                    (hstate-mem s))
                                       (cdr (hstate-otevs s)))
                         (append (step-events (timed-event-ev (car (hstate-otevs s)))
                                              (des-state-tm w)
                                              (des-state-mem w))
                                 (remove-ev (des-state-tevs w)
                                            (car (hstate-otevs s)))))
                        (set-equiv (step-memory (timed-event-ev (car (hstate-otevs s)))
                                                (hstate-tm s)
                                                (hstate-mem s))
                                   (step-memory (timed-event-ev (car (hstate-otevs s)))
                                                (des-state-tm w)
                                                (des-state-mem w)))))
          :hints (("Subgoal 2'" :in-theory (disable step-events-congruence)
                   :use ((:instance step-events-congruence
                                    (ev (TIMED-EVENT-EV (CAR (HSTATE-OTEVS S))))
                                    (tm (DES-STATE-TM W))
                                    (mem (DES-STATE-MEM W))
                                    (mem-equiv (HSTATE-MEM S)))))
                  ("Subgoal 1'" :in-theory (disable step-memory-congruence)
                   :use ((:instance step-memory-congruence
                                    (ev (TIMED-EVENT-EV (CAR (HSTATE-OTEVS S))))
                                    (tm (DES-STATE-TM W))
                                    (mem (DES-STATE-MEM W))
                                    (mem-equiv (HSTATE-MEM S))))))))
 
 (local (defthmd lwfsk2a-spec-step
          (implies (and (b s w)
                        (consp (hstate-otevs s))
                        (equal (hstate-tm s)
                               (timed-event-tm (car (hstate-otevs s)))))
                   (spec-ev-transp w (r (hodes-transf s))))
          :hints (("goal" :use ((:instance spec-ev-transp-suff
                                           (tev (car (hstate-otevs s)))
                                           (v (r (hodes-transf s))))
                                (:instance e1))
                   :in-theory (disable spec-ev-transp-suff 
                                       acl2::set-equiv-is-an-equivalence
                                       acl2::commutativity-of-append-under-set-equiv
                                       e1
                                       spec-ev-transp)))))

 (defthm lwfsk2a-l1-cons
   (implies (and (B s w)
                 (consp (hstate-otevs s))
                 (equal (hstate-tm s)
                        (timed-event-tm (car (hstate-otevs s)))))
            (and (spec-ev-transp w (R (hodes-transf s)))
                 (B (hodes-transf s) (R (hodes-transf s)))))
   :hints (("goal" :use ((:instance lwfsk2a-spec-step)
                         (:instance lwfsk2a-B)))))

 (local (defthm events-at-tm-cons
          (implies (and (lo-tep x) (consp x))
                   (events-at-tm x (timed-event-tm (car x))))))

 (local (defthm lwfsk2a-l1-events-at-tm
          (implies (and (B s w)
                        (consp (hstate-otevs s))
                        (equal (hstate-tm s)
                               (timed-event-tm (car (hstate-otevs s)))))
                   (events-at-tm (des-state-tevs w) (des-state-tm w)))
          :hints (("Goal" :in-theory (disable
                                      events-at-tm-l-set-equiv
                                      timed-event eventp)
                   :use ((:instance events-at-tm-l-set-equiv
                                    (x (des-state-tevs w))
                                    (y (hstate-otevs s))
                                    (tm (hstate-tm s))))))))

 (defthmd lwfsk2a-lemma
   (implies (and (B s w)
                 (equal (hstate-tm s)
                        (timed-event-tm (car (hstate-otevs s)))))
            (and (spec-transp w (R (hodes-transf s)))
                 (B (hodes-transf s) (R (hodes-transf s)))))
   :hints (("Goal" :cases ((consp (hstate-otevs s)))
            :in-theory (e/d ()(r-definition-rule
                               spec-ev-transp
                               des-state-equal-definition-rule
                               hodes-transf-definition-rule
                               lwfsk2a-l1-events-at-tm
                               lwfsk2a-l1-cons)))
           ("Subgoal 1" :use ((:instance lwfsk2a-l1-cons)
                              (:instance lwfsk2a-l1-events-at-tm)))))
 )
 
(defthm no-event-<-tm
  (implies (and (lo-tep l) (timep tm1) (timep tm2)
                (< tm1 tm2)
                (valid-lo-tevs l tm2))
           (not (events-at-tm l tm1)))) 

(defthm valid-nil
          (implies (timep tm)
                   (valid-lo-tevs nil tm)))

(in-theory (disable valid-lo-tevs-definition-rule))

(encapsulate
 nil
 (local (defthmd lwfsk2d-l1
          (implies (and (B s w)
                        (not (equal (hstate-tm s)
                                    (timed-event-tm (car (hstate-otevs s))))))
                   (spec-transp w (des-state (1+ (des-state-tm w))
                                             (des-state-tevs w)
                                             (des-state-mem w))))
          :hints (("Goal" :in-theory (disable (:definition events-at-tm-definition-rule)
                                              (:definition spec-ev-transp)
                                              valid-lo-tevs->=-tm
                                              no-events-at-tm-top-of-queue-1
                                              no-events-at-tm-top-of-queue-2
                                              events-at-tm-l-set-equiv)
                   :use ((:instance no-events-at-tm-top-of-queue-1
                                    (E (hstate-otevs s))
                                    (tm (hstate-tm s)))
                         (:instance events-at-tm-l-set-equiv
                                    (x (des-state-tevs w))
                                    (y (hstate-otevs s))
                                    (tm (des-state-tm w))))))))


 (local (defthmd lwfsk2d-l2a
          (implies (and (B s w)
                        (not (equal (hstate-tm s)
                                    (timed-event-tm (car (hstate-otevs s))))))
                   (< (des-state-tm w) (hstate-tm (hodes-transf s))))
          :hints (("Goal" :in-theory (disable no-events-at-tm-top-of-queue-2
                                              events-at-tm-l-set-equiv)
                   :use ((:instance no-events-at-tm-top-of-queue-2
                                    (E (hstate-otevs s))
                                    (tm (hstate-tm s)))
                         (:instance events-at-tm-l-set-equiv
                                    (x (hstate-otevs s))
                                    (y (des-state-tevs w))
                                    (tm (hstate-tm s))))))))

 (local (defthm bla
          (implies (and (timep x) (timep y)
                        (< y x))
                   (<= (1+ y) x))))

 (local (defthmd lwfsk2d-l2b
          (implies (and (B s w)
                        (not (equal (hstate-tm s)
                                    (timed-event-tm (car (hstate-otevs s))))))
                   (<= (1+ (des-state-tm w)) (hstate-tm (hodes-transf s))))
          :hints (("Goal" :use ((:instance lwfsk2d-l2a))
                   :in-theory (e/d (timep) (valid-lo-tevs->=-tm
                                            no-events-at-tm-top-of-queue-1
                                            no-events-at-tm-top-of-queue-2
                                            hodes-transf-definition-rule))))))

 (local (defthmd lwfsk2d-l2c
          (implies (and (B s w)
                        (not (equal (hstate-tm s)
                                    (timed-event-tm (car (hstate-otevs s))))))
                   (let ((u (hodes-transf s)))
                     (and (<= (1+ (des-state-tm w)) (hstate-tm u))
                          (set-equiv (des-state-tevs w)
                                     (history-otevs (hstate-h u)))
                          (set-equiv (des-state-mem w)
                                     (history-mem (hstate-h u))))))
          :hints (("Goal" :in-theory (e/d (good-histp-definition-rule
                                           lwfsk2d-l2b
                                           valid-lo-tevs->=-tm)
                                          (valid-lo-tevs-definition-rule))))))

 (local (defthmd  C-good-state-valid-lo-tevs
          (implies
           (and
            (valid-lo-tevs (hstate-otevs s)
                           (timed-event-tm (car (hstate-otevs s))))
            (<= (+ 1 (des-state-tm w))
                (timed-event-tm (car (hstate-otevs s))))
            (set-equiv (des-state-tevs w)
                       (hstate-otevs s))
            (des-state-tevs w)
            (hstatep s)
            (valid-lo-tevs (hstate-otevs s)
                           (hstate-tm s))
            (des-statep w))
           (valid-lo-tevs (des-state-tevs w)
                          (+ 1 (des-state-tm w))))
          :hints (("Goal" :use ((:instance valid-lo-tevs->=-tm
                                           (t1 (timed-event-tm (car (hstate-otevs s))))
                                           (t2 (1+ (des-state-tm w)))
                                           (E (hstate-otevs s)))
                                (:instance valid-lo-tevs-o-lo-tep
                                           (E (hstate-otevs s))))
                   :in-theory (e/d()
                                  (valid-lo-tevs-o-lo-tep
                                   valid-lo-tevs->=-tm
                                   valid-lo-tevs-definition-rule
                                   ordered-lo-tep-definition-rule timed-event
                                   des-state-equal-definition-rule))))))
 
 (local (defthmd lwfsk2d-l2-cons
          (let ((u (hodes-transf s))
                (v (des-state (1+ (des-state-tm w))
                              (des-state-tevs w)
                              (des-state-mem w))))
            (implies (and (B s w)
                          (consp (hstate-otevs s))
                          (not (equal (hstate-tm s)
                                      (timed-event-tm (car (hstate-otevs s))))))
                     (C u v)))
          :hints (("Goal" :in-theory (e/d () ( o-lo-tep
                                               valid-lo-tevs-definition-rule
                                               des-state-equal-definition-rule
                                               good-histp-definition-rule
                                               hstate-equal-definition-rule))
                   :use ((:instance lwfsk2d-l2c)
                         (:instance good-hstate-inductive)))
                  ("Subgoal 3'" :in-theory (disable C-good-state-valid-lo-tevs)
                   :use ((:instance C-good-state-valid-lo-tevs))))))



 (local (defthmd lwfsk2d-l2-empty
          (let ((u (hodes-transf s))
                (v (des-state (1+ (des-state-tm w))
                              (des-state-tevs w)
                              (des-state-mem w))))
            (implies (and (B s w)
                          (endp (hstate-otevs s)))
                     (C u v)))
          :hints (("Goal" :in-theory (e/d (good-histp-definition-rule)
                                          (valid-lo-tevs->=-tm
                                           valid-lo-tevs-definition-rule
                                           no-events-at-tm-top-of-queue-1
                                           no-events-at-tm-top-of-queue-2))))))

 (local (defthmd lwfsk2d-l2
          (let ((u (hodes-transf s))
                (v (des-state (1+ (des-state-tm w))
                              (des-state-tevs w)
                              (des-state-mem w))))
            (implies (and (B s w)
                          (not (equal (hstate-tm s)
                                      (timed-event-tm (car (hstate-otevs s))))))
                     (and (C u v)
                          (good-des-statep v))))
          :hints (("Goal" :cases ((consp (hstate-otevs s)))
                   :use ((:instance lwfsk2d-l2-empty)
                         (:instance lwfsk2d-l2-cons))
                   :in-theory (disable hodes-transf-definition-rule
                                       b-definition-rule
                                       c-definition-rule)))))

 (defthmd lwfsk2d-lemma
   (let ((u (hodes-transf s))
         (v (des-state (1+ (des-state-tm w))
                       (des-state-tevs w)
                       (des-state-mem w))))
     (implies (and (B s w)
                   (not (equal (hstate-tm s)
                               (timed-event-tm (car (hstate-otevs s))))))
              (and (good-des-statep v)
                   (spec-transp w v)
                   (C u v))))
   :hints (("Goal" 
            :use ((:instance lwfsk2d-l1)
                  (:instance lwfsk2d-l2))
            :in-theory (disable hodes-transf-definition-rule
                                b-definition-rule
                                c-definition-rule))))
  )

(defun-sk lwfsk2a (u w)
  (exists v
    (and (B u v)
         (spec-transp w v)))
  :witness-dcls ((declare (xargs :guard (and (hstatep u) (des-statep w))
                                 :verify-guards nil))))

(verify-guards lwfsk2a)

(defun-sk lwfsk2d (u w)
  (exists v
    (and (C u v)
         (spec-transp w v)))
  :witness-dcls ((declare (xargs :guard (and (hstatep u) (des-statep w))
                                 :verify-guards nil))))

(verify-guards lwfsk2d)

;; 2a holds when s and w have an event is scheduled (both have same
;; otevs) at current time (both s and w have same time) While 2d holds
;; when s and w have no events scheduled at current time.


(defthm R-preserves-good-state
  (implies (good-hstatep s)
           (good-des-statep (R s)))
  :rule-classes (:forward-chaining))

(defthm B-is-a-LWFSK
  (implies (B s w)
           (or (lwfsk2a (hodes-transf s) w)
               (lwfsk2d (hodes-transf s) w)))
  :hints (("Goal" :cases ((not (equal (hstate-tm s)
                                      (timed-event-tm (car (hstate-otevs s)))))))
          ("Subgoal 2"
           :use ((:instance lwfsk2a-suff
                            (u (hodes-transf s))
                            (v (R (hodes-transf s))))
                 (:instance lwfsk2a-lemma))
           :in-theory (disable hodes-transf-definition-rule
                               good-des-statep
                               b-definition-rule
                               c-definition-rule
                               good-des-statep-definition-rule
                               good-hstatep-definition-rule
                               r-definition-rule
                               lwfsk2a lwfsk2a-suff
                               lwfsk2d lwfsk2d-suff))
          ("Subgoal 1"
           :use ((:instance lwfsk2d-suff
                            (u (hodes-transf s))
                            (v (des-state (1+ (des-state-tm w))
                                          (des-state-tevs w)
                                          (des-state-mem w))))
                 (:instance lwfsk2d-lemma))
           :in-theory (disable hodes-transf-definition-rule
                               b-definition-rule
                               c-definition-rule
                               good-des-statep-definition-rule
                               good-hstatep-definition-rule
                               r-definition-rule
                               lwfsk2a lwfsk2a-suff
                               lwfsk2d lwfsk2d-suff)))
  :rule-classes nil)

(defun-sk lwfsk2f (x y)
  (exists z
    (and (C x z)
         ;; (good-des-statep z)
         (spec-transp y z)
         (< (rankls z x) (rankls y x))))
  :witness-dcls ((declare (xargs :guard (and (hstatep x) (des-statep y))
                                 :verify-guards nil))))

(verify-guards lwfsk2f)

(encapsulate
 nil

 (defunc C-witness-y-tm<x-tm (y)
   :input-contract (des-statep y)
   :output-contract (des-statep (C-witness-y-tm<x-tm y))
   (des-state (1+ (des-state-tm y))
              (des-state-tevs y)
              (des-state-mem y)))

 (local (defthm bla
          (implies (and (timep x) (timep y)
                        (< y x))
                   (<= (1+ y) x))))

 (local (defthm valid-lo-tevs-y-x-tm
          (implies (and (good-hstatep x)  
                        (C x y)
                        (< (des-state-tm y) (hstate-tm x)))
                   (valid-lo-tevs (des-state-tevs y) (hstate-tm x)))))
 
 
 (local (in-theory (disable no-events-at-tm-top-of-queue-2
                            no-events-at-tm-top-of-queue-1)))

 ;; These along with valid-lo-tevs->=-tm are not good rewrite rules
 ;; and often results in significant slow down.
 
 (defthm lwfsk2f-1
   (let ((z (C-witness-y-tm<x-tm y)))
     (implies (and (C x y)
                   (not (B x y))
                   (< (des-state-tm y) (hstate-tm x)))
              (and (C x z)
                   (good-des-statep z)
                   (spec-transp y z)
                   (< (rankls z x) (rankls y x))))))

 
 )

(defthm history-tevs-car
  (implies (and (good-hstatep x)
                (history-valid (hstate-h x))
                (consp (history-otevs (hstate-h x))))
           (equal (timed-event-tm (car (history-otevs (hstate-h x))))
                  (hstate-tm x)))
  :instructions (:bash
                 (:dv 2)
                 (:equiv
                  x
                  (hstate
                   (timed-event-tm (car (history-otevs (hstate-h x))))
                   (insert-otevs
                    (step-events (timed-event-ev (car (history-otevs (hstate-h x))))
                                 (timed-event-tm (car (history-otevs (hstate-h x))))
                                 (history-mem (hstate-h x)))
                    (cdr (history-otevs (hstate-h x))))
                   (step-memory (timed-event-ev (car (history-otevs (hstate-h x))))
                                (timed-event-tm (car (history-otevs (hstate-h x))))
                                (history-mem (hstate-h x)))
                   (history t (history-tm (hstate-h x))
                            (history-otevs (hstate-h x))
                            (history-mem (hstate-h x)))))
                 (:rewrite hstate-constructor-destructors-proper)
                 :up :bash
                 :bash :bash
                 :bash :bash))

;; Proof for (C x (C-witness-y-tm=x-tm x y)) follows
(encapsulate
 nil
 
 (defunc C-witness-y-tm=x-tm (x y)
   :input-contract (and (hstatep x) (des-statep y))
   :output-contract (des-statep (C-witness-y-tm=x-tm x y))
   (let* ((y-tm (des-state-tm y))
          (y-tevs (des-state-tevs y))
          (y-mem (des-state-mem y))
          (h (hstate-h x))
          (hotevs (history-otevs h)))
     (if (consp hotevs)
         (let* ((tev (car hotevs))
                (ev (timed-event-ev tev))
                (new-evs (step-events ev y-tm y-mem))
                (z-mem (step-memory ev y-tm y-mem))
                (z-tevs (remove-ev y-tevs tev))
                (z-tevs (append new-evs z-tevs)))
           (des-state y-tm z-tevs z-mem))
       (des-state (1+ y-tm) y-tevs y-mem))))


 (in-theory (enable good-histp-definition-rule))
 (in-theory (disable valid-lo-tevs->=-tm 
                     valid-lo-tevs-definition-rule))

 (local (defthmd lwfsk2f-spec-ev-transp
          (implies (and (good-hstatep x)
                        (good-des-statep y)
                        (C x y)
                        (not (B x y))
                        (equal (des-state-tm y) (hstate-tm x)))
                   (spec-ev-transp y (C-witness-y-tm=x-tm x y)))
          :hints (("Goal" :in-theory (disable spec-ev-transp-suff)
                   :use ((:instance spec-ev-transp-suff
                                    (w y)
                                    (v (C-witness-y-tm=x-tm x y))
                                    (tev (car (history-otevs (hstate-h x))))))))))
 
 (local (defthmd lwfsk2f-event-at-y-tm
          (implies (and (good-hstatep x)
                        (good-des-statep y)
                        (C x y)
                        (not (B x y))
                        (equal (des-state-tm y) (hstate-tm x)))
                   (events-at-tm (des-state-tevs y) (des-state-tm y)))
          :hints (("Goal" :in-theory (disable events-at-tm-l-set-equiv)
                   :use ((:instance events-at-tm-l-set-equiv
                                    (x (history-otevs (hstate-h x)))
                                    (y (des-state-tevs y))
                                    (tm (timed-event-tm
                                         (car (history-otevs (hstate-h x)))))))))))
                   
 (defthmd lwfsk2f-spec-transp
   (implies (and (C x y)
                 (not (B x y))
                 (equal (des-state-tm y) (hstate-tm x)))
            (spec-transp y (C-witness-y-tm=x-tm x y)))
   :hints (("Goal" :in-theory (e/d (spec-transp-definition-rule)
                                   (good-hstatep-definition-rule
                                    good-des-statep-definition-rule
                                    c-witness-y-tm=x-tm-definition-rule
                                    des-state-equal-definition-rule
                                    c-definition-rule
                                    b-definition-rule))
            :use ((:instance lwfsk2f-event-at-y-tm)
                  (:instance lwfsk2f-spec-ev-transp)))))

 )

(in-theory (disable eventp))

(encapsulate
 nil

 (local (defthm events-at-tm-distributes-over-append
          (implies (and (lo-tep l1) (lo-tep l2) (timep tm))
                   (equal (events-at-tm (append l1 l2) tm)
                          (append (events-at-tm l1 tm)
                                  (events-at-tm l2 tm))))))

 (local (defthm no-new-evs-at-tm
          (implies (and (eventp ev)
                        (timep tm)
                        (memoryp mem))
                   (not (events-at-tm (step-events ev tm mem) tm)))
          :hints (("Goal" :use ((:instance step-events-contract)
                                (:instance no-event-<-tm
                                           (l (step-events ev tm mem))
                                           (tm1 tm)
                                           (tm2 (1+ tm))))
                   :in-theory (e/d (timep) (step-events-contract
                                            no-event-<-tm))))))
 
 (local (defthm events-at-tm-remove-ev
          (implies (and (timed-eventp tev) (lo-tep E)
                        (timep tm))
                   (equal (events-at-tm (remove-ev E tev) tm)
                          (remove-ev (events-at-tm E tm) tev)))))

 (local (defthm l1
          (implies (and (timed-eventp tev) (timep tm)
                        (lo-tep E)
                        (member-equal tev E))
                   (< (len (remove-ev E tev))
                      (len E)))))

 (local (defthm l3
          (implies (and (timed-eventp tev) (timep tm)
                        (lo-tep l2) (memoryp mem)
                        (member-equal tev (events-at-tm l2 tm)))
                   (< (len (events-at-tm (append (step-events
                                                  (timed-event-ev tev)
                                                  tm mem)
                                                 (remove-ev l2 tev))
                                         tm))
                      (len (events-at-tm l2 tm))))
          :hints (("Goal" :in-theory (disable events-at-tm-l-set-equiv
                                              events-at-tm-definition-rule
                                              timed-event
                                              step-events-contract)
                   :use ((:instance step-events-contract (ev (timed-event-ev tev))))
                   :do-not-induct t))))

 (local (defthm l3a
          (implies (and (lo-tep l) (consp l))
                   (member-equal (car l) (events-at-tm l (timed-event-tm (car l)))))
          :hints (("Goal" :in-theory (disable events-at-tm-l-set-equiv)))))

 (local (defthm l3b
          (implies (and (lo-tep l2) (memoryp mem) (consp l2))
                   (< (len (events-at-tm (append (step-events
                                                  (timed-event-ev (car l2))
                                                  (timed-event-tm (car l2)) mem)
                                                 (remove-ev l2 (car l2)))
                                         (timed-event-tm (car l2))))
                      (len (events-at-tm l2 (timed-event-tm (car l2))))))
          :hints (("Goal" :use ((:instance l3 (tev (car l2))
                                           (tm (timed-event-tm (car l2)))))
                   :in-theory (disable l3 events-at-tm-l-set-equiv)
                   :do-not-induct t)
                  ("Goal'''" :in-theory (enable member-equal events-at-tm-definition-rule))))) 

 (local (in-theory (disable l1 l3 events-at-tm-remove-ev
                            no-new-evs-at-tm
                            events-at-tm-distributes-over-append)))


 (local (defthm l3c (implies (and (good-hstatep x)
                                  (good-des-statep y)
                                  (c x y)
                                  (not (b x y))
                                  (equal (des-state-tm y) (hstate-tm x)))
                             (member-equal (car (history-otevs (hstate-h x)))
                                           (events-at-tm (des-state-tevs y)
                                                         (des-state-tm y))))
          :hints (("Goal" :in-theory (disable events-at-tm-l-set-equiv
                                              b-definition-rule
                                              good-des-statep-definition-rule
                                              good-hstatep-definition-rule)
                   :use ((:instance events-at-tm-l-set-equiv
                                    (y (history-otevs (hstate-h x)))
                                    (x (des-state-tevs y))
                                    (tm (des-state-tm y)))
                         (:instance history-tevs-car)
                         (:instance l3a (l (history-otevs (hstate-h x)))))))))

 (defthmd l4
   (implies (and (C x y)
                 (not (B x y))
                 (equal (des-state-tm y) (hstate-tm x)))
            (< (rankls (C-witness-y-tm=x-tm x y) x)
               (rankls y x)))
   :hints (("Goal" :in-theory (disable l3b l3c
                                       events-at-tm-l-set-equiv
                                       b-definition-rule history
                                       historyp
                                       events-at-tm-definition-rule)
            :use ((:instance l3c)
                  (:instance l3
                             (tev (car (history-otevs (hstate-h x))))
                             (tm (timed-event-tm (car (history-otevs (hstate-h x)))))
                             (l2 (DES-STATE-TEVS Y))
                             (mem (DES-STATE-MEM Y)))
                  (:instance l3b
                             (l2 (DES-STATE-TEVS Y))
                             (mem (DES-STATE-MEM Y)))
                  (:instance history-tevs-car)))))
)

                  
(encapsulate
 nil
 (local (defthm remove-ev-valid-1
          (implies (and (o-lo-tep l) (timep tm) (consp l)
                        (valid-lo-tevs l tm))
                   (valid-lo-tevs (remove-ev l (car l)) tm))
          :hints (("Goal" :in-theory (enable valid-lo-tevs-definition-rule)))))

 (local (defthm remove-ev-valid-2
          (implies (and (o-lo-tep l) (timep tm) (consp l)
                        (lo-tep l-equiv)
                        (set-equiv l l-equiv)
                        (valid-lo-tevs l tm))
                   (valid-lo-tevs (remove-ev l-equiv (car l)) tm))
          :hints (("Goal" :use ((:instance remove-ev-valid-1)
                                (:instance remove-ev-preserves-set-equiv
                                           (x l) (y l-equiv)
                                           (tev (car l)))
                                (:instance valid-lo-tevs-setequiv
                                           (l2 (remove-ev l (car l)))
                                           (l1 (remove-ev l-equiv (car l)))
                                           (tm tm)))
                   :in-theory (disable valid-lo-tevs-setequiv
                                       remove-ev-valid-1)
                   :do-not-induct t))))
 
 ;; repeated
 (local (defthm valid-lo-tevs-append
          (implies (and (lo-tep l1) (lo-tep l2)
                        (timep tm1) (timep tm2)
                        (>= tm2 tm1)
                        (valid-lo-tevs l1 tm1)
                        (valid-lo-tevs l2 tm2))
                   (valid-lo-tevs (append l1 l2) tm1))
          :hints (("Goal" :in-theory (e/d (valid-lo-tevs-definition-rule)
                                          (timed-event eventp))))))

 (local (defthm lemma-1
          (implies (and (lo-tep l1) (timep tm) (consp l2)
                        (o-lo-tep l2)
                        (lo-tep l2-equiv)
                        (set-equiv l2 l2-equiv)
                        (valid-lo-tevs l1 (1+ tm))
                        (valid-lo-tevs l2 tm))
                   (valid-lo-tevs (append l1 (remove-ev l2-equiv (car l2))) tm))
          :hints (("Goal" :use ((:instance valid-lo-tevs->=-tm
                                           (E l1) (t1 (1+ tm))
                                           (t2 tm)))
                   :do-not-induct t
                   :in-theory (disable remove-ev-o-lo-tep timep
                                       valid-lo-tevs-o-lo-tep
                                       o-lo-tep-definition-rule
                                       lo-tep
                                       valid-lo-tevs-definition-rule
                                       remove-ev-definition-rule
                                       timed-event)))))
 
 (local (defthmd lwfsk2f-C-1
          (implies (and (good-hstatep x)
                        (good-des-statep y)
                        (C x y)
                        (not (B x y))
                        (equal (des-state-tm y) (hstate-tm x)))
                   (good-des-statep (C-witness-y-tm=x-tm x y)))
          :hints (("Goal" :in-theory (disable remove-ev-o-lo-tep
                                              valid-lo-tevs-o-lo-tep
                                              o-lo-tep-definition-rule
                                              lo-tep
                                              valid-lo-tevs-definition-rule
                                              remove-ev-definition-rule
                                              timed-event)))))

 (in-theory (disable  acl2::commutativity-of-append-under-set-equiv))

 (local (in-theory (disable hstate-equal-definition-rule
                     (:congruence acl2::set-equiv-implies-equal-consp-1))))

 (local (defthm c3
          (implies (and (good-hstatep x)
                        (good-des-statep y)
                        (c x y)
                        (not (b x y))
                        (equal (des-state-tm y) (hstate-tm x)))
                   (equal (des-state-tm (R x)) (des-state-tm (c-witness-y-tm=x-tm x y))))))

 (local (defthm foo-1
          (IMPLIES
           (AND
            (EQUAL (TIMED-EVENT-TM (CAR (HISTORY-OTEVS (HSTATE-H X))))
                   (DES-STATE-TM Y))
            (HSTATEP X)
            (VALID-LO-TEVS (HSTATE-OTEVS X)
                           (DES-STATE-TM Y))
            (HISTORY-OTEVS (HSTATE-H X))
            (HSTATE-EQUAL
             (HSTATE
              (DES-STATE-TM Y)
              (INSERT-OTEVS
               (STEP-EVENTS (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                            (DES-STATE-TM Y)
                            (HISTORY-MEM (HSTATE-H X)))
               (CDR (HISTORY-OTEVS (HSTATE-H X))))
              (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                           (DES-STATE-TM Y)
                           (HISTORY-MEM (HSTATE-H X)))
              (HISTORY T (HISTORY-TM (HSTATE-H X))
                       (HISTORY-OTEVS (HSTATE-H X))
                       (HISTORY-MEM (HSTATE-H X))))
             X)
            (DES-STATEP Y)
            (VALID-LO-TEVS (DES-STATE-TEVS Y)
                           (DES-STATE-TM Y))
            (HISTORY-VALID (HSTATE-H X))
            (SET-EQUIV (DES-STATE-TEVS Y)
                       (HISTORY-OTEVS (HSTATE-H X)))
            (SET-EQUIV (DES-STATE-MEM Y)
                       (HISTORY-MEM (HSTATE-H X)))
            (NOT (EQUAL (DES-STATE (DES-STATE-TM Y)
                                   (HSTATE-OTEVS X)
                                   (HSTATE-MEM X))
                        Y))
            (NOT (SET-EQUIV (DES-STATE-MEM Y)
                            (HSTATE-MEM X)))
            (EQUAL (DES-STATE-TM Y) (HSTATE-TM X))
            (SET-EQUIV (STEP-EVENTS (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                    (DES-STATE-TM Y)
                                    (DES-STATE-MEM Y))
                       (STEP-EVENTS (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                    (DES-STATE-TM Y)
                                    (HISTORY-MEM (HSTATE-H X)))))
           (SET-EQUIV
            (HSTATE-OTEVS X)
            (APPEND (STEP-EVENTS (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                 (DES-STATE-TM Y)
                                 (HISTORY-MEM (HSTATE-H X)))
                    (CDR (HISTORY-OTEVS (HSTATE-H X))))))
          :INSTRUCTIONS
          (:PROMOTE
           :EXPAND (:DV 1)
           (:EQUIV
            X
            (HSTATE
             (DES-STATE-TM Y)
             (INSERT-OTEVS
              (STEP-EVENTS
               (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
               (DES-STATE-TM Y)
               (HISTORY-MEM (HSTATE-H X)))
              (CDR (HISTORY-OTEVS (HSTATE-H X))))
             (STEP-MEMORY
              (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
              (DES-STATE-TM Y)
              (HISTORY-MEM (HSTATE-H X)))
             (HISTORY T (HISTORY-TM (HSTATE-H X))
                      (HISTORY-OTEVS (HSTATE-H X))
                      (HISTORY-MEM (HSTATE-H X))))
            HSTATE-EQUAL)
           (:REWRITE HSTATE-CONSTRUCTOR-DESTRUCTORS-PROPER)
           (:REWRITE APPEND-SETEQUIV-INSERT-TEVS)
           :UP
           :BASH :BASH
           :BASH :BASH
           :BASH :BASH)))

 (local (defthm foo-2
          (IMPLIES
           (AND
            (EQUAL (TIMED-EVENT-TM (CAR (HISTORY-OTEVS (HSTATE-H X))))
                   (DES-STATE-TM Y))
            (HSTATEP X)
            (VALID-LO-TEVS (HSTATE-OTEVS X)
                           (DES-STATE-TM Y))
            (HISTORY-OTEVS (HSTATE-H X))
            (HSTATE-EQUAL
             (HSTATE
              (DES-STATE-TM Y)
              (INSERT-OTEVS
               (STEP-EVENTS (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                            (DES-STATE-TM Y)
                            (HISTORY-MEM (HSTATE-H X)))
               (CDR (HISTORY-OTEVS (HSTATE-H X))))
              (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                           (DES-STATE-TM Y)
                           (HISTORY-MEM (HSTATE-H X)))
              (HISTORY T (HISTORY-TM (HSTATE-H X))
                       (HISTORY-OTEVS (HSTATE-H X))
                       (HISTORY-MEM (HSTATE-H X))))
             X)
            (DES-STATEP Y)
            (VALID-LO-TEVS (DES-STATE-TEVS Y)
                           (DES-STATE-TM Y))
            (HISTORY-VALID (HSTATE-H X))
            (SET-EQUIV (DES-STATE-TEVS Y)
                       (HISTORY-OTEVS (HSTATE-H X)))
            (SET-EQUIV (DES-STATE-MEM Y)
                       (HISTORY-MEM (HSTATE-H X)))
            (NOT (EQUAL (DES-STATE (DES-STATE-TM Y)
                                   (HSTATE-OTEVS X)
                                   (HSTATE-MEM X))
                        Y))
            (NOT (SET-EQUIV (DES-STATE-TEVS Y)
                            (HSTATE-OTEVS X)))
            (EQUAL (DES-STATE-TM Y) (HSTATE-TM X))
            (SET-EQUIV (STEP-EVENTS (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                    (DES-STATE-TM Y)
                                    (DES-STATE-MEM Y))
                       (STEP-EVENTS (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                    (DES-STATE-TM Y)
                                    (HISTORY-MEM (HSTATE-H X)))))
           (SET-EQUIV
            (HSTATE-OTEVS X)
            (APPEND (STEP-EVENTS (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                 (DES-STATE-TM Y)
                                 (DES-STATE-MEM Y))
                    (CDR (HISTORY-OTEVS (HSTATE-H X))))))
          :INSTRUCTIONS
          (:PROMOTE
           :EXPAND (:DV 1)
           (:EQUIV
            X
            (HSTATE
             (DES-STATE-TM Y)
             (INSERT-OTEVS
              (STEP-EVENTS
               (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
               (DES-STATE-TM Y)
               (HISTORY-MEM (HSTATE-H X)))
              (CDR (HISTORY-OTEVS (HSTATE-H X))))
             (STEP-MEMORY
              (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
              (DES-STATE-TM Y)
              (HISTORY-MEM (HSTATE-H X)))
             (HISTORY T (HISTORY-TM (HSTATE-H X))
                      (HISTORY-OTEVS (HSTATE-H X))
                      (HISTORY-MEM (HSTATE-H X))))
            HSTATE-EQUAL)
           (:REWRITE HSTATE-CONSTRUCTOR-DESTRUCTORS-PROPER)
           (:REWRITE APPEND-SETEQUIV-INSERT-TEVS)
           :UP
           :BASH :BASH
           :BASH :BASH
           :BASH :BASH)))

 (local (defthm c2
          (implies (and (good-hstatep x)
                        (good-des-statep y)
                        (c x y)
                        (not (b x y))
                        (equal (des-state-tm y) (hstate-tm x)))
                   (set-equiv (des-state-tevs (R x))
                              (des-state-tevs (c-witness-y-tm=x-tm x y))))
          :hints (("goal" :in-theory (disable history-tevs-car)
                   :use ((:instance history-tevs-car)
                         (:instance step-events-congruence
                                    (ev (timed-event-ev (car (history-otevs (hstate-h x)))))
                                    (tm (des-state-tm y))
                                    (mem (des-state-mem y))
                                    (mem-equiv (history-mem (hstate-h x)))))
                   :do-not '(eliminate-destructors)))))

 (local (defthm foo-3
          (IMPLIES
           (AND
            (EQUAL (TIMED-EVENT-TM (CAR (HISTORY-OTEVS (HSTATE-H X))))
                   (DES-STATE-TM Y))
            (SET-EQUIV (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                    (DES-STATE-TM Y)
                                    (DES-STATE-MEM Y))
                       (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                    (DES-STATE-TM Y)
                                    (HISTORY-MEM (HSTATE-H X))))
            (HSTATEP X)
            (VALID-LO-TEVS (HSTATE-OTEVS X)
                           (DES-STATE-TM Y))
            (HISTORY-OTEVS (HSTATE-H X))
            (HSTATE-EQUAL
             (HSTATE
              (DES-STATE-TM Y)
              (INSERT-OTEVS
               (STEP-EVENTS (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                            (DES-STATE-TM Y)
                            (HISTORY-MEM (HSTATE-H X)))
               (CDR (HISTORY-OTEVS (HSTATE-H X))))
              (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                           (DES-STATE-TM Y)
                           (HISTORY-MEM (HSTATE-H X)))
              (HISTORY T (HISTORY-TM (HSTATE-H X))
                       (HISTORY-OTEVS (HSTATE-H X))
                       (HISTORY-MEM (HSTATE-H X))))
             X)
            (DES-STATEP Y)
            (VALID-LO-TEVS (DES-STATE-TEVS Y)
                           (DES-STATE-TM Y))
            (HISTORY-VALID (HSTATE-H X))
            (SET-EQUIV (DES-STATE-TEVS Y)
                       (HISTORY-OTEVS (HSTATE-H X)))
            (SET-EQUIV (DES-STATE-MEM Y)
                       (HISTORY-MEM (HSTATE-H X)))
            (NOT (EQUAL (DES-STATE (DES-STATE-TM Y)
                                   (HSTATE-OTEVS X)
                                   (HSTATE-MEM X))
                        Y))
            (NOT (SET-EQUIV (DES-STATE-MEM Y)
                            (HSTATE-MEM X)))
            (EQUAL (DES-STATE-TM Y) (HSTATE-TM X)))
           (SET-EQUIV (HSTATE-MEM X)
                      (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                   (DES-STATE-TM Y)
                                   (DES-STATE-MEM Y))))
          :INSTRUCTIONS
          (:PROMOTE
           :EXPAND (:DV 1)
           (:EQUIV
            X
            (HSTATE
             (DES-STATE-TM Y)
             (INSERT-OTEVS
              (STEP-EVENTS
               (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
               (DES-STATE-TM Y)
               (HISTORY-MEM (HSTATE-H X)))
              (CDR (HISTORY-OTEVS (HSTATE-H X))))
             (STEP-MEMORY
              (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
              (DES-STATE-TM Y)
              (HISTORY-MEM (HSTATE-H X)))
             (HISTORY T (HISTORY-TM (HSTATE-H X))
                      (HISTORY-OTEVS (HSTATE-H X))
                      (HISTORY-MEM (HSTATE-H X))))
            HSTATE-EQUAL)
           (:REWRITE HSTATE-CONSTRUCTOR-DESTRUCTORS-PROPER)
           :up :bash
           :bash :bash
           :bash)))

 (local (defthm foo-4
          (IMPLIES
           (AND
            (EQUAL (TIMED-EVENT-TM (CAR (HISTORY-OTEVS (HSTATE-H X))))
                   (DES-STATE-TM Y))
            (SET-EQUIV (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                    (DES-STATE-TM Y)
                                    (DES-STATE-MEM Y))
                       (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                    (DES-STATE-TM Y)
                                    (HISTORY-MEM (HSTATE-H X))))
            (HSTATEP X)
            (VALID-LO-TEVS (HSTATE-OTEVS X)
                           (DES-STATE-TM Y))
            (HISTORY-OTEVS (HSTATE-H X))
            (HSTATE-EQUAL
             (HSTATE
              (DES-STATE-TM Y)
              (INSERT-OTEVS
               (STEP-EVENTS (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                            (DES-STATE-TM Y)
                            (HISTORY-MEM (HSTATE-H X)))
               (CDR (HISTORY-OTEVS (HSTATE-H X))))
              (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                           (DES-STATE-TM Y)
                           (HISTORY-MEM (HSTATE-H X)))
              (HISTORY T (HISTORY-TM (HSTATE-H X))
                       (HISTORY-OTEVS (HSTATE-H X))
                       (HISTORY-MEM (HSTATE-H X))))
             X)
            (DES-STATEP Y)
            (VALID-LO-TEVS (DES-STATE-TEVS Y)
                           (DES-STATE-TM Y))
            (HISTORY-VALID (HSTATE-H X))
            (SET-EQUIV (DES-STATE-TEVS Y)
                       (HISTORY-OTEVS (HSTATE-H X)))
            (SET-EQUIV (DES-STATE-MEM Y)
                       (HISTORY-MEM (HSTATE-H X)))
            (NOT (EQUAL (DES-STATE (DES-STATE-TM Y)
                                   (HSTATE-OTEVS X)
                                   (HSTATE-MEM X))
                        Y))
            (NOT (SET-EQUIV (DES-STATE-TEVS Y)
                            (HSTATE-OTEVS X)))
            (EQUAL (DES-STATE-TM Y) (HSTATE-TM X)))
           (SET-EQUIV (HSTATE-MEM X)
                      (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                   (DES-STATE-TM Y)
                                   (DES-STATE-MEM Y))))
          :INSTRUCTIONS
          (:PROMOTE
           :EXPAND (:DV 1)
           (:EQUIV
            X
            (HSTATE
             (DES-STATE-TM Y)
             (INSERT-OTEVS
              (STEP-EVENTS
               (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
               (DES-STATE-TM Y)
               (HISTORY-MEM (HSTATE-H X)))
              (CDR (HISTORY-OTEVS (HSTATE-H X))))
             (STEP-MEMORY
              (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
              (DES-STATE-TM Y)
              (HISTORY-MEM (HSTATE-H X)))
             (HISTORY T (HISTORY-TM (HSTATE-H X))
                      (HISTORY-OTEVS (HSTATE-H X))
                      (HISTORY-MEM (HSTATE-H X))))
            HSTATE-EQUAL)
           (:REWRITE HSTATE-CONSTRUCTOR-DESTRUCTORS-PROPER)
           :up :bash
           :bash :bash
           :bash)))
 
 (local (defthm c1
          (implies (and (good-hstatep x)
                        (good-des-statep y)
                        (c x y)
                        (not (b x y))
                        (equal (des-state-tm y) (hstate-tm x)))
                   (set-equiv (des-state-mem (c-witness-y-tm=x-tm x y))
                              (des-state-mem (r x))))
          :hints (("goal" :in-theory (disable history-tevs-car)
                   :use ((:instance history-tevs-car)
                         (:instance step-memory-congruence
                                    (ev (timed-event-ev (car (history-otevs (hstate-h x)))))
                                    (tm (des-state-tm y))
                                    (mem (des-state-mem y))
                                    (mem-equiv (history-mem (hstate-h x)))))
                   :do-not '(eliminate-destructors)))))

 (local (defthm lwfsk2f-C-2
          (implies (and (good-hstatep x)
                        (good-des-statep y)
                        (C x y)
                        (not (B x y))
                        (equal (des-state-tm y) (hstate-tm x)))
                   (des-state-equal (R x) (C-witness-y-tm=x-tm x y)))
          :hints (("Goal" :in-theory (disable
                                      good-des-statep-definition-rule
                                      good-hstatep-definition-rule
                                      c-witness-y-tm=x-tm-definition-rule
                                      c-definition-rule
                                      B-definition-rule
                                      r-definition-rule
                                      C-implies-good-state-fw)
                   :use ((:instance C-implies-good-state-fw))))))

 (local (defthm lwfsk2f-C-3
          (implies (and (C x y)
                        (not (B x y))
                        (equal (des-state-tm y) (hstate-tm x)))
                   (B x (C-witness-y-tm=x-tm x y)))
          :hints (("Goal"
                   :use ((:instance lwfsk2f-C-1)
                         (:instance lwfsk2f-C-2)
                         (:instance B-definition-rule
                                    (s x)
                                    (w (C-witness-y-tm=x-tm x y))))
                   :in-theory (disable des-state-equal-definition-rule
                                       good-des-statep-definition-rule
                                       good-hstatep-definition-rule
                                       c-witness-y-tm=x-tm-definition-rule
                                       c-definition-rule
                                       b-definition-rule
                                       r-definition-rule lwfsk2f-C-2
                                       lwfsk2f-C-1)))))


 (local (defthm lwfsk2f-C-4
          (implies (and (C x y)
                        (not (B x y))
                        (equal (des-state-tm y) (hstate-tm x)))
                   (C x (C-witness-y-tm=x-tm x y)))
          :hints (("Goal"
                   :use ((:instance lwfsk2f-C-1)
                         (:instance lwfsk2f-C-3)
                         (:instance C-definition-rule
                                    (x x)
                                    (y (C-witness-y-tm=x-tm x y))))
                   :in-theory (disable des-state-equal-definition-rule
                                       good-des-statep-definition-rule
                                       good-hstatep-definition-rule
                                       c-witness-y-tm=x-tm-definition-rule
                                       c-definition-rule
                                       b-definition-rule
                                       r-definition-rule lwfsk2f-C-2
                                       lwfsk2f-C-1)))))

 (defthm lwfsk2f-C-5
   (implies (and (C x y)
                 (not (B x y))
                 (equal (des-state-tm y) (hstate-tm x)))
            (and (C x (C-witness-y-tm=x-tm x y))
                 (good-des-statep (C-witness-y-tm=x-tm x y))
                 (spec-transp y (C-witness-y-tm=x-tm x y))
                 (< (rankls (C-witness-y-tm=x-tm x y) x)
                    (rankls y x))))
   :hints (("Goal"
            :use ((:instance lwfsk2f-C-1)
                  (:instance lwfsk2f-C-4)
                  (:instance l4)
                  (:instance lwfsk2f-spec-transp))
                  :in-theory (disable des-state-equal-definition-rule
                                      good-des-statep-definition-rule
                                      good-hstatep-definition-rule
                                      c-witness-y-tm=x-tm-definition-rule
                                      c-definition-rule
                                      b-definition-rule
                                      r-definition-rule lwfsk2f-C-4
                                      spec-transp-definition-rule
                                      lwfsk2f-C-1 lwfsk2f-C-2
                                      lwfsk2f-C-3
                                      ACL2::DEFAULT-LESS-THAN-1
                                      ACL2::DEFAULT-LESS-THAN-2
                                      good-des-statep-contract
                                      good-hstatep-contract
                                      (:rewrite events-at-tm-l-set-equiv)))))
 (defthmd case-exhaustive
   (implies (and (good-hstatep x)
                 (good-des-statep y)
                 (C x y)
                 (not (B x y)))
            (<= (des-state-tm y) (hstate-tm x))))
  
 (defthmd lwfsk2f-C
   (let ((z (if (< (des-state-tm y) (hstate-tm x))
                (C-witness-y-tm<x-tm y)
              (c-witness-y-tm=x-tm x y)))) 
     (implies (and (good-hstatep x)
                   (good-des-statep y)
                   (C x y)
                   (not (B x y)))
              (and (C x z)
                   (good-des-statep z)
                   (spec-transp y z)
                   (< (rankls z x) (rankls y x)))))
   :hints (("Goal"
            :cases ((< (des-state-tm y) (hstate-tm x))
                    (= (des-state-tm y) (hstate-tm x)))
            :use ((:instance case-exhaustive)
                  (:instance lwfsk2f-C-5)
                  (:instance lwfsk2f-1))
            :in-theory (disable des-state-equal-definition-rule
                                good-des-statep-definition-rule
                                good-hstatep-definition-rule
                                c-witness-y-tm=x-tm-definition-rule
                                c-witness-y-tm<x-tm-definition-rule
                                c-definition-rule
                                b-definition-rule
                                r-definition-rule lwfsk2f-1
                                case-exhaustive
                                ACL2::DEFAULT-LESS-THAN-1
                                ACL2::DEFAULT-LESS-THAN-2
                                good-des-statep-contract
                                good-hstatep-contract
                                spec-transp-definition-rule
                                rankls-definition-rule
                                (:rewrite events-at-tm-l-set-equiv)
                                ;; c-implies-v-good-des-state
                                lwfsk2f-C-5))))
 
 (local (in-theory (disable des-state-equal-definition-rule
                            good-des-statep-definition-rule
                            good-hstatep-definition-rule
                            c-witness-y-tm=x-tm-definition-rule
                            c-witness-y-tm<x-tm-definition-rule
                            c-definition-rule b-definition-rule
                            r-definition-rule lwfsk2f-1 case-exhaustive
                            ACL2::DEFAULT-LESS-THAN-1
                            ACL2::DEFAULT-LESS-THAN-2
                            good-des-statep-contract good-hstatep-contract
                            spec-transp-definition-rule
                            rankls-definition-rule
                            ;; c-implies-v-good-des-state
                            lwfsk2f-C lwfsk2f
                            lwfsk2f-suff)))

 
 (defthmd C-is-a-witness
   (implies (and (C x y)
                 (not (B x y)))
            (lwfsk2f x y))
   :hints (("Goal"
            :cases ((< (des-state-tm y) (hstate-tm x))
                    (= (des-state-tm y) (hstate-tm x)))
            :use ((:instance case-exhaustive)
                  (:instance lwfsk2f-C)
                  (:instance lwfsk2f-suff (z (c-witness-y-tm=x-tm x y)))
                  (:instance lwfsk2f-suff (z (c-witness-y-tm<x-tm y)))))))
 )

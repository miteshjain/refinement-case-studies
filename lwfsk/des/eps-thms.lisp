(in-package "ACL2S")
(include-book "string-order" :ttags :all)
(include-book "defunbc" :ttags :all)
(include-book "higher-order" :ttags :all)

;; Data definitions for AEPS, a Discrete-Event Simulation system

;; Time is an integer
(defdata time nat)

;; An event is a string (any type will do)
(defdata event string)

;; A timed-event is record consisting of a time and an event.
(defdata timed-event
  (record (tm . time)
          (ev . event)))

;; A multiset of timed-events
(defdata lo-te (listof timed-event))

;; A memory is a collection of global variable (var) and integer pair
(defdata memory (alistof var integer))

;; A state of the AEPS consists of the current time, the list of
;; timed-events to execute and the memory.
(defdata aeps-state
  (record (tm . time)
          (tevs . lo-te)
          (mem . memory)))

;; To avoid having to type acl2:: in front of set-equiv
(defabbrev set-equiv (a b)
  (acl2::set-equiv a b))

(add-macro-fn set-equiv acl2::set-equiv)

;; The definition of aeps-state equality. The timed events are a set,
;; so we have to compare them using set equality. The memory is also a
;; set of variable, value pairs, so we also treat it as a set.
(defunbc aeps-state-equal (s w)
  :input-contract t
  (or (equal s w)
      (and (aeps-statep s)
           (aeps-statep w)
           (equal (aeps-state-tm s)
                  (aeps-state-tm w))
           (set-equiv (aeps-state-mem s)
                      (aeps-state-mem w))
           (set-equiv (aeps-state-tevs s)
                      (aeps-state-tevs w)))))

(defequiv aeps-state-equal)

(defcong aeps-state-equal equal (aeps-state-tm x) 1)
(defcong aeps-state-equal set-equiv (aeps-state-tevs x) 1)
(defcong aeps-state-equal set-equiv (aeps-state-mem x) 1)

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

;; The execution of an event is modeled as an uninterpreted
;; functions. The functions takes the current time and the current
;; memory as input and returns an updated memory and a list of new
;; events that are scheduled to be executed at some time > tm and a
;; list of events to be removed from the Sch. The new events are added
;; into Sch and list of events are removed from Sch.

(encapsulate
 (((step-events-add * * *) => *)
  ((step-events-rm * * *) => *)
  ((step-memory  * * *) => *))
 
 (local (defun step-events-add (ev tm mem)
          (declare (ignore ev tm mem))
          nil))

 (local (defun step-events-rm (ev tm mem)
          (declare (ignore ev tm mem))
          nil))

 (local (defun step-memory (ev tm mem)
          (declare (ignore ev tm mem))
          nil))

 (defthm step-events-add-contract
   (implies (and (eventp ev)
                 (timep tm)
                 (memoryp mem))
            (and (lo-tep (step-events-add ev tm mem))
                 (valid-lo-tevs (step-events-add ev tm mem)
                                (1+ tm)))))

 (defthm step-events-rm-contract
   (implies (and (eventp ev)
                 (timep tm)
                 (memoryp mem))
            (lo-tep (step-events-rm ev tm mem))))
 
 (defthm step-memory-contract
   (implies (and (eventp ev)
                 (timep tm)
                 (memoryp mem))
            (memoryp (step-memory ev tm mem))))

 ;; needs a loop-stopper bad rewrite
 (defthmd step-events-add-congruence
   (implies (and (memoryp mem)
                 (memoryp mem-equiv)
                 (eventp ev)
                 (timep tm)
                 (set-equiv (double-rewrite mem) (double-rewrite mem-equiv)))
            (set-equiv (step-events-add ev tm mem)
                       (step-events-add ev tm mem-equiv))))

 (defthmd step-events-rm-congruence
   (implies (and (memoryp mem)
                 (memoryp mem-equiv)
                 (eventp ev)
                 (timep tm)
                 (set-equiv (double-rewrite mem) (double-rewrite mem-equiv)))
            (set-equiv (step-events-rm ev tm mem)
                       (step-events-rm ev tm mem-equiv))))

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

(defunc remove-tev-high (tev tevs)
  "Removes all occurrences of tev in tevs"
  :input-contract (and (timed-eventp tev) (lo-tep tevs) )
  :output-contract (lo-tep (remove-tev-high tev tevs))
  (filter* (lambda (e1 e2) (not (equal e1 e2))) tevs tev))

(defunc remove-tev (tev tevs)
  "Removes all occurrences of tev in tevs"
  :input-contract (and (timed-eventp tev) (lo-tep tevs))
  :output-contract (lo-tep (remove-tev tev tevs))
  (if (endp tevs)
      nil
    (if (equal (car tevs) tev)
        (remove-tev tev (cdr tevs))
      (cons (car tevs) (remove-tev tev (cdr tevs))))))

(defthmd remove-tev-equiv
  (implies (and (timed-eventp tev) (lo-tep tevs))
           (equal (remove-tev tev tevs)
                  (remove-tev-high tev tevs))))

(defthm remove-tev-member-equal
  (implies (and (timed-eventp tev)
                (lo-tep tevs))
           (not (member-equal tev (remove-tev tev tevs)))))


(defunc remove-tevs (l tevs)
  "Removes all occurrences of timed-events in l from tevs"
  :input-contract (and (lo-tep l) (lo-tep tevs))
  :output-contract (lo-tep (remove-tevs l tevs))
  (if (endp l)
      tevs
    (remove-tev (car l) (remove-tevs (cdr l) tevs))))

(in-theory
 (disable aeps-state aeps-statep aeps-state-tm
          aeps-state-tevs aeps-state-mem))

(defun-sk aeps-ev-transp (w v)
  (exists tev
    (let ((tm (aeps-state-tm w))
          (tevs (aeps-state-tevs w))
          (mem (aeps-state-mem w)))
      (and (timed-eventp tev)
           (equal (timed-event-tm tev) tm)
           (member-equal tev tevs)
           (let* ((ev (timed-event-ev tev))
                  (add-tevs (step-events-add ev tm mem))
                  (rm-tevs (step-events-rm ev tm mem))
                  (new-mem (step-memory ev tm mem))
                  (new-tevs (remove-tevs rm-tevs (remove-tev tev tevs)))
                  (new-tevs (append new-tevs add-tevs)))
             (aeps-state-equal v (aeps-state tm new-tevs new-mem))))))
  :witness-dcls ((declare (xargs :guard (and (aeps-statep w) (aeps-statep v))
                                 :verify-guards nil))))

(verify-guards aeps-ev-transp
               :hints (("goal" :in-theory (disable (:definition timed-event-ev)
                                                   (:definition timed-event-tm)))))

(defunbc aeps-transp (w v)
  "transition relation of AEPS"
  :input-contract (and (aeps-statep w) (aeps-statep v))
  (let ((w-tm (aeps-state-tm w))
        (w-tevs (aeps-state-tevs w))
        (w-mem (aeps-state-mem w)))
    (if (not (events-at-tm w-tevs w-tm))
        (aeps-state-equal v (aeps-state (1+ w-tm) w-tevs w-mem))
      (aeps-ev-transp w v))))


;; PEPS

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
  "An OptAEPS schedule recognizer"
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

;; State of OptAEPS
(defdata peps-state
  (record (tm . time)
          (otevs . o-lo-te)
          (mem . memory)))

(defunbc peps-state-equal (s w)
  :input-contract t
  (or (equal s w)
      (and (peps-statep s)
           (peps-statep w)
           (equal (peps-state-tm s)
                  (peps-state-tm w))
           (equal (peps-state-otevs s)
                  (peps-state-otevs w))
           (set-equiv (peps-state-mem s)
                            (peps-state-mem w)))))

(defequiv peps-state-equal)

(in-theory (disable timep o-lo-tep-definition-rule peps-state
                    peps-state-otevs peps-state-tm peps-state-mem
                    timed-event-ev timed-event-tm))


(encapsulate
 nil
 (local (in-theory (enable  o-lo-tep-definition-rule)))

 (local (defunc remove-tev-ordered (x l)
          :input-contract (and (timed-eventp x) (o-lo-tep l))
          :output-contract (o-lo-tep (remove-tev-ordered x l))
          (cond ((endp l) nil)
                ((equal x (car l)) (cdr l))
                ((te-< x (car l)) l)
                (t (cons (car l) (remove-tev-ordered x (cdr l)))))))

 (local (defthm remove-tev-equal-remove-tev-ordered
          (implies (and (timed-eventp x) (o-lo-tep l))
                   (equal (remove-tev x l)
                          (remove-tev-ordered x l)))))
 
 (defthm remove-tev-from-otevs
   (implies (and (timed-eventp tev)
                 (o-lo-tep otevs))
            (o-lo-tep (remove-tev tev otevs))))
 
 (defthm remove-tevs-from-otevs
   (implies (and (lo-tep l)
                 (o-lo-tep otevs))
           (o-lo-tep (remove-tevs l otevs))))
 )
  
  
(defunc peps-transf (s)
  "transition function for the implementation"
  :input-contract (peps-statep s)
  :output-contract (peps-statep (peps-transf s))
  (let ((tm (peps-state-tm s))
        (otevs (peps-state-otevs s))
        (mem (peps-state-mem s)))
    (if (endp otevs)
        (peps-state (1+ tm) otevs mem)
      (b* ((tev (car otevs))
           (ev (timed-event-ev tev))
           (et (timed-event-tm tev))
           (add-tevs (step-events-add ev et mem))
           (rm-tevs (step-events-rm ev et mem))
           (new-mem (step-memory ev et mem))
           (new-otevs (cdr otevs))
           (new-otevs (remove-tevs rm-tevs new-otevs))
           (new-otevs (insert-otevs add-tevs new-otevs))
           (new-tm (timed-event-tm tev)))
        (peps-state new-tm new-otevs new-mem)))))

;; We next aepscribe an HPEPS machine obtained by augumenting a state
;; of OptAEPS machine with a history component. The transition function
;; of HPEPS is defined by modifying the transition function of
;; OptAEPS such that the history variable records the past information.

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
                   history-tm aeps-state))

(defunc hpeps-transf (s)
  "transition function for HPEPS"
  :input-contract (hstatep s)
  :output-contract (hstatep (hpeps-transf s))
  (let* ((tm (hstate-tm s))
         (otevs (hstate-otevs s))
         (mem (hstate-mem s))
         (hist (history t tm otevs mem)))
    (if (endp otevs)
        (hstate (1+ tm) otevs mem hist)
      (let* ((tev (car otevs))
             (ev (timed-event-ev tev))
             (et (timed-event-tm tev))
             (add-tevs (step-events-add ev et mem))
             (rm-tevs (step-events-rm ev et mem))
             (new-mem (step-memory ev et mem))
             (new-otevs (cdr otevs))
             (new-otevs (remove-tevs rm-tevs new-otevs))
             (new-otevs (insert-otevs add-tevs new-otevs))
             (new-tm (timed-event-tm tev)))
        (hstate new-tm new-otevs new-mem hist)))))


;; OptAEPS refines HPEPS under the refinement map P
(defunc P (s)
  :input-contract (peps-statep s)
  :output-contract (hstatep (P s))
  (let ((tm (peps-state-tm s))
        (otevs (peps-state-otevs s))
        (mem (peps-state-mem s)))
    (hstate tm otevs mem (history nil 0 nil nil))))

(defunbc good-peps-statep (s)
  "good peps state recognizer"
  :input-contract t
  (and (peps-statep s)
       (valid-lo-tevs (peps-state-otevs s) (peps-state-tm s))))

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
         (sh (hpeps-transf hst)))
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
  "SKS/STS relation between OptAEPS and HPEPS"
  :input-contract t
  (and (good-peps-statep s)
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
  (implies (good-peps-statep s)
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
 (local (defunc remove-tev-ordered (x l)
          :input-contract (and (timed-eventp x) (o-lo-tep l))
          :output-contract (o-lo-tep (remove-tev-ordered x l))
          :function-contract-hints (("goal" :in-theory (enable o-lo-tep-definition-rule)))
          (cond ((endp l) nil)
                ((equal x (car l)) (cdr l))
                ((te-< x (car l)) l)
                (t (cons (car l) (remove-tev-ordered x (cdr l)))))))

 (local (defthm remove-tev-equal-remove-tev-ordered
 (implies (and (timed-eventp x) (o-lo-tep l))
          (equal (remove-tev x l)
                 (remove-tev-ordered x l)))
 :hints (("goal" :in-theory (enable o-lo-tep-definition-rule)))))
      
        
 (local (defthm l1a
  (implies (and (o-lo-tep (cons tev l))
                (o-lo-tep l)
                (timed-eventp tev)
                (timed-eventp x))
           (o-lo-tep (cons tev (remove-tev x l))))
  :hints (("goal" :in-theory (enable o-lo-tep-definition-rule)))))



(local (in-theory (disable remove-tev-equal-remove-tev-ordered)))

(local (defthmd l1b
  (implies (and (lo-tep r)
                (lo-tep l)
                (consp r)
                (implies (and (o-lo-tep (cons tev l))
                              (lo-tep (cdr r))
                              (timed-eventp tev))
                         (o-lo-tep (cons tev (remove-tevs (cdr r) l))))
                (lo-tep (cons tev l))
                (ordered-lo-tep (cons tev l))
                (timed-eventp tev))
           (o-lo-tep (cons tev (remove-tevs r l))))
  :hints (("goal" :do-not-induct t
           :use ((:instance o-lo-tep-cdr (l (cons tev (remove-tevs (cdr r) l))))
                 (:instance l1a (x (car r)) (l (remove-tevs (cdr r) l))))
           :in-theory (disable o-lo-tep-cdr l1a ordered-lo-tep-definition-rule)))))

(defthm remove-tevs-o-lo-tep
    (implies (and (o-lo-tep (cons tev l))
                  (lo-tep r)
                  (timed-eventp tev))
             (o-lo-tep (cons tev (remove-tevs r l))))
    :hints (("goal" :in-theory (enable o-lo-tep-definition-rule remove-tevs)
             :induct (remove-tevs r l))
            ("Subgoal *1/2'" :use ((:instance l1b)))))
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
                                              VALID-LO-TEVS->=-TM )
                   :use ((:instance o-lo-tep-cdr (l (cons tev l)))
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
                                              VALID-LO-TEVS->=-TM  l1
                                              VALID-LO-TEVS-SETEQUIV)
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
 
 (defthm remove-tev-valid-1-general
   (implies (and (lo-tep l) (timep tm) (timed-eventp tev)
                 (valid-lo-tevs l tm))
            (valid-lo-tevs (remove-tev tev l) tm))
   :hints (("Goal" :in-theory (enable valid-lo-tevs-definition-rule))))

 (defthm remove-tevs-valid-lo-tevs
          (implies (and (lo-tep l) (timep tm) (lo-tep l1)
                        (valid-lo-tevs l tm))
                   (valid-lo-tevs (remove-tevs l1 l) tm))
          :hints (("Goal" :in-theory (enable valid-lo-tevs-definition-rule))))
              
  (defthm good-peps-inductive
    (implies (good-peps-statep s)
             (good-peps-statep (peps-transf s)))
    :rule-classes (:forward-chaining :rewrite))

  (defthm good-hstate-inductive
    (implies (good-hstatep s)
             (good-hstatep (hpeps-transf s)))
    :hints (("Goal" :in-theory (disable
                                no-events-at-tm-top-of-queue-1
                                no-events-at-tm-top-of-queue-2)))
    :rule-classes (:forward-chaining :rewrite))

  )
 

(encapsulate
 nil
 (local (defthm remove-tev-equal-remove
          (implies (and (lo-tep l) (timed-eventp tev))
                   (equal (remove-tev tev l)
                          (remove-equal tev l)))))

 (local (defun induct-list (r l)
          (if (endp r)
              l
            (cons (car r) (induct-list (cdr r) l)))))
 
 
 (local (defthm a11
          (implies (and (true-listp tevs)
                        (true-listp r2))
                   (equal (set-difference-equal tevs (cons r1 r2))
                          (set-difference-equal (remove-equal r1 tevs) r2)))
          :hints (("goal" :induct (induct-list tevs r1)))))

 
 (local (defthm a2
          (implies (and (lo-tep tevs)
                        (lo-tep r))
                   (equal (remove-tevs r tevs)
                          (set-difference-equal tevs r)))))

 ;; (defthm remove-tevs-l-equiv-is-set-equiv
 ;;   (implies (and (lo-tep tevs)
 ;;                 (lo-tep r)
 ;;                 (lo-tep r-equiv)
 ;;                 (set-equiv r r-equiv))
 ;;            (set-equiv (remove-tevs r tevs)
 ;;                       (remove-tevs r-equiv tevs))))
  (defthm remove-tevs-l-equiv-is-set-equiv
     (implies (and (lo-tep tevs)
                  (lo-tep l)
                  (lo-tep l-equiv)
                  (set-equiv l l-equiv))
             (set-equiv (remove-tevs l tevs)
                        (remove-tevs l-equiv tevs))))

 )
 

(encapsulate
 nil

 (local (defthm remove-tev-equal-remove
          (implies (and (lo-tep l) (timed-eventp tev))
                   (equal (remove-tev tev l)
                          (remove tev l)))))

 (local (in-theory (disable remove-tevs-l-equiv-is-set-equiv)))
 (defthmd remove-tevs-l-equiv-is-set-equiv-1
   (implies (and (lo-tep tevs)
                 (lo-tep l)
                 (lo-tep l-equiv)
                 (set-equiv l l-equiv))
            (set-equiv (remove-tevs tevs l)
                       (remove-tevs tevs l-equiv))))
 
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

 (local (defthmd insert-otevs-l-equiv-is-equal
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

 (local (defthm insert-otevs-l-equiv-is-equal-1
          (implies (and (o-lo-tep otevs)
                        (o-lo-tep otevs-equiv)
                        (set-equiv otevs otevs-equiv) 
                        (lo-tep l)
                        (lo-tep l-equiv)
                        (set-equiv l l-equiv))
                   (equal (insert-otevs l otevs)
                          (insert-otevs l-equiv otevs-equiv)))
          :hints (("Goal"
                   :in-theory (disable insert-otevs-l-equiv-is-equal)                   
                   :use ((:instance insert-otevs-l-equiv-is-set-eqiuv)
                         (:instance o-lo-tep-set-equiv-is-equal (x (insert-otevs l otevs))
                                    (y (insert-otevs l-equiv otevs)))
                         (:instance o-lo-tep-set-equiv-is-equal (x otevs)
                                     (y otevs-equiv)))))))

 
            
 ;; Not sure if it is useful here and/or there might be a better place for
 ;; this congruence relation
 ;; (defthm hpeps-transf-congruence
 ;;   (implies (hstate-equal s w)
 ;;            (hstate-equal (hpeps-transf s)
 ;;                          (hpeps-transf w)))
 ;;   :hints (("goal" :in-theory (disable insert-otevs-l-equiv-is-equal)
 ;;            :use ((:instance step-events-add-congruence
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
 ;;                             (l (step-events-add (timed-event-ev (car (hstate-otevs s)))
 ;;                                             (timed-event-tm (car (hstate-otevs s)))
 ;;                                             (hstate-mem s)))
 ;;                             (l-equiv (step-events-add (timed-event-ev (car (hstate-otevs s)))
 ;;                                                   (timed-event-tm (car (hstate-otevs s)))
 ;;                                                   (hstate-mem w)))))))
 ;;   :rule-classes (:congruence))
 
 (local (defthm A-proof-1
          (implies (and (A s w)
                        (good-hstatep (hpeps-transf w))
                        (good-peps-statep (peps-transf s)))                
                   (A (peps-transf s)
                      (hpeps-transf w)))
          :hints (("Goal" :in-theory (disable good-peps-statep good-hstatep
                                              good-hstate-inductive
                                              good-peps-inductive
                                              valid-lo-tevs->=-tm
                                              no-events-at-tm-top-of-queue-1
                                              no-events-at-tm-top-of-queue-2)
                   :use ((:instance step-events-add-congruence
                                    (ev (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W))))
                                    (tm (TIMED-EVENT-tm (CAR (HSTATE-OTEVS W))))
                                    (mem-equiv (PEPS-STATE-MEM S))
                                    (mem (HSTATE-MEM W)))
                         (:instance step-events-rm-congruence
                                    (ev (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W))))
                                    (tm (TIMED-EVENT-tm (CAR (HSTATE-OTEVS W))))
                                    (mem-equiv (PEPS-STATE-MEM S))
                                    (mem (HSTATE-MEM W)))
                         (:instance step-memory-congruence
                                    (ev (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W))))
                                    (tm (TIMED-EVENT-tm (CAR (HSTATE-OTEVS W))))
                                    (mem-equiv (PEPS-STATE-MEM S))
                                    (mem (HSTATE-MEM W)))))
                  ("Subgoal 3'"
                   :use ((:instance step-events-add-congruence
                                    (ev (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W))))
                                    (tm (TIMED-EVENT-tm (CAR (HSTATE-OTEVS W))))
                                    (mem-equiv (PEPS-STATE-MEM S))
                                    (mem (HSTATE-MEM W)))
                         (:instance step-events-rm-congruence
                                    (ev (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W))))
                                    (tm (TIMED-EVENT-tm (CAR (HSTATE-OTEVS W))))
                                    (mem-equiv (PEPS-STATE-MEM S))
                                    (mem (HSTATE-MEM W)))
                         (:instance remove-tevs-l-equiv-is-set-equiv
                                    (tevs (cdr (hstate-otevs w)))
                                    (l (step-events-rm (timed-event-ev (car (hstate-otevs w)))
                                                       (timed-event-tm (car (hstate-otevs w)))
                                                       (peps-state-mem s)))
                                    (l-equiv  (step-events-rm (timed-event-ev (car (hstate-otevs w)))
                                                              (timed-event-tm (car (hstate-otevs w)))
                                                              (hstate-mem w))))
                         (:instance insert-otevs-l-equiv-is-equal-1
                                    (otevs (REMOVE-TEVS (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W)))
                                                                        (TIMED-EVENT-TM (CAR (HSTATE-OTEVS W)))
                                                                        (PEPS-STATE-MEM S))
                                                        (CDR (HSTATE-OTEVS W))))
                                    (otevs-equiv (REMOVE-TEVS (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W)))
                                                                              (TIMED-EVENT-TM (CAR (HSTATE-OTEVS W)))
                                                                              (HSTATE-MEM W))
                                                              (CDR (HSTATE-OTEVS W))))
                                    (l (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W)))
                                                    (TIMED-EVENT-TM (CAR (HSTATE-OTEVS W)))
                                                    (PEPS-STATE-MEM S)))
                                    (l-equiv (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W)))
                                                          (TIMED-EVENT-TM (CAR (HSTATE-OTEVS W)))
                                                          (HSTATE-MEM W)))))
                   :in-theory (disable insert-otevs-l-equiv-is-equal-1 remove-tevs-l-equiv-is-set-equiv))
                  ("Subgoal 2'"
                   :use ((:instance step-events-add-congruence
                                    (ev (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W))))
                                    (tm (TIMED-EVENT-tm (CAR (HSTATE-OTEVS W))))
                                    (mem-equiv (PEPS-STATE-MEM S))
                                    (mem (HSTATE-MEM W)))
                         (:instance step-events-rm-congruence
                                    (ev (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W))))
                                    (tm (TIMED-EVENT-tm (CAR (HSTATE-OTEVS W))))
                                    (mem-equiv (PEPS-STATE-MEM S))
                                    (mem (HSTATE-MEM W)))
                         (:instance remove-tevs-l-equiv-is-set-equiv
                                    (tevs (cdr (hstate-otevs w)))
                                    (l (step-events-rm (timed-event-ev (car (hstate-otevs w)))
                                                       (timed-event-tm (car (hstate-otevs w)))
                                                       (peps-state-mem s)))
                                    (l-equiv  (step-events-rm (timed-event-ev (car (hstate-otevs w)))
                                                              (timed-event-tm (car (hstate-otevs w)))
                                                              (hstate-mem w))))
                         (:instance insert-otevs-l-equiv-is-equal-1
                                    (otevs (REMOVE-TEVS (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W)))
                                                                        (TIMED-EVENT-TM (CAR (HSTATE-OTEVS W)))
                                                                        (PEPS-STATE-MEM S))
                                                        (CDR (HSTATE-OTEVS W))))
                                    (otevs-equiv (REMOVE-TEVS (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W)))
                                                                              (TIMED-EVENT-TM (CAR (HSTATE-OTEVS W)))
                                                                              (HSTATE-MEM W))
                                                              (CDR (HSTATE-OTEVS W))))
                                    (l (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W)))
                                                    (TIMED-EVENT-TM (CAR (HSTATE-OTEVS W)))
                                                    (PEPS-STATE-MEM S)))
                                    (l-equiv (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W)))
                                                          (TIMED-EVENT-TM (CAR (HSTATE-OTEVS W)))
                                                          (HSTATE-MEM W)))))
                   :in-theory (disable INSERT-OTEVS-L-EQUIV-IS-EQUAL-1 remove-tevs-l-equiv-is-set-equiv))
                  ("Subgoal 1"
                   :use ((:instance step-events-add-congruence
                                    (ev (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W))))
                                    (tm (TIMED-EVENT-tm (CAR (HSTATE-OTEVS W))))
                                    (mem-equiv (PEPS-STATE-MEM S))
                                    (mem (HSTATE-MEM W)))
                         (:instance step-events-rm-congruence
                                    (ev (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W))))
                                    (tm (TIMED-EVENT-tm (CAR (HSTATE-OTEVS W))))
                                    (mem-equiv (PEPS-STATE-MEM S))
                                    (mem (HSTATE-MEM W)))
                         (:instance remove-tevs-l-equiv-is-set-equiv
                                    (tevs (cdr (hstate-otevs w)))
                                    (l (step-events-rm (timed-event-ev (car (hstate-otevs w)))
                                                       (timed-event-tm (car (hstate-otevs w)))
                                                       (peps-state-mem s)))
                                    (l-equiv  (step-events-rm (timed-event-ev (car (hstate-otevs w)))
                                                              (timed-event-tm (car (hstate-otevs w)))
                                                              (hstate-mem w))))
                         (:instance insert-otevs-l-equiv-is-equal-1
                                    (otevs (REMOVE-TEVS (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W)))
                                                                        (TIMED-EVENT-TM (CAR (HSTATE-OTEVS W)))
                                                                        (PEPS-STATE-MEM S))
                                                        (CDR (HSTATE-OTEVS W))))
                                    (otevs-equiv (REMOVE-TEVS (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W)))
                                                                              (TIMED-EVENT-TM (CAR (HSTATE-OTEVS W)))
                                                                              (HSTATE-MEM W))
                                                              (CDR (HSTATE-OTEVS W))))
                                    (l (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W)))
                                                    (TIMED-EVENT-TM (CAR (HSTATE-OTEVS W)))
                                                    (PEPS-STATE-MEM S)))
                                    (l-equiv (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HSTATE-OTEVS W)))
                                                          (TIMED-EVENT-TM (CAR (HSTATE-OTEVS W)))
                                                          (HSTATE-MEM W)))))
                   :in-theory (disable INSERT-OTEVS-L-EQUIV-IS-EQUAL-1 remove-tevs-l-equiv-is-set-equiv)))))

 (local (defthm A-implies-good-states
          (implies (A s w)
                   (and (good-peps-statep s)
                        (good-hstatep w)))
          :hints (("Goal" :in-theory (disable p-definition-rule
                                              good-hstatep-definition-rule
                                              good-peps-statep-definition-rule)))))
 
 (defthmd A-is-a-RWFSK
   (implies (and (A s w))
            (A (peps-transf s)
               (hpeps-transf w)))
   :hints (("Goal" :in-theory (disable A-definition-rule
                                       hpeps-transf-definition-rule
                                       good-peps-statep-definition-rule
                                       good-hstatep-definition-rule))))

 )

;; HPEPS refines AEPS

(defunc R (s)
  "A refinement map from an HPEPS state to a AEPS state"
  :input-contract (hstatep s)
  :output-contract (aeps-statep (R s))
  (aeps-state (hstate-tm s) (hstate-otevs s) (hstate-mem s)))

(defunbc good-aeps-statep (s)
  :input-contract t
  (and (aeps-statep s)
       (valid-lo-tevs (aeps-state-tevs s) (aeps-state-tm s))))

(defthm good-aeps-state-is-aeps-state-fw
  (implies (good-aeps-statep x)
           (aeps-statep x))
  :rule-classes (:rewrite :forward-chaining))

(defunbc B (s w)
  "SKS relation between an OptAEPS state and a AEPS state"
  :input-contract t
  (and (good-hstatep s)
       (good-aeps-statep w)
       (aeps-state-equal (R s) w)))

(defthm B-implies-good-states
  (implies (B s w)
           (and (good-hstatep s) (good-aeps-statep w)))
  :rule-classes (:forward-chaining))

(defthm R-good
  (implies (good-hstatep s)
           (B s (R s))))

;; Not sure if it will be useful
(defcong hstate-equal aeps-state-equal (R x) 1)

;; LWFSK witness

(defunbc O (x y)
  :input-contract t
  (and (good-hstatep x)
       (good-aeps-statep y)
       (or (B x y)
           (and (history-valid (hstate-h x))
                (consp (history-otevs (hstate-h x)))
                (<= (aeps-state-tm y) (hstate-tm x))
                (set-equiv (aeps-state-tevs y)
                           (history-otevs (hstate-h x)))
                (set-equiv (aeps-state-mem y)
                           (history-mem (hstate-h x)))))))

(defthm O-implies-good-state-fw
  (implies (O x y)
           (and (good-hstatep x)
                (good-aeps-statep y)))
  :hints (("Goal" :in-theory (disable good-aeps-statep-definition-rule
                                      good-hstatep-definition-rule))))

(defunc rankls (y x)
  :input-contract (and (aeps-statep y) (hstatep x))
  :output-contract (natp (rankls y x))
  (nfix (- (+ (hstate-tm x)
              (len (events-at-tm (aeps-state-tevs y) (hstate-tm x))))
           (aeps-state-tm y))))


(encapsulate
 nil
 ;; remove-tev on ordererd list
 (local (defthm o-lo-tep-member-equal
          (implies (o-lo-tep (cons x l))
                   (not (member-equal x l)))
          :hints (("goal" :in-theory (enable te-<-definition-rule o-lo-tep member-equal)))))
 
 (local  (defthm o-lo-tep-noduplicates
           (implies (o-lo-tep x)
                    (no-duplicatesp-equal x))
           :hints (("goal" :in-theory (enable te-<-definition-rule no-duplicatesp-equal o-lo-tep)))))

 (local (defthm remove-tev-not-member
          (implies (and (o-lo-tep x) (timed-eventp tev)
                        (not (member-equal tev x)))
                   (equal (remove-tev tev x)
                          x))))

 (defthm remove-tev-o-lo-tep
   (implies (and (o-lo-tep x) (consp x))
            (equal (remove-tev (car x) x)
                   (cdr x))))
 )

(encapsulate
 nil
 (local (defthm remove-tev-member-1
          (implies (and (lo-tep l) (timed-eventp tev)
                        (not (equal x tev))
                        (member-equal x l))
                   (member-equal x (remove-tev tev l)))))
 
 (local (defthm remove-tev-preserves-subset
          (implies (and (lo-tep x) (lo-tep y) (timed-eventp tev)
                        (subsetp-equal (double-rewrite x) (double-rewrite y)))
                   (subsetp-equal (remove-tev tev x)
                                  (remove-tev tev y)))
          :hints (("goal" :in-theory (enable  subsetp-equal)))))

 (defthmd remove-tev-preserves-set-equiv
   (implies (and (lo-tep x) (lo-tep y) (timed-eventp tev)
                 (set-equiv x y))
            (set-equiv (remove-tev tev x)
                       (remove-tev tev y)))
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
            (set-equiv (append l (remove-tev (car x) y))
                       (insert-otevs l (cdr x))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance remove-tev-preserves-set-equiv
                             (x y) (y x)
                             (tev (car x))))
            :in-theory (disable remove-tev-definition-rule
                                remove-tev-preserves-set-equiv))))

(encapsulate
 nil
 (local (defthm lemma
          (implies (and (lo-tep l)
                        (lo-tep r)
                        (o-lo-tep x)
                        x (lo-tep y)
                        (set-equiv x y))
                   (set-equiv  (remove-tevs r (cdr x))
                               (remove-tevs r (remove-tev (car x) y))))
          :hints (("goal" :do-not-induct t
                   :use ((:instance remove-tev-preserves-set-equiv
                                    (x y) (y x)
                                    (tev (car x)))
                         (:instance remove-tev-o-lo-tep (x x))
                         (:instance remove-tevs-l-equiv-is-set-equiv-1
                                    (l (cdr x))
                                    (l-equiv (remove-tev (car x) y))
                                    (tevs r)))
                   :in-theory (disable remove-tev-definition-rule
                                       remove-tev-o-lo-tep
                                       remove-tev-preserves-set-equiv
                                       remove-tevs-l-equiv-is-set-equiv)))))

 (defthm new-tevs-append-insert-lemma-1
   (implies (and (lo-tep l) (lo-tep r)
                 (o-lo-tep x) (consp x)
                 (lo-tep y) (set-equiv x y))
            (set-equiv (append l (remove-tevs r (remove-tev (car x) y)))
                       (insert-otevs l (remove-tevs r (cdr x)))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance remove-tev-preserves-set-equiv (y x) (x y)
                             (tev (car x)))
                  (:instance remove-tevs-l-equiv-is-set-equiv-1
                                                    (l (remove-tev (car x) x))
                                                    (l-equiv (remove-tev (car x) y))
                                                    (tevs r)))
            :in-theory (disable remove-tev-definition-rule
                                remove-tev-o-lo-tep
                                remove-tev-preserves-set-equiv
                                remove-tevs-l-equiv-is-set-equiv
                                remove-tevs-l-equiv-is-set-equiv-1))))
 
           
)

(encapsulate
 nil
 ;; Case when there is an event to be picked (the first one) in
 ;; HPEPS at current time. In this case , we show that (R
 ;; (hpeps-transf s)) is a witness for lwfsk2a.

 (local (in-theory (disable eventp valid-lo-tevs->=-tm
                            no-events-at-tm-top-of-queue-1
                            no-events-at-tm-top-of-queue-2)))
 
 (local (defthmd lwfsk2a-B
          (implies (B s w)
                   (B (hpeps-transf s)
                      (R (hpeps-transf s))))
          :hints (("goal" :in-theory (disable good-aeps-statep
                                              good-hstatep
                                              hpeps-transf
                                              r-definition-rule)
                   :use ((:instance good-hstate-inductive))))))

 (local (in-theory (disable good-histp-definition-rule)))

 (local (defthm lwfsk2a-l1-empty
          (implies (and (B s w)
                        (endp (hstate-otevs s)))
                   (and (aeps-transp w (R (hpeps-transf s)))
                        (B (hpeps-transf s) (R (hpeps-transf s)))))
          :hints (("Goal" :in-theory (e/d (valid-lo-tevs-definition-rule
                                           good-histp-definition-rule) ())))))


 ;; TODO: why this intermediate lemma is needed for lwfsk2a-aeps-step
 (local (defthm e1
          (implies (and (B s w)
                        (consp (hstate-otevs s))
                        (equal (hstate-tm s)
                               (timed-event-tm (car (hstate-otevs s)))))
                   (and (equal (timed-event-tm (car (hstate-otevs s))) (aeps-state-tm w))
                        (timed-eventp (car (hstate-otevs s)))
                        (member-equal (car (hstate-otevs s)) (aeps-state-tevs w))
                        (equal (hstate-tm s) (aeps-state-tm w))
                        (set-equiv
                         (insert-otevs (step-events-add (timed-event-ev (car (hstate-otevs s)))
                                                        (hstate-tm s)
                                                        (hstate-mem s))
                                       (remove-tevs (step-events-rm (timed-event-ev (car (hstate-otevs s)))
                                                                    (aeps-state-tm w)
                                                                    (hstate-mem s))
                                                    (cdr (hstate-otevs s))))
                         (append (step-events-add (timed-event-ev (car (hstate-otevs s)))
                                              (aeps-state-tm w)
                                              (aeps-state-mem w))
                                 (remove-tevs (step-events-rm (timed-event-ev (car (hstate-otevs s)))
                                                              (aeps-state-tm w)
                                                              (aeps-state-mem w))
                                              (remove-tev (car (hstate-otevs s))
                                                          (aeps-state-tevs w)))))
                        (set-equiv (step-memory (timed-event-ev (car (hstate-otevs s)))
                                                (hstate-tm s)
                                                (hstate-mem s))
                                   (step-memory (timed-event-ev (car (hstate-otevs s)))
                                                (aeps-state-tm w)
                                                (aeps-state-mem w)))))
          :hints (("Subgoal 2'" :in-theory (disable step-events-add-congruence
                                                    step-events-rm-congruence
                                                    remove-tevs-l-equiv-is-set-equiv)
                   :use ((:instance step-events-add-congruence
                                    (ev (timed-event-ev (car (hstate-otevs s))))
                                    (tm (aeps-state-tm w))
                                    (mem (aeps-state-mem w))
                                    (mem-equiv (hstate-mem s)))
                         (:instance step-events-rm-congruence
                                    (ev (timed-event-ev (car (hstate-otevs s))))
                                    (tm (aeps-state-tm w))
                                    (mem (aeps-state-mem w))
                                    (mem-equiv (hstate-mem s)))
                         (:instance remove-tevs-l-equiv-is-set-equiv
                                    (tevs (cdr (hstate-otevs s)))
                                    (l (step-events-rm (timed-event-ev (car (hstate-otevs s)))
                                                       (aeps-state-tm w)
                                                       (aeps-state-mem w)))
                                    (l-equiv (step-events-rm (timed-event-ev (car (hstate-otevs s)))
                                                             (aeps-state-tm w)
                                                             (hstate-mem s))))))
                  ("Subgoal 1'" :in-theory (disable step-memory-congruence)
                   :use ((:instance step-memory-congruence
                                    (ev (TIMED-EVENT-EV (CAR (HSTATE-OTEVS S))))
                                    (tm (AEPS-STATE-TM W))
                                    (mem (AEPS-STATE-MEM W))
                                    (mem-equiv (HSTATE-MEM S))))))))
 

 (local (defthmd  bla
          (implies (and 
                    (SET-EQUIV
                     (INSERT-OTEVS
                      (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HSTATE-OTEVS S)))
                                       (AEPS-STATE-TM W)
                                       (HSTATE-MEM S))
                      (REMOVE-TEVS (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HSTATE-OTEVS S)))
                                                   (AEPS-STATE-TM W)
                                                   (HSTATE-MEM S))
                                   (CDR (HSTATE-OTEVS S))))
                     (APPEND
                      (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HSTATE-OTEVS S)))
                                       (AEPS-STATE-TM W)
                                       (AEPS-STATE-MEM W))
                      (REMOVE-TEVS (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HSTATE-OTEVS S)))
                                                   (AEPS-STATE-TM W)
                                                   (AEPS-STATE-MEM W))
                                   (REMOVE-TEV (CAR (HSTATE-OTEVS S))
                                               (AEPS-STATE-TEVS W)))))
                    (EQUAL (HSTATE-TM S) (AEPS-STATE-TM W)))

                   (SET-EQUIV
                    (INSERT-OTEVS
                     (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HSTATE-OTEVS S)))
                                      (HSTATE-TM S)
                                      (HSTATE-MEM S))
                     (REMOVE-TEVS (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HSTATE-OTEVS S)))
                                                  (HSTATE-TM S)
                                                  (HSTATE-MEM S))
                                  (CDR (HSTATE-OTEVS S))))
                    (APPEND
                     (REMOVE-TEVS (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HSTATE-OTEVS S)))
                                                  (AEPS-STATE-TM W)
                                                  (AEPS-STATE-MEM W))
                                  (REMOVE-TEV (CAR (HSTATE-OTEVS S))
                                              (AEPS-STATE-TEVS W)))
                     (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HSTATE-OTEVS S)))
                                      (AEPS-STATE-TM W)
                                      (AEPS-STATE-MEM W)))))))
 (local (defthmd lwfsk2a-aeps-step
          (implies (and (B s w)
                        (consp (hstate-otevs s))
                        (equal (hstate-tm s)
                               (timed-event-tm (car (hstate-otevs s)))))
                   (aeps-ev-transp w (R (hpeps-transf s))))
          :hints (("goal" :use ((:instance aeps-ev-transp-suff
                                           (tev (car (hstate-otevs s)))
                                           (v (R (hpeps-transf s))))
                                (:instance e1))
                   :in-theory (disable aeps-ev-transp-suff 
                                       acl2::set-equiv-is-an-equivalence
                                       remove-tevs-l-equiv-is-set-equiv
                                       acl2::commutativity-of-append-under-set-equiv
                                       e1
                                       aeps-ev-transp))
                  ("Subgoal 12" :use ((:instance bla)))
                  ("Subgoal 11" :use ((:instance bla)))
                  ("Subgoal 10" :use ((:instance bla))))))
 
 (local (defthm lwfsk2a-l1-cons
          (implies (and (B s w)
                        (consp (hstate-otevs s))
                        (equal (hstate-tm s)
                               (timed-event-tm (car (hstate-otevs s)))))
                   (and (aeps-ev-transp w (R (hpeps-transf s)))
                        (B (hpeps-transf s) (R (hpeps-transf s)))))
          :hints (("goal" :use ((:instance lwfsk2a-aeps-step)
                                (:instance lwfsk2a-B))))))

 (local (defthm events-at-tm-cons
          (implies (and (lo-tep x) (consp x))
                   (events-at-tm x (timed-event-tm (car x))))))

 (local (defthm lwfsk2a-l1-events-at-tm
          (implies (and (B s w)
                        (consp (hstate-otevs s))
                        (equal (hstate-tm s)
                               (timed-event-tm (car (hstate-otevs s)))))
                   (events-at-tm (aeps-state-tevs w) (aeps-state-tm w)))
          :hints (("Goal" :in-theory (disable
                                      events-at-tm-l-set-equiv
                                      timed-event eventp)
                   :use ((:instance events-at-tm-l-set-equiv
                                    (x (aeps-state-tevs w))
                                    (y (hstate-otevs s))
                                    (tm (hstate-tm s))))))))

 (defthmd lwfsk2a-lemma
   (implies (and (B s w)
                 (equal (hstate-tm s)
                        (timed-event-tm (car (hstate-otevs s)))))
            (and (aeps-transp w (R (hpeps-transf s)))
                 (B (hpeps-transf s) (R (hpeps-transf s)))))
   :hints (("Goal" :cases ((consp (hstate-otevs s)))
            :in-theory (e/d ()(r-definition-rule
                               aeps-ev-transp
                               aeps-state-equal-definition-rule
                               hpeps-transf-definition-rule
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
 (local (defthmd rlwfsk2b-l1
          (implies (and (B s w)
                        (not (equal (hstate-tm s)
                                    (timed-event-tm (car (hstate-otevs s))))))
                   (aeps-transp w (aeps-state (1+ (aeps-state-tm w))
                                             (aeps-state-tevs w)
                                             (aeps-state-mem w))))
          :hints (("Goal" :in-theory (disable (:definition events-at-tm-definition-rule)
                                              (:definition aeps-ev-transp)
                                              valid-lo-tevs->=-tm
                                              no-events-at-tm-top-of-queue-1
                                              no-events-at-tm-top-of-queue-2
                                              events-at-tm-l-set-equiv)
                   :use ((:instance no-events-at-tm-top-of-queue-1
                                    (E (hstate-otevs s))
                                    (tm (hstate-tm s)))
                         (:instance events-at-tm-l-set-equiv
                                    (x (aeps-state-tevs w))
                                    (y (hstate-otevs s))
                                    (tm (aeps-state-tm w))))))))

 ;; (local (defthm car-valid-lo-tevs
 ;;          (implies (and (timep tm) (o-lo-tep l) l
 ;;                        (valid-lo-tevs l tm)
 ;;                        (not (equal tm (timed-event-tm (car l)))))
 ;;                   (< tm (timed-event-tm (car l))))
 ;;          :hints (("goal" :in-theory (enable valid-lo-tevs-definition-rule)))))

 ;; (local (defthm bla1
 ;;          (implies (and (timep tm1) (timep tm2)
 ;;                        (lo-tep l1)
 ;;                        (o-lo-tep l2)
 ;;                        (equal tm1 tm2)
 ;;                        (valid-lo-tevs l1 tm1)
 ;;                        (set-equiv l1 l2) l2
 ;;                        (not (equal tm1 (timed-event-tm (car l2)))))
 ;;                   (< tm1 (timed-event-tm (car l2))))))
 
 
 (local (defthmd rlwfsk2b-l2a
          (implies (and (B s w) ;(HSTATE-OTEVS S)
                        (not (equal (hstate-tm s)
                                    (timed-event-tm (car (hstate-otevs s))))))
                   (< (aeps-state-tm w) (hstate-tm (hpeps-transf s))))
          :hints (("Goal" :in-theory (disable no-events-at-tm-top-of-queue-2
                                              events-at-tm-l-set-equiv)
                   :use ((:instance no-events-at-tm-top-of-queue-2
                                    (E (hstate-otevs s))
                                    (tm (hstate-tm s)))
                         (:instance events-at-tm-l-set-equiv
                                    (x (hstate-otevs s))
                                    (y (aeps-state-tevs w))
                                    (tm (hstate-tm s))))))))

 (local (defthm bla
          (implies (and (timep x) (timep y)
                        (< y x))
                   (<= (1+ y) x))))

 (local (defthmd rlwfsk2b-l2b
          (implies (and (B s w) 
                        (not (equal (hstate-tm s)
                                    (timed-event-tm (car (hstate-otevs s))))))
                   (<= (1+ (aeps-state-tm w)) (hstate-tm (hpeps-transf s))))
          :hints (("Goal" :use ((:instance rlwfsk2b-l2a))
                   :in-theory (e/d (timep) (valid-lo-tevs->=-tm
                                            no-events-at-tm-top-of-queue-1
                                            no-events-at-tm-top-of-queue-2
                                            hpeps-transf-definition-rule))))))

 (local (defthmd rlwfsk2b-l2c
          (implies (and (B s w) ;(hstate-otevs s)
                        (not (equal (hstate-tm s)
                                    (timed-event-tm (car (hstate-otevs s))))))
                   (let ((u (hpeps-transf s)))
                     (and (<= (1+ (aeps-state-tm w)) (hstate-tm u))
                          (set-equiv (aeps-state-tevs w)
                                     (history-otevs (hstate-h u)))
                          (set-equiv (aeps-state-mem w)
                                     (history-mem (hstate-h u))))))
          :hints (("Goal" :in-theory (e/d (good-histp-definition-rule
                                           rlwfsk2b-l2b
                                           valid-lo-tevs->=-tm)
                                          (valid-lo-tevs-definition-rule))))))

 (local (defthmd  O-good-state-valid-lo-tevs
          (implies
           (and
            (valid-lo-tevs (hstate-otevs s)
                           (timed-event-tm (car (hstate-otevs s))))
            (<= (+ 1 (aeps-state-tm w))
                (timed-event-tm (car (hstate-otevs s))))
            (set-equiv (aeps-state-tevs w)
                       (hstate-otevs s))
            (aeps-state-tevs w)
            (hstatep s)
            (valid-lo-tevs (hstate-otevs s)
                           (hstate-tm s))
            (aeps-statep w))
           (valid-lo-tevs (aeps-state-tevs w)
                          (+ 1 (aeps-state-tm w))))
          :hints (("Goal" :use ((:instance valid-lo-tevs->=-tm
                                           (t1 (timed-event-tm (car (hstate-otevs s))))
                                           (t2 (1+ (aeps-state-tm w)))
                                           (E (hstate-otevs s)))
                                (:instance valid-lo-tevs-o-lo-tep
                                           (E (hstate-otevs s))))
                   :in-theory (e/d()
                                  (valid-lo-tevs-o-lo-tep
                                   valid-lo-tevs->=-tm
                                   valid-lo-tevs-definition-rule
                                   ordered-lo-tep-definition-rule timed-event
                                   aeps-state-equal-definition-rule))))))
 
 (local (defthmd rlwfsk2b-l2-cons
          (let ((u (hpeps-transf s))
                (v (aeps-state (1+ (aeps-state-tm w))
                              (aeps-state-tevs w)
                              (aeps-state-mem w))))
            (implies (and (B s w)
                          (consp (hstate-otevs s))
                          (not (equal (hstate-tm s)
                                      (timed-event-tm (car (hstate-otevs s))))))
                     (O u v)))
          :hints (("Goal" :in-theory (e/d () ( o-lo-tep
                                               valid-lo-tevs-definition-rule
                                               aeps-state-equal-definition-rule
                                               good-histp-definition-rule
                                               hstate-equal-definition-rule))
                   :use ((:instance rlwfsk2b-l2c)
                         (:instance good-hstate-inductive)))
                  ("Subgoal 3'" :in-theory (disable O-good-state-valid-lo-tevs)
                   :use ((:instance O-good-state-valid-lo-tevs))))))



 (local (defthmd rlwfsk2b-l2-empty
          (let ((u (hpeps-transf s))
                (v (aeps-state (1+ (aeps-state-tm w))
                              (aeps-state-tevs w)
                              (aeps-state-mem w))))
            (implies (and (B s w)
                          (endp (hstate-otevs s)))
                     (O u v)))
          :hints (("Goal" :in-theory (e/d (good-histp-definition-rule)
                                          (valid-lo-tevs->=-tm
                                           valid-lo-tevs-definition-rule
                                           no-events-at-tm-top-of-queue-1
                                           no-events-at-tm-top-of-queue-2))))))

 (local (defthmd rlwfsk2b-l2
          (let ((u (hpeps-transf s))
                (v (aeps-state (1+ (aeps-state-tm w))
                              (aeps-state-tevs w)
                              (aeps-state-mem w))))
            (implies (and (B s w)
                          (not (equal (hstate-tm s)
                                      (timed-event-tm (car (hstate-otevs s))))))
                     (and (O u v)
                          (good-aeps-statep v))))
          :hints (("Goal" :cases ((consp (hstate-otevs s)))
                   :use ((:instance rlwfsk2b-l2-empty)
                         (:instance rlwfsk2b-l2-cons))
                   :in-theory (disable hpeps-transf-definition-rule
                                       b-definition-rule
                                       O-definition-rule)))))

 (defthmd rlwfsk2b-lemma
   (let ((u (hpeps-transf s))
         (v (aeps-state (1+ (aeps-state-tm w))
                       (aeps-state-tevs w)
                       (aeps-state-mem w))))
     (implies (and (B s w)
                   (not (equal (hstate-tm s)
                               (timed-event-tm (car (hstate-otevs s))))))
              (and (good-aeps-statep v)
                   (aeps-transp w v)
                   (O u v))))
   :hints (("Goal" 
            :use ((:instance rlwfsk2b-l1)
                  (:instance rlwfsk2b-l2))
            :in-theory (disable hpeps-transf-definition-rule
                                b-definition-rule
                                O-definition-rule))))
 )

(defun-sk lwfsk2a (u w)
  (exists v
    (and (B u v)
         (aeps-transp w v)))
  :witness-dcls ((declare (xargs :guard (and (hstatep u) (aeps-statep w))
                                 :verify-guards nil))))

(verify-guards lwfsk2a)

;; (defun-sk lwfsk2d (u w)
;;   (exists v
;;     (and (O u v)
;;          (aeps-transp w v)))
;;   :witness-dcls ((declare (xargs :guard (and (hstatep u) (aeps-statep w))
;;                                  :verify-guards nil))))

;; (verify-guards lwfsk2d)

(defun-sk rlwfsk2b (u w)
  (exists v
    (and (O u v)
         (aeps-transp w v)))
  :witness-dcls ((declare (xargs :guard (and (hstatep u) (aeps-statep w))
                                 :verify-guards nil))))

(verify-guards rlwfsk2b)

;; 2a holds when s and w have an event is scheduled (both have same
;; otevs) at current time (both s and w have same time) While 2d holds
;; when s and w have no events scheduled at current time.


(defthm R-preserves-good-state
  (implies (good-hstatep s)
           (good-aeps-statep (R s)))
  :rule-classes (:forward-chaining))

(encapsulate
  nil
  
  (local (defthm lwfsk2a=>rlwfsk2b 
           (implies (lwfsk2a u w)
                    (rlwfsk2b u w))
           :hints (("goal" :use  ((:instance lwfsk2a (u u) (w w))
                                  (:instance rlwfsk2b-suff (u u) (w w) 
                                   (v (lwfsk2a-witness u w))))
                           :in-theory (disable (:definition B-definition-rule)
                                               (:definition aeps-state-equal-definition-rule)
                                               (:definition good-aeps-statep-definition-rule)
                                               (:definition good-histp-definition-rule)
                                               (:definition good-hstatep-definition-rule)
                                               (:definition lwfsk2a)
                                               (:definition rlwfsk2b))))))


  (local (defthm B-is-an-LWFSK
           (implies (B s w)
                    (or (lwfsk2a (hpeps-transf s) w)
                        (rlwfsk2b (hpeps-transf s) w)))
           :hints (("Goal" :cases ((not (equal (hstate-tm s)
                                               (timed-event-tm (car (hstate-otevs s)))))))
                   ("Subgoal 2"
                    :use ((:instance lwfsk2a-suff
                           (u (hpeps-transf s))
                           (v (R (hpeps-transf s))))
                          (:instance lwfsk2a-lemma))
                    :in-theory (disable hpeps-transf-definition-rule
                                        good-aeps-statep
                                        b-definition-rule
                                        O-definition-rule
                                        good-aeps-statep-definition-rule
                                        good-hstatep-definition-rule
                                        r-definition-rule
                                        lwfsk2a lwfsk2a-suff
                                        rlwfsk2b rlwfsk2b-suff))
                   ("Subgoal 1"
                    :use ((:instance rlwfsk2b-suff
                           (u (hpeps-transf s))
                           (v (aeps-state (1+ (aeps-state-tm w))
                                          (aeps-state-tevs w)
                                          (aeps-state-mem w))))
                          (:instance rlwfsk2b-lemma))
                    :in-theory (disable hpeps-transf-definition-rule
                                        b-definition-rule
                                        O-definition-rule
                                        good-aeps-statep-definition-rule
                                        good-hstatep-definition-rule
                                        r-definition-rule
                                        lwfsk2a lwfsk2a-suff
                                        rlwfsk2b rlwfsk2b-suff)))
           :rule-classes nil))

  (defthmd B-is-an-RLWFSK
    (implies (B s w)
             (rlwfsk2b (hpeps-transf s) w))
    :hints (("goal" :in-theory (disable B-definition-rule hpeps-transf rlwfsk2b rlwfsk2b-suff
                                        lwfsk2a lwfsk2a-suff)
                    :use ((:instance B-is-an-LWFSK)
                          (:instance lwfsk2a=>rlwfsk2b (u (hpeps-transf s)))))))
  )

(defun-sk lwfsk2f (x y)
  (exists z
    (and (O x z)
         (aeps-transp y z)
         (< (rankls z x) (rankls y x))))
  :witness-dcls ((declare (xargs :guard (and (hstatep x) (aeps-statep y))
                                 :verify-guards nil))))

(verify-guards lwfsk2f)


(defun-sk rlwfsk2c (x y)
  (exists z
    (and (O x z)
         (aeps-transp y z)
         (< (rankls z x) (rankls y x))))
  :witness-dcls ((declare (xargs :guard (and (hstatep x) (aeps-statep y))
                                 :verify-guards nil))))

(verify-guards rlwfsk2c)

(encapsulate
 nil

 (defunc O-witness-y-tm<x-tm (y)
   :input-contract (aeps-statep y)
   :output-contract (aeps-statep (O-witness-y-tm<x-tm y))
   (aeps-state (1+ (aeps-state-tm y))
              (aeps-state-tevs y)
              (aeps-state-mem y)))

 (local (defthm bla
          (implies (and (timep x) (timep y)
                        (< y x))
                   (<= (1+ y) x))))


  (local (defthm valid-lo-tevs-y-x-tm
          (implies (and (good-hstatep x)  
                        (O x y)
                        (< (aeps-state-tm y) (hstate-tm x)))
                   (valid-lo-tevs (aeps-state-tevs y) (hstate-tm x)))))
 
 
 (local (in-theory (disable no-events-at-tm-top-of-queue-2
                            no-events-at-tm-top-of-queue-1)))

 ;; These along with valid-lo-tevs->=-tm are not good rewrite rules
 ;; and often results in significant slow down.
 
 (defthm rlwfsk2c-1
   (let ((z (O-witness-y-tm<x-tm y)))
     (implies (and (O x y)
                   (not (B x y))
                   (< (aeps-state-tm y) (hstate-tm x)))
              (and (O x z)
                   (good-aeps-statep z)
                   (aeps-transp y z)
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
                    (step-events-add (timed-event-ev (car (history-otevs (hstate-h x))))
                                 (timed-event-tm (car (history-otevs (hstate-h x))))
                                 (history-mem (hstate-h x)))
                    (REMOVE-TEVS
                     (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                     (TIMED-EVENT-TM (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                     (HISTORY-MEM (HSTATE-H X)))
                     (CDR (HISTORY-OTEVS (HSTATE-H X)))))
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

;; Proof for (O x (O-witness-y-tm=x-tm x y)) follows
(encapsulate
 nil
 
 (defunc O-witness-y-tm=x-tm (x y)
   :input-contract (and (hstatep x) (aeps-statep y))
   :output-contract (aeps-statep (O-witness-y-tm=x-tm x y))
   (let* ((y-tm (aeps-state-tm y))
          (y-tevs (aeps-state-tevs y))
          (y-mem (aeps-state-mem y))
          (h (hstate-h x))
          (hotevs (history-otevs h)))
     (if (consp hotevs)
         (let* ((tev (car hotevs))
                (ev (timed-event-ev tev))
                (add-tevs (step-events-add ev y-tm y-mem))
                (rm-tevs (step-events-rm ev y-tm y-mem))
                (z-mem (step-memory ev y-tm y-mem))
                (z-tevs (remove-tev tev y-tevs))
                (z-tevs (remove-tevs rm-tevs z-tevs))
                (z-tevs (append add-tevs z-tevs)))
           (aeps-state y-tm z-tevs z-mem))
       (aeps-state (1+ y-tm) y-tevs y-mem))))

;; local added
 (local (in-theory (enable good-histp-definition-rule)))
 (local (in-theory (disable valid-lo-tevs->=-tm 
                     valid-lo-tevs-definition-rule)))

 (local (defthmd rlwfsk2c-aeps-ev-transp
          (implies (and (good-hstatep x)
                        (good-aeps-statep y)
                        (O x y)
                        (not (B x y))
                        (equal (aeps-state-tm y) (hstate-tm x)))
                   (aeps-ev-transp y (O-witness-y-tm=x-tm x y)))
          :hints (("Goal" :in-theory (disable aeps-ev-transp-suff)
                   :use ((:instance aeps-ev-transp-suff
                                    (w y)
                                    (v (O-witness-y-tm=x-tm x y))
                                    (tev (car (history-otevs (hstate-h x))))))))))
 
 (local (defthmd rlwfsk2c-event-at-y-tm
          (implies (and (good-hstatep x)
                        (good-aeps-statep y)
                        (O x y)
                        (not (B x y))
                        (equal (aeps-state-tm y) (hstate-tm x)))
                   (events-at-tm (aeps-state-tevs y) (aeps-state-tm y)))
          :hints (("Goal" :in-theory (disable events-at-tm-l-set-equiv)
                   :use ((:instance events-at-tm-l-set-equiv
                                    (x (history-otevs (hstate-h x)))
                                    (y (aeps-state-tevs y))
                                    (tm (timed-event-tm
                                         (car (history-otevs (hstate-h x)))))))))))
                   
 (defthmd rlwfsk2c-aeps-transp
   (implies (and (O x y)
                 (not (B x y))
                 (equal (aeps-state-tm y) (hstate-tm x)))
            (aeps-transp y (O-witness-y-tm=x-tm x y)))
   :hints (("Goal" :in-theory (e/d (aeps-transp-definition-rule)
                                   (good-hstatep-definition-rule
                                    good-aeps-statep-definition-rule
                                    O-witness-y-tm=x-tm-definition-rule
                                    aeps-state-equal-definition-rule
                                    O-definition-rule
                                    b-definition-rule))
            :use ((:instance rlwfsk2c-event-at-y-tm)
                  (:instance rlwfsk2c-aeps-ev-transp)))))

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
                   (not (events-at-tm (step-events-add ev tm mem) tm)))
          :hints (("Goal" :use ((:instance step-events-add-contract)
                                (:instance no-event-<-tm
                                           (l (step-events-add ev tm mem))
                                           (tm1 tm)
                                           (tm2 (1+ tm))))
                   :in-theory (e/d (timep) (step-events-add-contract
                                            no-event-<-tm))))))

 (local (defthm events-at-tm-remove-tev
          (implies (and (timed-eventp tev) (lo-tep E)
                        (timep tm))
                   (equal (events-at-tm (remove-tev tev E) tm)
                          (remove-tev tev (events-at-tm E tm))))))

 (local (defthm len-remove-tev-<=
          (implies (and (timed-eventp tev) (timep tm)
                        (lo-tep E))
                   (<= (len (remove-tev tev E))
                       (len E)))
          :rule-classes (:rewrite :linear)))

 (local (defthm l1
          (implies (and (lo-tep E) (lo-tep r) (timep tm) (timed-eventp tev))
                   (<= (len (events-at-tm (remove-tev  tev (remove-tevs r E)) tm))
                       (len (events-at-tm (remove-tevs r E) tm))))
          :hints (("goal" :do-not-induct t
                   :in-theory (disable remove-tevs-definition-rule events-at-tm-definition-rule)))
          :rule-classes (:rewrite :linear)))

 
 (local (defthm remove-tev-non-increasing-events-at-tm
          (implies (and (lo-tep l) (timep tm) (timed-eventp tev))
                   (<= (len (events-at-tm (remove-tev tev l) tm))
                       (len (events-at-tm l tm))))
          :hints (("Goal" :in-theory (enable events-at-tm-definition-rule)))
          :rule-classes :linear))

 (local (defthm l2
          (implies (and (lo-tep E) (lo-tep r) (timep tm))
                   (<= (len (events-at-tm (remove-tevs r E) tm))
                       (len (events-at-tm E tm))))
          :hints (("Goal" :in-theory (disable EVENTS-AT-TM-L-SET-EQUIV)))
          :rule-classes (:rewrite :linear)))


 (local (defthm l3
          (implies (and (timed-eventp tev) (timep tm)
                        (lo-tep E)
                        (member-equal tev E))
                   (< (len (remove-tev tev E))
                      (len E)))
          :rule-classes (:rewrite :linear)))

 (local (defthm l3-1
          (implies (and (timed-eventp tev) (timep tm)
                        (lo-tep r) (lo-tep l2) (memoryp mem))
                   (equal (len (events-at-tm (append (step-events-add (timed-event-ev tev)
                                                                      tm mem)
                                                     (remove-tevs r (remove-tev tev l2)))
                                             tm))
                          (len (events-at-tm (remove-tevs r (remove-tev tev l2)) tm))))
          :hints (("Goal" :in-theory (disable EVENTS-AT-TM-L-SET-EQUIV)))
          :rule-classes (:rewrite :linear)))

 (local (defthm l3-2
          (implies (and (timed-eventp tev) (timep tm)
                        (lo-tep l2) (memoryp mem)
                        (lo-tep r)
                        (member-equal tev (events-at-tm l2 tm)))
                   (< (len (events-at-tm (append (step-events-add (timed-event-ev tev)
                                                                  tm mem)
                                                 (remove-tevs r (remove-tev tev l2)))
                                         tm))
                      (len (events-at-tm l2 tm))))
          :hints (("Goal" :in-theory (disable EVENTS-AT-TM-L-SET-EQUIV)))
          :rule-classes (:rewrite :linear)))

 (local (defthm l3a
          (implies (and (lo-tep l) (consp l))
                   (member-equal (car l) (events-at-tm l (timed-event-tm (car l)))))
          :hints (("Goal" :in-theory (disable events-at-tm-l-set-equiv)))))


 (local (defthm l3b
          (implies (and (lo-tep l2) (memoryp mem) (consp l2)
                        (lo-tep r))
                   (< (len (events-at-tm (append (step-events-add (timed-event-ev (car l2))
                                                                  (timed-event-tm (car l2)) mem)
                                                 (remove-tevs r (remove-tev (car l2) l2)))
                                         (timed-event-tm (car l2))))
                      (len (events-at-tm l2 (timed-event-tm (car l2))))))
          :hints (("Goal" :in-theory (disable EVENTS-AT-TM-L-SET-EQUIV)))
          :rule-classes (:rewrite :linear)))        

 (local (defthm l3c
          (implies (and (good-hstatep x)
                        (good-aeps-statep y)
                        (O x y)
                        (not (B x y))
                        (equal (aeps-state-tm y) (hstate-tm x)))
                   (member-equal (car (history-otevs (hstate-h x)))
                                 (events-at-tm (aeps-state-tevs y)
                                               (aeps-state-tm y))))
          :hints (("Goal" :in-theory (disable events-at-tm-l-set-equiv
                                              b-definition-rule
                                              good-aeps-statep-definition-rule
                                              good-hstatep-definition-rule)
                   :use ((:instance events-at-tm-l-set-equiv
                                    (y (history-otevs (hstate-h x)))
                                    (x (aeps-state-tevs y))
                                    (tm (aeps-state-tm y)))
                         (:instance history-tevs-car)
                         (:instance l3a (l (history-otevs (hstate-h x)))))))))

 (defthmd l4
   (implies (and (O x y)
                 (not (B x y))
                 (equal (aeps-state-tm y) (hstate-tm x)))
            (< (rankls (O-witness-y-tm=x-tm x y) x)
               (rankls y x)))
   :hints (("Goal" :in-theory (disable l3b l3c
                                       events-at-tm-l-set-equiv
                                       b-definition-rule history
                                       historyp  history-tevs-car
                                       events-at-tm-definition-rule)
            :use ((:instance l3c)
                  (:instance l3-2
                             (tev (car (history-otevs (hstate-h x))))
                             (tm (timed-event-tm (car (history-otevs (hstate-h x)))))
                             (l2 (AEPS-STATE-TEVS Y))
                             (mem (AEPS-STATE-MEM Y))
                             (r (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                                (AEPS-STATE-TM Y)
                                                (AEPS-STATE-MEM Y))))
                  (:instance l3b
                             (l2 (AEPS-STATE-TEVS Y))
                             (mem (AEPS-STATE-MEM Y))
                             (r (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                                (AEPS-STATE-TM Y)
                                                (AEPS-STATE-MEM Y))))
                  (:instance history-tevs-car)))))
 )

                  
(encapsulate
 nil
 ;;todo takes long time to admit 20s

 (local (defthm remove-tev-valid-1
          (implies (and (o-lo-tep l) (timep tm) (consp l)
                        (valid-lo-tevs l tm))
                   (valid-lo-tevs (remove-tev (car l) l) tm))
          :hints (("Goal" :in-theory (enable valid-lo-tevs-definition-rule)))))

 (local (defthm remove-tev-valid-2
          (implies (and (o-lo-tep l) (timep tm) (consp l)
                        (lo-tep l-equiv)
                        (set-equiv l l-equiv)
                        (valid-lo-tevs l tm))
                   (valid-lo-tevs (remove-tev (car l) l-equiv) tm))
          :hints (("Goal" :use ((:instance remove-tev-valid-1)
                                (:instance remove-tev-preserves-set-equiv
                                           (x l) (y l-equiv)
                                           (tev (car l)))
                                (:instance valid-lo-tevs-setequiv
                                           (l2 (remove-tev (car l) l))
                                           (l1 (remove-tev (car l) l-equiv))
                                           (tm tm)))
                   :in-theory (disable valid-lo-tevs-setequiv
                                       remove-tev-valid-1)
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

 (defthm valid-lo-tevs-distributes-over-append
  (implies (and (lo-tep l1) (lo-tep l2)
                        (timep tm))
           (equal (valid-lo-tevs (append l1 l2) tm)
                  (and (valid-lo-tevs l1 tm)
                       (valid-lo-tevs l2 tm))))
  :hints (("Goal" :in-theory (e/d (valid-lo-tevs-definition-rule)
                                  (timed-event eventp)))))

 ;; (local (defthm remove-tev-valid-1-general
 ;;          (implies (and (lo-tep l) (timep tm) (timed-eventp tev)
 ;;                        (valid-lo-tevs l tm))
 ;;                   (valid-lo-tevs (remove-tev tev l) tm))
 ;;          :hints (("Goal" :in-theory (enable valid-lo-tevs-definition-rule)))))

 ;; (local (defthm remove-tevs-valid-lo-tevs
 ;;          (implies (and (lo-tep l) (timep tm) (lo-tep l1)
 ;;                        (valid-lo-tevs l tm))
 ;;                   (valid-lo-tevs (remove-tevs l1 l) tm))
 ;;          :hints (("Goal" :in-theory (enable valid-lo-tevs-definition-rule)))))

 (local (defthm lemma-1
          (implies (and (lo-tep l1) (timep tm) (consp l2)
                        (o-lo-tep l2)
                        (lo-tep l2-equiv)
                        (set-equiv l2 l2-equiv)
                        (valid-lo-tevs l1 (1+ tm))
                        (valid-lo-tevs l2 tm))
                   (valid-lo-tevs (append l1 (remove-tev  (car l2) l2-equiv)) tm))
          :hints (("Goal" :use ((:instance valid-lo-tevs->=-tm
                                           (E l1) (t1 (1+ tm))
                                           (t2 tm)))
                   :do-not-induct t
                   :in-theory (disable remove-tev-o-lo-tep timep
                                       valid-lo-tevs-o-lo-tep
                                       o-lo-tep-definition-rule
                                       lo-tep
                                       valid-lo-tevs-definition-rule
                                       remove-tev-definition-rule
                                       timed-event
                                       valid-lo-tevs-append)))))
 (local (defthmd rlwfsk2c-O-1
          (implies (and (good-hstatep x)
                        (good-aeps-statep y)
                        (O x y)
                        (not (B x y))
                        (equal (aeps-state-tm y) (hstate-tm x)))
                   (good-aeps-statep (O-witness-y-tm=x-tm x y)))
          :hints (("Goal" :in-theory (disable remove-tev-o-lo-tep
                                              valid-lo-tevs-o-lo-tep
                                              o-lo-tep-definition-rule
                                              lo-tep
                                              valid-lo-tevs-definition-rule
                                              remove-tev-definition-rule
                                              timed-event))
                  ("subgoal 4.4" :use ((:instance valid-lo-tevs->=-tm
                                                  (e (step-events-add (timed-event-ev (car (history-otevs (hstate-h x))))
                                                                      (aeps-state-tm y)
                                                                      (aeps-state-mem y)))
                                                  (t1 (1+ (aeps-state-tm y)))
                                                  (t2 (aeps-state-tm y))))
                   :in-theory (disable (:rewrite valid-lo-tevs->=-tm)))
                  ("subgoal 4.3" :in-theory (disable remove-tev-valid-1-general
                                                     remove-tevs-valid-lo-tevs)
                   :use ((:instance remove-tev-valid-1-general
                                    (l (aeps-state-tevs y))
                                    (tm (aeps-state-tm y))
                                    (tev (CAR (HISTORY-OTEVS (HSTATE-H X)))))
                         (:instance remove-tevs-valid-lo-tevs
                                    (l (remove-tev (car (history-otevs (hstate-h x)))
                                                   (aeps-state-tevs y)))
                                    (l1 (step-events-rm (timed-event-ev (car (history-otevs (hstate-h x))))
                                                        (aeps-state-tm y)
                                                        (aeps-state-mem y)))
                                    (tm (aeps-state-tm y)))))
                  ("subgoal 4.2" :use ((:instance valid-lo-tevs->=-tm
                                                  (e (step-events-add (timed-event-ev (car (history-otevs (hstate-h x))))
                                                                      (aeps-state-tm y)
                                                                      (aeps-state-mem y)))
                                                  (t1 (1+ (aeps-state-tm y)))
                                                  (t2 (aeps-state-tm y)))))
                  ("subgoal 4.1" :use ((:instance valid-lo-tevs->=-tm
                                                  (e (step-events-add (timed-event-ev (car (history-otevs (hstate-h x))))
                                                                      (aeps-state-tm y)
                                                                      (aeps-state-mem y)))
                                                  (t1 (1+ (aeps-state-tm y)))
                                                  (t2 (aeps-state-tm y)))))
                  ("subgoal 2.2" :use ((:instance valid-lo-tevs->=-tm
                                                  (e (step-events-add (timed-event-ev (car (history-otevs (hstate-h x))))
                                                                      (aeps-state-tm y)
                                                                      (aeps-state-mem y)))
                                                  (t1 (1+ (aeps-state-tm y)))
                                                  (t2 (aeps-state-tm y)))))
                  ("subgoal 2.1" :use ((:instance valid-lo-tevs->=-tm
                                                  (e (step-events-add (timed-event-ev (car (history-otevs (hstate-h x))))
                                                                      (aeps-state-tm y)
                                                                      (aeps-state-mem y)))
                                                  (t1 (1+ (aeps-state-tm y)))
                                                  (t2 (aeps-state-tm y))))
                   :in-theory (disable (:rewrite valid-lo-tevs->=-tm))))))

 (in-theory (disable  acl2::commutativity-of-append-under-set-equiv))

 (local (in-theory (disable hstate-equal-definition-rule
                     (:congruence acl2::set-equiv-implies-equal-consp-1))))

 (local (defthm c3
          (implies (and (good-hstatep x)
                        (good-aeps-statep y)
                        (O x y)
                        (not (B x y))
                        (equal (aeps-state-tm y) (hstate-tm x)))
                   (equal (aeps-state-tm (R x)) (aeps-state-tm (O-witness-y-tm=x-tm x y))))))

 (local (defthm foo-1
          (IMPLIES
           (AND
            (EQUAL (TIMED-EVENT-TM (CAR (HISTORY-OTEVS (HSTATE-H X))))
                   (AEPS-STATE-TM Y))
            (HSTATEP X)
            (VALID-LO-TEVS (HSTATE-OTEVS X)
                           (AEPS-STATE-TM Y))
            (HISTORY-OTEVS (HSTATE-H X))
            (HSTATE-EQUAL
             (HSTATE
              (AEPS-STATE-TM Y)
              (INSERT-OTEVS
               (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                            (AEPS-STATE-TM Y)
                            (HISTORY-MEM (HSTATE-H X)))
               (CDR (HISTORY-OTEVS (HSTATE-H X))))
              (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                           (AEPS-STATE-TM Y)
                           (HISTORY-MEM (HSTATE-H X)))
              (HISTORY T (HISTORY-TM (HSTATE-H X))
                       (HISTORY-OTEVS (HSTATE-H X))
                       (HISTORY-MEM (HSTATE-H X))))
             X)
            (AEPS-STATEP Y)
            (VALID-LO-TEVS (AEPS-STATE-TEVS Y)
                           (AEPS-STATE-TM Y))
            (HISTORY-VALID (HSTATE-H X))
            (SET-EQUIV (AEPS-STATE-TEVS Y)
                       (HISTORY-OTEVS (HSTATE-H X)))
            (SET-EQUIV (AEPS-STATE-MEM Y)
                       (HISTORY-MEM (HSTATE-H X)))
            (NOT (EQUAL (AEPS-STATE (AEPS-STATE-TM Y)
                                   (HSTATE-OTEVS X)
                                   (HSTATE-MEM X))
                        Y))
            (NOT (SET-EQUIV (AEPS-STATE-MEM Y)
                            (HSTATE-MEM X)))
            (EQUAL (AEPS-STATE-TM Y) (HSTATE-TM X))
            (SET-EQUIV (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                    (AEPS-STATE-TM Y)
                                    (AEPS-STATE-MEM Y))
                       (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                    (AEPS-STATE-TM Y)
                                    (HISTORY-MEM (HSTATE-H X)))))
           (SET-EQUIV
            (HSTATE-OTEVS X)
            (APPEND (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                 (AEPS-STATE-TM Y)
                                 (HISTORY-MEM (HSTATE-H X)))
                    (CDR (HISTORY-OTEVS (HSTATE-H X))))))
          :INSTRUCTIONS
          (:PROMOTE
           :EXPAND (:DV 1)
           (:EQUIV
            X
            (HSTATE
             (AEPS-STATE-TM Y)
             (INSERT-OTEVS
              (STEP-EVENTS-ADD
               (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
               (AEPS-STATE-TM Y)
               (HISTORY-MEM (HSTATE-H X)))
              (CDR (HISTORY-OTEVS (HSTATE-H X))))
             (STEP-MEMORY
              (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
              (AEPS-STATE-TM Y)
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

 (local (defthm p1
          (implies (and (HSTATEP X) (AEPS-STATEP Y)
                        (SET-EQUIV (AEPS-STATE-TEVS Y)
                                   (HISTORY-OTEVS (HSTATE-H X)))
                        (HISTORY-OTEVS (HSTATE-H X)))
                   (set-equiv (REMOVE-TEV (CAR (HISTORY-OTEVS (HSTATE-H X)))
                                          (AEPS-STATE-TEVS Y))
                              (remove-tev (CAR (HISTORY-OTEVS (HSTATE-H X)))
                                          (HISTORY-OTEVS (HSTATE-H X)))))
          :hints (("goal" :use (:instance remove-tev-preserves-set-equiv
                                          (x (AEPS-STATE-TEVS Y))
                                          (y (HISTORY-OTEVS (HSTATE-H X)))
                                          (tev (CAR (HISTORY-OTEVS (HSTATE-H X)))))))))

 (local (defthm p2
          (implies (and (HSTATEP X) (AEPS-STATEP Y)
                        (SET-EQUIV (AEPS-STATE-TEVS Y)
                                   (HISTORY-OTEVS (HSTATE-H X)))
                        (HISTORY-OTEVS (HSTATE-H X)))
                   (set-equiv (REMOVE-TEV (CAR (HISTORY-OTEVS (HSTATE-H X)))
                                          (AEPS-STATE-TEVS Y))
                              (cdr (HISTORY-OTEVS (HSTATE-H X)))))))

 (local (defthmd p3
          (implies (and (lo-tep r)
                        (o-lo-tep x)
                        x (lo-tep y)
                        (set-equiv x y))
                   (set-equiv  (remove-tevs r (cdr x))
                               (remove-tevs r (remove-tev (car x) y))))
          :hints (("goal" :do-not-induct t
                   :use ((:instance remove-tev-preserves-set-equiv
                                    (x y) (y x)
                                    (tev (car x)))
                         (:instance remove-tev-o-lo-tep (x x))
                         (:instance remove-tevs-l-equiv-is-set-equiv-1
                                    (l (cdr x))
                                    (l-equiv (remove-tev (car x) y))
                                    (tevs r)))
                   :in-theory (disable remove-tev-definition-rule
                                       remove-tev-o-lo-tep
                                       remove-tev-preserves-set-equiv
                                       remove-tevs-l-equiv-is-set-equiv)))))
 

 (local (defthmd p4
          (implies (and (lo-tep r1)
                        (lo-tep r2)
                        (o-lo-tep x)
                        x (lo-tep y)
                        (set-equiv x y)
                        (set-equiv r1 r2))
                   (set-equiv  (remove-tevs r1 (cdr x))
                               (remove-tevs r2 (remove-tev (car x) y))))
          :hints (("goal" :do-not-induct t
                   :use ((:instance remove-tevs-l-equiv-is-set-equiv
                                    (l r1)
                                    (l-equiv r2)
                                    (tevs (remove-tev (car x) y)))
                         (:instance p3 (r r1)))
                   :in-theory (disable p3
                                       remove-tev-definition-rule
                                       remove-tev-o-lo-tep
                                       remove-tev-preserves-set-equiv
                                       remove-tevs-l-equiv-is-set-equiv
                                       remove-tevs-l-equiv-is-set-equiv-1)))))

 (local (defthm p5
          (implies (and (HSTATEP X) (AEPS-STATEP Y)
                        (SET-EQUIV (AEPS-STATE-TEVS Y)
                                   (HISTORY-OTEVS (HSTATE-H X)))
                        (SET-EQUIV (AEPS-STATE-MEM Y)
                                   (HISTORY-MEM (HSTATE-H X)))
                        (HISTORY-OTEVS (HSTATE-H X)))
                   (set-equiv
                    (remove-tevs
                     (step-events-rm (timed-event-ev (car (history-otevs (hstate-h x))))
                                     (aeps-state-tm y)
                                     (history-mem (hstate-h x)))
                     (cdr (history-otevs (hstate-h x))))
                    (remove-tevs
                     (step-events-rm (timed-event-ev (car (history-otevs (hstate-h x))))
                                     (aeps-state-tm y)
                                     (aeps-state-mem y))
                     (remove-tev (car (history-otevs (hstate-h x)))
                                 (aeps-state-tevs y)))))
          :hints (("goal" :use ((:instance step-events-rm-congruence
                                           (ev (timed-event-ev (car (history-otevs (hstate-h x)))))
                                           (tm (aeps-state-tm y))
                                           (mem (history-mem (hstate-h x)))
                                           (mem-equiv (aeps-state-mem y)))
                                (:instance p4
                                           (x (HISTORY-OTEVS (HSTATE-H X)))
                                           (r1 (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                                               (AEPS-STATE-TM Y)
                                                               (HISTORY-MEM (HSTATE-H X))))
                                           (r2 (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                                               (AEPS-STATE-TM Y)
                                                               (AEPS-STATE-MEM Y)))
                                           (y (AEPS-STATE-TEVS Y))))))))
 

 (local (in-theory (disable p1 p2 p3 p4 p5)))

 (local (defthm foo-2a
          (IMPLIES
           (AND
            (EQUAL (TIMED-EVENT-TM (CAR (HISTORY-OTEVS (HSTATE-H X))))
                   (AEPS-STATE-TM Y))
            (SET-EQUIV
             (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                              (AEPS-STATE-TM Y)
                              (AEPS-STATE-MEM Y))
             (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                              (AEPS-STATE-TM Y)
                              (HISTORY-MEM (HSTATE-H X))))
            (SET-EQUIV
             (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                             (AEPS-STATE-TM Y)
                             (AEPS-STATE-MEM Y))
             (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                             (AEPS-STATE-TM Y)
                             (HISTORY-MEM (HSTATE-H X))))
            (HSTATEP X)
            (VALID-LO-TEVS (HSTATE-OTEVS X)
                           (AEPS-STATE-TM Y))
            (HISTORY-OTEVS (HSTATE-H X))
            (HSTATE-EQUAL
             (HSTATE
              (AEPS-STATE-TM Y)
              (INSERT-OTEVS
               (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                (AEPS-STATE-TM Y)
                                (HISTORY-MEM (HSTATE-H X)))
               (REMOVE-TEVS
                (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                (AEPS-STATE-TM Y)
                                (HISTORY-MEM (HSTATE-H X)))
                (CDR (HISTORY-OTEVS (HSTATE-H X)))))
              (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                           (AEPS-STATE-TM Y)
                           (HISTORY-MEM (HSTATE-H X)))
              (HISTORY T (HISTORY-TM (HSTATE-H X))
                       (HISTORY-OTEVS (HSTATE-H X))
                       (HISTORY-MEM (HSTATE-H X))))
             X)
            (VALID-LO-TEVS (HISTORY-OTEVS (HSTATE-H X))
                           (AEPS-STATE-TM Y))
            (AEPS-STATEP Y)
            (VALID-LO-TEVS (AEPS-STATE-TEVS Y)
                           (AEPS-STATE-TM Y))
            (HISTORY-VALID (HSTATE-H X))
            (SET-EQUIV (AEPS-STATE-TEVS Y)
                       (HISTORY-OTEVS (HSTATE-H X)))
            (SET-EQUIV (AEPS-STATE-MEM Y)
                       (HISTORY-MEM (HSTATE-H X)))
            (NOT (EQUAL (AEPS-STATE (AEPS-STATE-TM Y)
                                   (HSTATE-OTEVS X)
                                   (HSTATE-MEM X))
                        Y))
            (NOT (SET-EQUIV (AEPS-STATE-MEM Y)
                            (HSTATE-MEM X)))
            (EQUAL (AEPS-STATE-TM Y) (HSTATE-TM X)))
           (SET-EQUIV
            (HSTATE-OTEVS X)
            (APPEND
             (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                              (AEPS-STATE-TM Y)
                              (AEPS-STATE-MEM Y))
             (REMOVE-TEVS
              (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                              (AEPS-STATE-TM Y)
                              (AEPS-STATE-MEM Y))
              (REMOVE-TEV (CAR (HISTORY-OTEVS (HSTATE-H X)))
                          (AEPS-STATE-TEVS Y))))))
          :INSTRUCTIONS
          (:PROMOTE
           :EXPAND (:DV 1)
           (:EQUIV
            X
            (HSTATE
             (AEPS-STATE-TM Y)
             (INSERT-OTEVS
              (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                               (AEPS-STATE-TM Y)
                               (HISTORY-MEM (HSTATE-H X)))
              (REMOVE-TEVS
               (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                               (AEPS-STATE-TM Y)
                               (HISTORY-MEM (HSTATE-H X)))
               (CDR (HISTORY-OTEVS (HSTATE-H X)))))
             (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                          (AEPS-STATE-TM Y)
                          (HISTORY-MEM (HSTATE-H X)))
             (HISTORY T (HISTORY-TM (HSTATE-H X))
                      (HISTORY-OTEVS (HSTATE-H X))
                      (HISTORY-MEM (HSTATE-H X))))
            HSTATE-EQUAL)
           (:REWRITE HSTATE-CONSTRUCTOR-DESTRUCTORS-PROPER)
           (:REWRITE APPEND-SETEQUIV-INSERT-TEVS)
           :UP
           (:DV 1 2)
           (:REWRITE P5)
           :UP
           :UP
           (:DV 1 1)
           (:REWRITE STEP-EVENTS-ADD-CONGRUENCE
                     ((MEM-EQUIV (AEPS-STATE-MEM Y))))
           :UP
           :UP
           :BASH
           :BASH
           :BASH
           :BASH
           :BASH
           :BASH
           :BASH
           :BASH
           :BASH)))

 (local (defthm foo-2b
          (IMPLIES
           (AND
            (EQUAL (TIMED-EVENT-TM (CAR (HISTORY-OTEVS (HSTATE-H X))))
                   (AEPS-STATE-TM Y))
            (SET-EQUIV
             (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                              (AEPS-STATE-TM Y)
                              (AEPS-STATE-MEM Y))
             (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                              (AEPS-STATE-TM Y)
                              (HISTORY-MEM (HSTATE-H X))))
            (SET-EQUIV
             (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                             (AEPS-STATE-TM Y)
                             (AEPS-STATE-MEM Y))
             (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                             (AEPS-STATE-TM Y)
                             (HISTORY-MEM (HSTATE-H X))))
            (HSTATEP X)
            (VALID-LO-TEVS (HSTATE-OTEVS X)
                           (AEPS-STATE-TM Y))
            (HISTORY-OTEVS (HSTATE-H X))
            (HSTATE-EQUAL
             (HSTATE
              (AEPS-STATE-TM Y)
              (INSERT-OTEVS
               (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                (AEPS-STATE-TM Y)
                                (HISTORY-MEM (HSTATE-H X)))
               (REMOVE-TEVS
                (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                (AEPS-STATE-TM Y)
                                (HISTORY-MEM (HSTATE-H X)))
                (CDR (HISTORY-OTEVS (HSTATE-H X)))))
              (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                           (AEPS-STATE-TM Y)
                           (HISTORY-MEM (HSTATE-H X)))
              (HISTORY T (HISTORY-TM (HSTATE-H X))
                       (HISTORY-OTEVS (HSTATE-H X))
                       (HISTORY-MEM (HSTATE-H X))))
             X)
            (AEPS-STATEP Y)
            (VALID-LO-TEVS (AEPS-STATE-TEVS Y)
                           (AEPS-STATE-TM Y))
            (HISTORY-VALID (HSTATE-H X))
            (SET-EQUIV (AEPS-STATE-TEVS Y)
                       (HISTORY-OTEVS (HSTATE-H X)))
            (SET-EQUIV (AEPS-STATE-MEM Y)
                       (HISTORY-MEM (HSTATE-H X)))
            (NOT (EQUAL (AEPS-STATE (AEPS-STATE-TM Y)
                                   (HSTATE-OTEVS X)
                                   (HSTATE-MEM X))
                        Y))
            (NOT (SET-EQUIV (AEPS-STATE-TEVS Y)
                            (HSTATE-OTEVS X)))
            (EQUAL (AEPS-STATE-TM Y) (HSTATE-TM X)))
           (SET-EQUIV
            (HSTATE-OTEVS X)
            (APPEND
             (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                              (AEPS-STATE-TM Y)
                              (AEPS-STATE-MEM Y))
             (REMOVE-TEVS
              (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                              (AEPS-STATE-TM Y)
                              (AEPS-STATE-MEM Y))
              (CDR (HISTORY-OTEVS (HSTATE-H X)))))))
          :INSTRUCTIONS
          (:PROMOTE
           :EXPAND (:DV 1)
           (:EQUIV
            X
            (HSTATE
             (AEPS-STATE-TM Y)
             (INSERT-OTEVS
              (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                               (AEPS-STATE-TM Y)
                               (HISTORY-MEM (HSTATE-H X)))
              (REMOVE-TEVS
               (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                               (AEPS-STATE-TM Y)
                               (HISTORY-MEM (HSTATE-H X)))
               (CDR (HISTORY-OTEVS (HSTATE-H X)))))
             (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                          (AEPS-STATE-TM Y)
                          (HISTORY-MEM (HSTATE-H X)))
             (HISTORY T (HISTORY-TM (HSTATE-H X))
                      (HISTORY-OTEVS (HSTATE-H X))
                      (HISTORY-MEM (HSTATE-H X))))
            HSTATE-EQUAL)
           (:REWRITE HSTATE-CONSTRUCTOR-DESTRUCTORS-PROPER)
           (:REWRITE APPEND-SETEQUIV-INSERT-TEVS)
           :UP
           (:DV 1 2)
           (:REWRITE P5)
           :UP
           :UP
           (:DV 1 1)
           (:REWRITE STEP-EVENTS-ADD-CONGRUENCE
                     ((MEM-EQUIV (AEPS-STATE-MEM Y))))
           :UP
           :UP
           :BASH
           :BASH
           :BASH
           :BASH
           :BASH
           :BASH
           :BASH
           :BASH
           :BASH)))


 ;;todo

 (local (defthm c2
          (implies (and (good-hstatep x)
                        (good-aeps-statep y)
                        (O x y)
                        (not (B x y))
                        (equal (aeps-state-tm y) (hstate-tm x)))
                   (set-equiv (aeps-state-tevs (R x))
                              (aeps-state-tevs (O-witness-y-tm=x-tm x y))))
          :hints (("goal" :in-theory (disable history-tevs-car)
                   :use ((:instance history-tevs-car)
                         (:instance step-events-add-congruence
                                    (ev (timed-event-ev (car (history-otevs (hstate-h x)))))
                                    (tm (aeps-state-tm y))
                                    (mem (aeps-state-mem y))
                                    (mem-equiv (history-mem (hstate-h x))))
                         (:instance step-events-rm-congruence
                                    (ev (timed-event-ev (car (history-otevs (hstate-h x)))))
                                    (tm (aeps-state-tm y))
                                    (mem (aeps-state-mem y))
                                    (mem-equiv (history-mem (hstate-h x)))))
                   :do-not '(eliminate-destructors)))))
 

 (local (defthm foo-3
          (IMPLIES
           (AND
            (EQUAL (TIMED-EVENT-TM (CAR (HISTORY-OTEVS (HSTATE-H X))))
                   (AEPS-STATE-TM Y))
            (SET-EQUIV (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                    (AEPS-STATE-TM Y)
                                    (AEPS-STATE-MEM Y))
                       (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                    (AEPS-STATE-TM Y)
                                    (HISTORY-MEM (HSTATE-H X))))
            (HSTATEP X)
            (VALID-LO-TEVS (HSTATE-OTEVS X)
                           (AEPS-STATE-TM Y))
            (HISTORY-OTEVS (HSTATE-H X))
            (HSTATE-EQUAL
             (HSTATE
              (AEPS-STATE-TM Y)
              (INSERT-OTEVS
               (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                (AEPS-STATE-TM Y)
                                (HISTORY-MEM (HSTATE-H X)))
               (REMOVE-TEVS
                (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                (AEPS-STATE-TM Y)
                                (HISTORY-MEM (HSTATE-H X)))
                (CDR (HISTORY-OTEVS (HSTATE-H X)))))
              (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                           (AEPS-STATE-TM Y)
                           (HISTORY-MEM (HSTATE-H X)))
              (HISTORY T (HISTORY-TM (HSTATE-H X))
                       (HISTORY-OTEVS (HSTATE-H X))
                       (HISTORY-MEM (HSTATE-H X))))
             X)
            (AEPS-STATEP Y)
            (VALID-LO-TEVS (AEPS-STATE-TEVS Y)
                           (AEPS-STATE-TM Y))
            (HISTORY-VALID (HSTATE-H X))
            (SET-EQUIV (AEPS-STATE-TEVS Y)
                       (HISTORY-OTEVS (HSTATE-H X)))
            (SET-EQUIV (AEPS-STATE-MEM Y)
                       (HISTORY-MEM (HSTATE-H X)))
            (NOT (EQUAL (AEPS-STATE (AEPS-STATE-TM Y)
                                   (HSTATE-OTEVS X)
                                   (HSTATE-MEM X))
                        Y))
            (NOT (SET-EQUIV (AEPS-STATE-MEM Y)
                            (HSTATE-MEM X)))
            (EQUAL (AEPS-STATE-TM Y) (HSTATE-TM X)))
           (SET-EQUIV (HSTATE-MEM X)
                      (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                   (AEPS-STATE-TM Y)
                                   (AEPS-STATE-MEM Y))))
          :INSTRUCTIONS
          (:PROMOTE
           :EXPAND (:DV 1)
           (:EQUIV
            X
            (HSTATE
             (AEPS-STATE-TM Y)
             (INSERT-OTEVS
              (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                               (AEPS-STATE-TM Y)
                               (HISTORY-MEM (HSTATE-H X)))
              (REMOVE-TEVS
               (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                               (AEPS-STATE-TM Y)
                               (HISTORY-MEM (HSTATE-H X)))
               (CDR (HISTORY-OTEVS (HSTATE-H X)))))
             (STEP-MEMORY
              (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
              (AEPS-STATE-TM Y)
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
                   (AEPS-STATE-TM Y))
            (SET-EQUIV (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                    (AEPS-STATE-TM Y)
                                    (AEPS-STATE-MEM Y))
                       (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                    (AEPS-STATE-TM Y)
                                    (HISTORY-MEM (HSTATE-H X))))
            (HSTATEP X)
            (VALID-LO-TEVS (HSTATE-OTEVS X)
                           (AEPS-STATE-TM Y))
            (HISTORY-OTEVS (HSTATE-H X))
            (HSTATE-EQUAL
             (HSTATE
              (AEPS-STATE-TM Y)
              (INSERT-OTEVS
              (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                               (AEPS-STATE-TM Y)
                               (HISTORY-MEM (HSTATE-H X)))
              (REMOVE-TEVS
               (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                               (AEPS-STATE-TM Y)
                               (HISTORY-MEM (HSTATE-H X)))
               (CDR (HISTORY-OTEVS (HSTATE-H X)))))
              (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                           (AEPS-STATE-TM Y)
                           (HISTORY-MEM (HSTATE-H X)))
              (HISTORY T (HISTORY-TM (HSTATE-H X))
                       (HISTORY-OTEVS (HSTATE-H X))
                       (HISTORY-MEM (HSTATE-H X))))
             X)
            (AEPS-STATEP Y)
            (VALID-LO-TEVS (AEPS-STATE-TEVS Y)
                           (AEPS-STATE-TM Y))
            (HISTORY-VALID (HSTATE-H X))
            (SET-EQUIV (AEPS-STATE-TEVS Y)
                       (HISTORY-OTEVS (HSTATE-H X)))
            (SET-EQUIV (AEPS-STATE-MEM Y)
                       (HISTORY-MEM (HSTATE-H X)))
            (NOT (EQUAL (AEPS-STATE (AEPS-STATE-TM Y)
                                   (HSTATE-OTEVS X)
                                   (HSTATE-MEM X))
                        Y))
            (NOT (SET-EQUIV (AEPS-STATE-TEVS Y)
                            (HSTATE-OTEVS X)))
            (EQUAL (AEPS-STATE-TM Y) (HSTATE-TM X)))
           (SET-EQUIV (HSTATE-MEM X)
                      (STEP-MEMORY (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                                   (AEPS-STATE-TM Y)
                                   (AEPS-STATE-MEM Y))))
          :INSTRUCTIONS
          (:PROMOTE
           :EXPAND (:DV 1)
           (:EQUIV
            X
            (HSTATE
             (AEPS-STATE-TM Y)
             (INSERT-OTEVS
              (STEP-EVENTS-ADD (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                               (AEPS-STATE-TM Y)
                               (HISTORY-MEM (HSTATE-H X)))
              (REMOVE-TEVS
               (STEP-EVENTS-RM (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
                               (AEPS-STATE-TM Y)
                               (HISTORY-MEM (HSTATE-H X)))
               (CDR (HISTORY-OTEVS (HSTATE-H X)))))
             (STEP-MEMORY
              (TIMED-EVENT-EV (CAR (HISTORY-OTEVS (HSTATE-H X))))
              (AEPS-STATE-TM Y)
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
                        (good-aeps-statep y)
                        (O x y)
                        (not (B x y))
                        (equal (aeps-state-tm y) (hstate-tm x)))
                   (set-equiv (aeps-state-mem (O-witness-y-tm=x-tm x y))
                              (aeps-state-mem (r x))))
          :hints (("goal" :in-theory (disable history-tevs-car)
                   :use ((:instance history-tevs-car)
                         (:instance step-memory-congruence
                                    (ev (timed-event-ev (car (history-otevs (hstate-h x)))))
                                    (tm (aeps-state-tm y))
                                    (mem (aeps-state-mem y))
                                    (mem-equiv (history-mem (hstate-h x)))))
                   :do-not '(eliminate-destructors)))))

 (local (defthm rlwfsk2c-O-2
          (implies (and (good-hstatep x)
                        (good-aeps-statep y)
                        (O x y)
                        (not (B x y))
                        (equal (aeps-state-tm y) (hstate-tm x)))
                   (aeps-state-equal (R x) (O-witness-y-tm=x-tm x y)))
          :hints (("Goal" :in-theory (disable
                                      good-aeps-statep-definition-rule
                                      good-hstatep-definition-rule
                                      O-witness-y-tm=x-tm-definition-rule
                                      O-definition-rule
                                      B-definition-rule
                                      r-definition-rule
                                      O-implies-good-state-fw)
                   :use ((:instance O-implies-good-state-fw))))))

 (local (defthm rlwfsk2c-O-3
          (implies (and (O x y)
                        (not (B x y))
                        (equal (aeps-state-tm y) (hstate-tm x)))
                   (B x (O-witness-y-tm=x-tm x y)))
          :hints (("Goal"
                   :use ((:instance rlwfsk2c-O-1)
                         (:instance rlwfsk2c-O-2)
                         (:instance B-definition-rule
                                    (s x)
                                    (w (O-witness-y-tm=x-tm x y))))
                   :in-theory (disable aeps-state-equal-definition-rule
                                       good-aeps-statep-definition-rule
                                       good-hstatep-definition-rule
                                       O-witness-y-tm=x-tm-definition-rule
                                       O-definition-rule
                                       b-definition-rule
                                       r-definition-rule rlwfsk2c-O-2
                                       rlwfsk2c-O-1)))))


 (local (defthm rlwfsk2c-O-4
          (implies (and (O x y)
                        (not (B x y))
                        (equal (aeps-state-tm y) (hstate-tm x)))
                   (O x (O-witness-y-tm=x-tm x y)))
          :hints (("Goal"
                   :use ((:instance rlwfsk2c-O-1)
                         (:instance rlwfsk2c-O-3)
                         (:instance O-definition-rule
                                    (x x)
                                    (y (O-witness-y-tm=x-tm x y))))
                   :in-theory (disable aeps-state-equal-definition-rule
                                       good-aeps-statep-definition-rule
                                       good-hstatep-definition-rule
                                       O-witness-y-tm=x-tm-definition-rule
                                       O-definition-rule
                                       b-definition-rule
                                       r-definition-rule rlwfsk2c-O-2
                                       rlwfsk2c-O-1)))))

 (defthm rlwfsk2c-O-5
   (implies (and (O x y)
                 (not (B x y))
                 (equal (aeps-state-tm y) (hstate-tm x)))
            (and (O x (O-witness-y-tm=x-tm x y))
                 (good-aeps-statep (O-witness-y-tm=x-tm x y))
                 (aeps-transp y (O-witness-y-tm=x-tm x y))
                 (< (rankls (O-witness-y-tm=x-tm x y) x)
                    (rankls y x))))
   :hints (("Goal"
            :use ((:instance rlwfsk2c-O-1)
                  (:instance rlwfsk2c-O-4)
                  (:instance l4)
                  (:instance rlwfsk2c-aeps-transp))
                  :in-theory (disable aeps-state-equal-definition-rule
                                      good-aeps-statep-definition-rule
                                      good-hstatep-definition-rule
                                      O-witness-y-tm=x-tm-definition-rule
                                      O-definition-rule
                                      b-definition-rule
                                      r-definition-rule rlwfsk2c-O-4
                                      aeps-transp-definition-rule
                                      rlwfsk2c-O-1 rlwfsk2c-O-2
                                      rlwfsk2c-O-3
                                      ACL2::DEFAULT-LESS-THAN-1
                                      ACL2::DEFAULT-LESS-THAN-2
                                      good-aeps-statep-contract
                                      good-hstatep-contract
                                      (:rewrite events-at-tm-l-set-equiv)))))

 (defthmd case-exhaustive
   (implies (and (good-hstatep x)
                 (good-aeps-statep y)
                 (O x y)
                 (not (B x y)))
            (<= (aeps-state-tm y) (hstate-tm x))))
  
 (defthmd rlwfsk2c-C
   (let ((z (if (< (aeps-state-tm y) (hstate-tm x))
                (O-witness-y-tm<x-tm y)
              (O-witness-y-tm=x-tm x y)))) 
     (implies (and (good-hstatep x)
                   (good-aeps-statep y)
                   (O x y)
                   (not (B x y)))
              (and (O x z)
                   (good-aeps-statep z)
                   (aeps-transp y z)
                   (< (rankls z x) (rankls y x)))))
   :hints (("Goal"
            :cases ((< (aeps-state-tm y) (hstate-tm x))
                    (= (aeps-state-tm y) (hstate-tm x)))
            :use ((:instance case-exhaustive)
                  (:instance rlwfsk2c-O-5)
                  (:instance rlwfsk2c-1))
            :in-theory (disable aeps-state-equal-definition-rule
                                good-aeps-statep-definition-rule
                                good-hstatep-definition-rule
                                O-witness-y-tm=x-tm-definition-rule
                                O-witness-y-tm<x-tm-definition-rule
                                O-definition-rule
                                b-definition-rule
                                r-definition-rule rlwfsk2c-1
                                case-exhaustive
                                ACL2::DEFAULT-LESS-THAN-1
                                ACL2::DEFAULT-LESS-THAN-2
                                good-aeps-statep-contract
                                good-hstatep-contract
                                aeps-transp-definition-rule
                                rankls-definition-rule
                                (:rewrite events-at-tm-l-set-equiv)
                                ;; c-implies-v-good-aeps-state
                                rlwfsk2c-O-5))))
 
 (local (in-theory (disable aeps-state-equal-definition-rule
                            good-aeps-statep-definition-rule
                            good-hstatep-definition-rule
                            O-witness-y-tm=x-tm-definition-rule
                            O-witness-y-tm<x-tm-definition-rule
                            O-definition-rule b-definition-rule
                            r-definition-rule rlwfsk2c-1 case-exhaustive
                            ACL2::DEFAULT-LESS-THAN-1
                            ACL2::DEFAULT-LESS-THAN-2
                            good-aeps-statep-contract good-hstatep-contract
                            aeps-transp-definition-rule
                            rankls-definition-rule
                            ;; c-implies-v-good-aeps-state
                            rlwfsk2c-C rlwfsk2c
                            rlwfsk2c-suff)))

 
 (defthmd O-is-good
   (implies (and (O x y)
                 (not (B x y)))
            (rlwfsk2c x y))
   :hints (("Goal"
            :cases ((< (aeps-state-tm y) (hstate-tm x))
                    (= (aeps-state-tm y) (hstate-tm x)))
            :use ((:instance case-exhaustive)
                  (:instance rlwfsk2c-C)
                  (:instance rlwfsk2c-suff (z (O-witness-y-tm=x-tm x y)))
                  (:instance rlwfsk2c-suff (z (O-witness-y-tm<x-tm y)))))))
 )#|ACL2s-ToDo-Line|#

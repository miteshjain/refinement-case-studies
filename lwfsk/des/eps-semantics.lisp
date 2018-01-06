(in-package "ACL2S")
(include-book "aeps-thms")

;; This file incluaeps only events needed to understand AEPS, our simple
;; discrete-event simulation system. All of the supporting theorems
;; can be found in the included book.

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

(defunbc valid-lo-tes (tevs time)
  "Checks if the list of timed events is valid: all events in tevs are
   scheduled to execute at a time >= to time" 
  :input-contract (and (lo-tep tevs) (timep time))
  (reduce* and t
           (map* (lambda (te tm) (>= (timed-event-tm te) tm)) tevs time)))

;;The execution of an event is modeled as an uninterpreted functions.
;;It takes the current time and the current memory as input and
;;returns an updated memory and a list of new events that are
;;scheduled to be executed at some time > tm. The new events are added
;;into Sch.

(encapsulate
 (((step-events-add * * *) => *)
  ((step-events-rm * * *) => *)
  ((step-memory  * * *) => *))
 
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

 (defthmd step-events-add-congruence
   (implies (and (memoryp mem)
                 (memoryp mem-equiv)
                 (eventp ev)
                 (timep tm)
                 (set-equiv mem mem-equiv))
            (set-equiv (step-events-add ev tm mem)
                       (step-events-add ev tm mem-equiv))))

 (defthmd step-events-rm-congruence
   (implies (and (memoryp mem)
                 (memoryp mem-equiv)
                 (eventp ev)
                 (timep tm)
                 (set-equiv mem mem-equiv))
            (set-equiv (step-events-rm ev tm mem)
                       (step-events-rm ev tm mem-equiv))))

 (defthmd step-memory-congruence
   (implies (and (memoryp mem)
                 (memoryp mem-equiv)
                 (eventp ev)
                 (timep tm)
                 (set-equiv mem mem-equiv))
            (set-equiv (step-memory ev tm mem)
                       (step-memory ev tm mem-equiv))))
 )

(defunbc aeps-transp (w v)
  "transition relation of AEPS"
  :input-contract (and (aeps-statep w) (aeps-statep v))
  (let ((w-tm (aeps-state-tm w))
        (w-tevs (aeps-state-tevs w))
        (w-mem (aeps-state-mem w)))
    (if (not (events-at-tm w-tevs w-tm))
        (aeps-state-equal v (aeps-state (1+ w-tm) w-tevs w-mem))
      (aeps-ev-transp w v))))

(defunc events-at-tm (tevs tm)
  "Returns the sublist of timed-events in tevs that are scheduled 
   to execute at time = tm"
  :input-contract (and (lo-tep tevs) (timep tm))
  :output-contract (lo-tep (events-at-tm Tevs tm))
  (filter* (lambda (tev tm) (equal (timed-event-tm tev) tm))
           tevs tm))

;; PETE: This should work. Use executable functions if possible.
;; (defunbc spec-ev-transp (w v w-tevs)
;;   :input-contract (and (aeps-statep w) (aeps-statep v) (lo-tep w-tevs))
;;   (let ((tm (aeps-state-tm w))
;;         (tevs (aeps-state-tevs w))
;;         (mem (aeps-state-mem w)))
;;     (if (endp w-tevs)
;;         nil
;;       (let* ((tev (car w-tevs))
;;              (ev (timed-event-ev tev))
;;              (etm (timed-event-tm tev))
;;              (new-evs (step-events ev tm mem))
;;              (new-mem (step-memory ev tm mem))
;;              (new-tevs (remove-ev tevs tev))
;;              (new-tevs (append new-evs new-tevs)))
;;         (or (and (equal etm tm)
;;                  (aeps-state-equal v (aeps-state tm new-tevs new-mem)))
;;             (spec-ev-transp (aeps-state tm (cdr tevs) mem) v))))))

;; (defunbc spec-ev-transp (w v)
;;   :input-contract (and (aeps-statep w) (aeps-statep v))
;;   (let ((tm (aeps-state-tm w))
;;         (tevs (aeps-state-tevs w))
;;         (mem (aeps-state-mem w)))
;;     (if (endp tevs)
;;         nil
;;       (let* ((tev (car tevs))
;;              (ev (timed-event-ev tev))
;;              (etm (timed-event-tm tev))
;;              (new-evs (step-events ev tm mem))
;;              (new-mem (step-memory ev tm mem))
;;              (new-tevs (remove-ev tevs tev))
;;              (new-tevs (append new-evs new-tevs)))
;;         (or (and (equal etm tm)
;;                  (aeps-state-equal v (aeps-state tm new-tevs new-mem)))
;;             (spec-ev-transp (aeps-state tm (cdr tevs) mem) v))))))

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
             (aeps-state-equal v (aeps-state tm new-tevs new-mem)))))))

(defunc remove-tev (tev tevs)
  "Removes all occurrences of tev in tevs"
  :input-contract (and (timed-eventp tev) (lo-tep tevs) )
  :output-contract (lo-tep (remove-tev tev tevs))
  (filter* (lambda (e1 e2) (not (equal e1 e2))) tevs tev))

(defunc remove-tevs (l tevs)
  "Removes all occurrences of timed-events in l from tevs"
  :input-contract (and (lo-tep l) (lo-tep tevs))
  :output-contract (lo-tep (remove-tevs l tevs))
  (if (endp l)
      tevs
    (remove-tev (car l) (remove-tevs (cdr l) tevs))))

;; Optimized Discrete-Event Simulation System
(defunbc o-lo-tep (l)
  "An PEPS schedule recognizer"
  :input-contract t
  (and (lo-tep l)
       (ordered-lo-tep l)))

(defunbc ordered-lo-tep (l)
  "Check if a list of timed-events, l, is ordered"
  :input-contract (lo-tep l)
  (cond ((endp l) t)
        ((endp (cdr l)) t)
        (t (and (te-< (car l) (second l))
                (ordered-lo-tep (cdr l))))))

(defunbc te-< (te1 te2)
  "A total ordering on timed-events"
  :input-contract (and (timed-eventp te1) (timed-eventp te2))
  (let ((t1 (timed-event-tm te1))
        (e1 (timed-event-ev te1))
        (t2 (timed-event-tm te2))
        (e2 (timed-event-ev te2)))
    (or (< t1 t2)
        (and (equal t1 t2) (event-< e1 e2)))))

(defunbc event-< (e1 e2)
  "A total ordering on events"
  :input-contract (and (eventp e1) (eventp e2))
  (and (string< e1 e2) t))

;; State of PEPS consists of the current time, the ordered list of
;; timed-events to execute and the memory.
(defdata peps-state
  (record (tm . time)
          (otevs . o-lo-te)
          (mem . memory)))

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

(defunc insert-otevs (l otevs)
  "Insert timed-events in l in otevs"
  :input-contract (and (lo-tep l) (o-lo-tep otevs))
  :output-contract (o-lo-tep (insert-otevs l otevs))
  (if (endp l)
      otevs
    (insert-tev (car l) (insert-otevs (cdr l) otevs))))

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


;; We show PEPS refines AEPS as follows:

;; 1. We first define HPEPS, a machine obtained by augmenting a
;; state of PEPS with a history component.

;; 2. Next we show that PEPS refines HPEPS 

;; 3. Finally we show that HPEPS refines AEPS.

;; We then appeal to the transitivity property of skipping refinement to
;; infer that PEPS refines AEPS. 


;; Step 1: Define HPEPS

;; A state of the HPEPS consists of the current time, the ordered
;; list of timed-events to execute, the memory, and the history
;; component.

(defdata hstate
  (record (tm . time)
          (otevs . o-lo-te)
          (mem . memory)
          (h . history)))

;; where the history component consists of the valid bit, the current
;; time, the ordered list of timed-events to execute, and the memory.
(defdata history
  (record (valid . boolean)
          (tm . time)
          (otevs . o-lo-te)
          (mem . memory)))

;; The transition function of HPEPS is obtained by modifying
;; PEPS-transf, the transition function of PEPS such that the
;; history component of the state records the past information.
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

;; PEPS refines HPEPS under the refinement map P
(defunc P (s)
  :input-contract (peps-statep s)
  :output-contract (hstatep (P s))
  (let ((tm (peps-state-tm s))
        (otevs (peps-state-otevs s))
        (mem (peps-state-mem s)))
    (hstate tm otevs mem (history nil 0 nil nil))))

;; We provide as witness a binary relation A and show that it is a
;; simulation relation

(encapsulate
 ((A (x y) t))

 (defthm A-is-a-binary-relation
   (booleanp (A x y)))
 )

;; Step 2: To show that PEPS refines HPEPS under the refinement
;; map P we first show that the A agrees with the refinement map P

(defthm P-good
  (implies (good-peps-statep s)
           (A s (P s))))

;; Next we show that A is a RWFSK on the disjoint union of HPEPS and
;; PEPS. Since both machines do not stutter we ignore rankt. Also
;; since both machines are deterministic we have simplified the
;; theorem by dropping the existential quantifier in RWFSK2b . We can
;; show that there is a simulation relation between PEPS and
;; HPEPS. However, showing that A is an SKS suffices for our purpose.

(defthm A-is-a-RWFSK
  (implies (A s w)
           (A (peps-transf s)
              (hpeps-transf w))))

(defthm good-peps-inductive
  (implies (good-peps-statep s)
           (good-peps-statep (peps-transf s))))

(defthm good-hstate-inductive
  (implies (good-hstatep s)
           (good-hstatep (hpeps-transf s))))


;; A state of PEPS is good if it has a valid list of timed-events.
(defunbc good-peps-statep (s)
  "good peps state recognizer"
  :input-contract t
  (and (peps-statep s)
       (valid-lo-tes (peps-state-otevs s) (peps-state-tm s))))

;; A state of HPEPS is good if it has a valid list of timed-events
;; and the history is good.
(defunbc good-hstatep (s)
  :input-contract t
  (and (hstatep s)
       (valid-lo-tes (hstate-otevs s) (hstate-tm s))
       (good-histp s)))

;; History is good if it records a time, an ordered list of
;; timed-events, and a memory, when "steped" results in the current
;; state.

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

;; hstate-equal: compares the current time, the ordered list of
;; timed-events and the memory in two states. In addition, it compares
;; that the history of two states is either both valid or both
;; invalid. In case the history is valid then it also compare the
;; history components.

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


;; Step 3: Next we show that HPEPS refines AEPS under the refinement
;; map R
(defunc R (s)
  "A refinement map from an PEPS state to a AEPS state"
  :input-contract (hstatep s)
  :output-contract (aeps-statep (R s))
  (aeps-state (hstate-tm s) (hstate-otevs s) (hstate-mem s)))

;; We provide as witness a binary relation B and show that it is an
;; SKS relation.

(encapsulate
 ;;"SKS relation between an PEPS state and a AEPS state"
 ((B (x y) t))
 
 (defthm B-is-a-binary-relation
   (booleanp (B x y)))
 )

;; First we show that the B agrees with the refinement map R
(defthm R-good
  (implies (good-hstatep s)
           (B s (R s))))

;; Next we show that B is an RLWFSK on the disjoinT union of HPEPS and
;; AEPS. Since both machines do not stutter, we ignore rankt. We
;; define as witness a binary relation O and rankls that satisfy
;; RLWFSK2.

(encapsulate
 ((O (x y) t)
  (rankls (y x) t))

 (local (defun O (x y)
          (declare (ignore x y))
          t))

 (local (defun rankls (y x)
          (declare (ignore x y))
          0))
 
 (defthm O-is-a-binary-relation
   (booleanp (C x y)))

 (defthm rankls-contract
   (implies (and (aeps-statep y) (hstatep x))
            (natp (rankls y x))))
 )

;; Next we show that B is an RLWFSK.
(defthm B-is-an-RLWFSK
  (implies (B s w)
           (rlwfsk2b (hpeps-transf s) w)))

(defun-sk rlwfsk2b (u w)
  (exists v
    (and (aeps-transp w v)
         (O u v))))

(defthm O-is-good
  (implies (and (O x y)
                (not (B x y)))
           (rlwfsk2c x y)))

(defun-sk rlwfsk2c (x y)
  (exists z
    (and (aeps-transp y z)
         (O x z)
         (< (rankls z x) (rankls y x)))))

(in-package "ACL2S")
(include-book "string-order" :ttags :all)
(include-book "defunbc" :ttags :all)
(include-book "higher-order" :ttags :all)

;; This file includes only events needed to understand the semantics
;; of the event-simulation systems and top-level proof of correctness.

;; Data definitions for DES, an abstract high-level specification

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

(defunbc valid-lo-tes (tevs time)
  "Checks if the list of timed events is valid: all events in tevs are
   scheduled to execute at a time >= to time" 
  :input-contract (and (lo-tep tevs) (timep time))
  (reduce* and t
           (map* (lambda (te tm) (>= (timed-event-tm te) tm)) tevs time)))

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
                 (valid-lo-tes (step-events ev tm mem)
                               (1+ tm)))))
 
 (defthm step-memory-contract
   (implies (and (eventp ev)
                 (timep tm)
                 (memoryp mem))
            (memoryp (step-memory ev tm mem))))

 (defthm step-events-congruence
   (implies (and (memoryp mem)
                 (memoryp mem-equiv)
                 (eventp ev)
                 (timep tm)
                 (set-equiv mem mem-equiv))
            (set-equiv (step-events ev tm mem)
                       (step-events ev tm mem-equiv))))

 (defthm step-memory-congruence
   (implies (and (memoryp mem)
                 (memoryp mem-equiv)
                 (eventp ev)
                 (timep tm)
                 (set-equiv mem mem-equiv))
            (set-equiv (step-memory ev tm mem)
                       (step-memory ev tm mem-equiv))))
 )

(defunbc spec-transp (w v)
  "transition relation of DES"
  :input-contract (and (des-statep w) (des-statep v))
  (let ((w-tm (des-state-tm w))
        (w-tevs (des-state-tevs w))
        (w-mem (des-state-mem w)))
    (if (not (events-at-tm w-tevs w-tm))
        (des-state-equal v (des-state (1+ w-tm) w-tevs w-mem))
      (spec-ev-transp w v))))

(defunc events-at-tm (tevs tm)
  "Returns the sublist of timed-events in tevs that are scheduled 
   to execute at time = tm"
  :input-contract (and (lo-tep tevs) (timep tm))
  :output-contract (lo-tep (events-at-tm Tevs tm))
  (filter* (lambda (tev tm) (equal (timed-event-tm tev) tm))
           tevs tm))

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
             (des-state-equal v (des-state tm new-tevs new-mem)))))))

(defunc remove-ev (tevs ev)
  "Removes all occurrences of ev in tevs"
  :input-contract (and (lo-tep tevs) (timed-eventp ev))
  :output-contract (lo-tep (remove-ev tevs ev))
  (filter* (lambda (e1 e2) (not (equal e1 e2))) tevs ev))

;; Optimized Discrete-Event Simulation System that can execute
;; multiple events simultaneously
(defunbc o-lo-tep (l)
  "An OptDES schedule recognizer"
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

;; State of MODES consists of the current time, an ordered list of
;; timed-events to execute and the memory.
(defdata modes-state
  (record (tm . time)
          (otevs . o-lo-te)
          (mem . memory)))

(defunbc modes-state-equal (s w)
  :input-contract t
  (or (equal s w)
      (and (modes-statep s)
           (modes-statep w)
           (equal (modes-state-tm s)
                  (modes-state-tm w))
           (equal (modes-state-otevs s)
                  (modes-state-otevs w))
           (set-equiv (modes-state-mem s)
                      (modes-state-mem w)))))

(defunbc modes-transp (s u)
  "transition relation of MODES machine"
  :input-contract (and (modes-statep s) (modes-statep u))
  (let ((tm (modes-state-tm s))
        (otevs (modes-state-otevs s))
        (mem (modes-state-mem s)))
    (if (endp otevs)
        (modes-state-equal u (modes-state (1+ tm) otevs mem))
      (let ((tm (timed-event-tm (car otevs))))
        (modes-tm-transp s u tm)))))

(defun-sk modes-tm-transp (s u tm)
  (exists Etm
      (and (lo-tep Etm)
           (consp Etm) 
           (let* ((otevs (modes-state-otevs s))
                  (mem (modes-state-mem s))
                  (res (execute-tevs Etm otevs mem))
                  (new-otevs (first res))
                  (new-mem (second res)))
             (and (subsetp-equal Etm (events-at-tm-otevs otevs tm))
                  (modes-state-equal u (modes-state tm new-otevs new-mem)))))))

(defunc execute-tevs (tevs otevs mem)
  "executes events in tevs in the order they appear in the list"
  :input-contract (and (lo-tep tevs) (o-lo-tep otevs) (memoryp mem))
  :output-contract (and (true-listp (execute-tevs tevs otevs mem))
                        (o-lo-tep (first (execute-tevs tevs otevs mem)))
                        (memoryp (second (execute-tevs tevs otevs mem))))
  (cond ((endp tevs)
         (list otevs mem))
        (t 
         (b* ((tev (car tevs))
              (ev (timed-event-ev tev))
              (et (timed-event-tm tev))
              (new-tevs (step-events ev et mem))
              (new-mem (step-memory ev et mem))
              (new-otevs (remove-ev-otevs otevs tev))
              (new-otevs (insert-otevs new-tevs new-otevs)))
           (execute-tevs (cdr tevs) new-otevs new-mem)))))

(defunc events-at-tm-otevs (otevs tm)
  "Returns the sublist of timed-events in otevs that are scheduled 
   to execute at time = tm"
  :input-contract (and (o-lo-tep otevs) (timep tm))
  :output-contract (o-lo-tep (events-at-tm-otevs tevs tm))
  (filter* (lambda (tev tm) (equal (timed-event-tm tev) tm))
           otevs tm))

(defunc remove-ev-otevs (otevs tev)
  "Remove timed-event tev form otevs"
  :input-contract (and (o-lo-tep otevs) (timed-eventp tev))
  :output-contract (o-lo-tep (remove-ev-otevs otevs tev))
  (if (endp otevs)
      nil
    (if (equal (car otevs) tev)
        (remove-ev-otevs (cdr otevs) tev)
      (cons (car otevs)
            (remove-ev-otevs (cdr otevs) tev)))))

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

;; We show that MODES refines DES as follows

;; We define three intermediate machines, B-machine, H-machine, and
;; Hp-machine. Next we show that B-machine refines H-machine and then
;; H-machine refines DES


(defdata bstate
  (record (tm . time)
          (otevs . o-lo-te)
          (mem . memory)))

(defunbc bstate-equal (s w)
  :input-contract t
  (or (equal s w)
      (and (bstatep s)
           (bstatep w)
           (equal (bstate-tm s)
                  (bstate-tm w))
           (equal (bstate-otevs s)
                  (bstate-otevs w))
           (set-equiv (bstate-mem s)
                      (bstate-mem w)))))

(defunbc b-transp (s u)
  :input-contract (and (bstatep s) (bstatep u))
  (let ((tm (bstate-tm s))
        (otevs (bstate-otevs s))
        (mem (bstate-mem s)))
    (if (endp otevs)
        (bstate-equal u (bstate (1+ tm) otevs mem))
      (b-ev-transp s u (timed-event-tm (car otevs))))))


(defun-sk b-ev-transp (s u tm)
  (exists tev
    (let ((otevs (bstate-otevs s))
          (mem (bstate-mem s)))
      (and (timed-eventp tev)
           (member-equal tev (events-at-tm-otevs otevs tm))
           (let* ((ev (timed-event-ev tev))
                  (new-evs (step-events ev tm mem))
                  (new-mem (step-memory ev tm mem))
                  (new-otevs (remove-ev-otevs otevs tev))
                  (new-otevs (insert-otevs new-evs new-otevs)))
             (bstate-equal u (bstate tm new-otevs new-mem)))))))

;; H-machine
(defdata hstate
  (record (tm . time)
          (otevs . o-lo-te)
          (mem . memory)
          (h . history)))

(defdata history
  (record (valid . boolean)
          (tm . time)
          (otevs . o-lo-te)
          (mem . memory)))

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


(defunbc h-transp (s u)
  :input-contract (and (hstatep s) (hstatep u))
  (let ((tm (hstate-tm s))
        (otevs (hstate-otevs s))
        (mem (hstate-mem s)))
    (if (endp otevs)
        (hstate-equal u (hstate (1+ tm) otevs mem
                                (history t tm otevs mem)))
      (h-ev-transp s u (timed-event-tm (car otevs))))))

(defun-sk h-ev-transp (s u tm)
  (exists tev
    (let ((otevs (hstate-otevs s))
          (mem (hstate-mem s)))
      (and (timed-eventp tev)
           (member-equal tev (events-at-tm-otevs otevs tm))
           (let* ((ev (timed-event-ev tev))
                  (new-evs (step-events ev tm mem))
                  (new-mem (step-memory ev tm mem))
                  (new-otevs (remove-ev-otevs otevs tev))
                  (new-otevs (insert-otevs new-evs new-otevs))
                  (hist (history t tm otevs mem)))
           (hstate-equal u (hstate tm new-otevs new-mem hist)))))))

;; B-machine refines H-machine under a refinement map P1
(defunc P1 (s)
  :input-contract (bstatep s)
  :output-contract (hstatep (P1 s))
  (let ((tm (bstate-tm s))
        (otevs (bstate-otevs s))
        (mem (bstate-mem s)))
    (hstate tm otevs mem (history nil 0 nil nil))))

(defunbc good-hstatep (s)
  :input-contract t
  (and (hstatep s)
       (valid-lo-tevs (hstate-otevs s) (hstate-tm s))
       (good-histp s)))

(defunbc good-bstatep (s)
  "good b-machine state recognizer"
  :input-contract t
  (and (bstatep s)
       (valid-lo-tevs (bstate-otevs s) (bstate-tm s))))


(encapsulate
 ((A (x y) t))
 
 (local (defun A (x y)
          (declare (ignore x y))
          t))

 (defthm A-is-a-binary-relation
   (booleanp (A x y)))
 )

(defthm P1-good
  (implies (good-bstatep s)
           (A s (P1 s))))


(defun-sk wfs-a (u w)
  (exists v
    (and (good-hstatep v)
         (h-transp w v)
         (A u v))))

(defthm A-is-a-bisimulation
  (implies (and (A s w)
                (good-bstatep u)
                (b-transp s u))
           (wfs-a u w)))

(defthm good-bstate-inductive
  (implies (and (good-bstatep s)
                (bstatep u)
                (b-transp s u))
           (good-bstatep u)))

(defthm good-hstate-inductive
  (implies (and (good-hstatep s)
                (hstatep u)
                (h-transp s u))
           (good-hstatep u))))

; h-machine refines des
(defunc R1 (s)
  "A refinement map from an hstate to a DES state"
  :input-contract (hstatep s)
  :output-contract (des-statep (R1 s))
  (des-state (hstate-tm s) (hstate-otevs s) (hstate-mem s)))

(encapsulate
 ;;"SKS relation between an hstate and a DES state"
 ((B1 (x y) t))
 
 (local (defun B1 (x y)
          (declare (ignore x y))
          t))

 (defthm B1-is-a-binary-relation
   (booleanp (B1 x y)))
 )


(defthm R1-good
  (implies (good-hstatep s)
           (B1 s (R s))))

(encapsulate
 ((C1 (x y) t)
  (rankls1 (y x) t))

 (local (defun C1 (x y)
          (declare (ignore x y))
          t))

 (local (defun rankls1 (y x)
          (declare (ignore x y))
          0))
 
 (defthm C1-is-a-binary-relation
   (booleanp (C1 x y)))

 (defthm rankls1-contract
   (implies (and (des-statep y) (hstatep x))
            (natp (rankls1 y x))))
 )


;; Next we show that B1 is an LWFSK.
(defthm B1-is-a-LWFSK
  (implies (and (B1 s w)
                (good-hstatep u)
                (h-transp s u))
           (or (lwfsk2a u w)
               (lwfsk2d u w))))

(defun-sk lwfsk2a (u w)
  (exists v
    (and (spec-transp w v)
         (B1 u v))))

(defun-sk lwfsk2d (u w)
  (exists v
    (and (spec-transp w v)
         (C1 u v))))

(defthm C1-is-good
  (implies (and (C1 x y)
                (not (B1 x y)))
           (lwfsk2f x y)))

(defun-sk lwfsk2f (x y)
  (exists z
    (and (spec-transp y z)
         (C1 x z)
         (< (rankls1 z x) (rankls1 y x)))))

;; Hp-machine


(defdata hpstate
  (record (tm . time)
          (otevs . o-lo-te)
          (mem . memory)
          (h . bseq)))

(defdata bseq (listof bstate))

(defunbc hpstate-equal (s w)
  :input-contract t
  (or (equal s w)
      (and (hpstatep s)
           (hpstatep w)
           (equal (hpstate-tm s)
                  (hpstate-tm w))
           (equal (hpstate-otevs s)
                  (hpstate-otevs w))
           (set-equiv (hpstate-mem s)
                      (hpstate-mem w))
           (equal (hpstate-h s)
                  (hpstate-h w)))))


(defunbc hp-transp (s u)
  :input-contract (and (hpstatep s) (hpstatep u))
  (let ((tm (hpstate-tm s))
        (otevs (hpstate-otevs s))
        (mem (hpstate-mem s)))
    (if (endp otevs)
        (equal u (hpstate (1+ tm) otevs mem
                          (list (bstate tm otevs mem)
                                (bstate (1+ tm) otevs mem))))
      (hp-tm-transp s u
                    (timed-event-tm (car otevs))))))
(defun-sk hp-tm-transp (s u tm)
  (exists Etm
      (and (lo-tep Etm)
           (consp Etm) 
           (let* ((otevs (hpstate-otevs s))
                  (mem (hpstate-mem s))
                  (res (execute-tevs-with-hist Etm otevs mem (list (bstate tm otevs mem))))
                  (new-otevs (first res))
                  (new-mem (second res))
                  (bseq (third res)))
             (and (subsetp-equal Etm (events-at-tm-otevs otevs tm))
                  (hpstate-equal u (hpstate tm new-otevs new-mem bseq)))))))

; modes refines hp-machine under a refinement map P2
(defunc P2 (s)
  :input-contract (modes-statep s)
  :output-contract (hpstatep (P2 s))
  (let ((tm (modes-state-tm s))
        (otevs (modes-state-otevs s))
        (mem (modes-state-mem s)))
    (hpstate tm otevs mem (list (bstate tm otevs mem)))))

                   
(defunbc good-histhp (s)
  "Checks if the history component of an Hpstate is good"
  :input-contract (hpstatep s)
  (let ((bseq (hpstate-h s)))
    (implies (consp bseq)
             (b-transp+ (hpstate-h s) (projB s)))))

(defunbc b-transp+ (seq u)
  :input-contract (and (bseqp seq) (bstatep u))
  (cond ((endp seq)
         nil)
        ((endp (cdr seq))
         (equal (car seq) u))
        (t (and (equal (car seq) u)
                (b-transp (cadr seq) (car seq))
                (b-transp+ (cdr seq) (cadr seq))))))

(defunc projB (s)
  :input-contract (hpstatep s)
  :output-contract (bstatep (projB s))
  (bstate (hpstate-tm s) (hpstate-otevs s) (hpstate-mem s)))


(defunbc good-hpstatep (s)
  :input-contract (hpstatep s)
  (and (hpstatep s)
       (good-histhp s)
       (valid-lo-tevs (hpstate-otevs s) (hpstate-tm s))))

(defunbc good-modes-statep (s)
  :input-contract t
  (and (modes-statep s)
       (valid-lo-tevs (modes-state-otevs s) (modes-state-tm s))))



(encapsulate
 ((A2 (x y) t))
 
 (local (defun A2 (x y)
          (declare (ignore x y))
          t))

 (defthm A2-is-a-binary-relation
   (booleanp (A2 x y)))
 )

(defthm P2-good
  (implies (good-modes-statep s)
           (A2 s (P2 s))))

(defun-sk wfs-a-1 (u w)
  (exists v
    (and (good-hpstatep v)
         (hp-transp w v)
         (A2 u v))))

(defthm A2-is-a-bisimulation
  (implies (and (A2 s w)
                (good-modes-statep u)
                (modes-transp s u))
           (wfs-a-1 u w)))


(defthm good-modes-state-inductive
  (implies (and (good-modes-statep s)
                (modes-statep u)
                (modes-transp s u))
           (good-modes-statep u)))

(defthm good-hpstate-inductive
  (implies (and (good-hpstatep s)
                (hpstatep u)
                (hp-transp s u))
           (good-hpstatep u)))

              
(encapsulate
 ;;"SKS relation between a hp-state and a bstate"
 ((B2 (x y) t))
 
 (local (defun B2 (x y)
          (declare (ignore x y))
          t))

 (defthm B2-is-a-binary-relation
   (booleanp (B2 x y)))
 )

(defthm R2-good
  (implies (good-hpstatep s)
           (B2 s (R2 s))))


(encapsulate
 ((C2 (x y) t)
  (rankls2 (y x) t))

 (local (defun C2 (x y)
          (declare (ignore x y))
          t))

 (local (defun rankls2 (y x)
          (declare (ignore x y))
          0))
 
 (defthm C2-is-a-binary-relation
   (booleanp (C2 x y)))

 (defthm rankls2-contract
   (implies (and (bstatep y) (hpstatep x))
            (natp (rankls2 y x))))
 )

;; Next we show that B2 is an LWFSK.
(defun-sk lwfsk2a-1 (u w)
  (exists v
    (and (b-transp w v)
         (B2 u v))))

(defun-sk lwfsk2d-1 (u w)
  (exists v
    (and (b-transp w v)
         (C2 u v))))

(defthm B2-is-a-LWFSK
  (implies (and (B2 s w)
                (good-hpstatep u)
                (hp-transp s u))
           (or (lwfsk2a-1 u w)
               (lwfsk2d-1 u w))))


(defun-sk lwfsk2f-1 (x y)
  (exists z
    (and (b-transp y z)
         (C2 x z)
         (< (rankls2 z x) (rankls2 y x)))))

(defthm C2-is-good
  (implies (and (C2 x y)
                (not (B2 x y)))
           (lwfsk2f-1 x y)))

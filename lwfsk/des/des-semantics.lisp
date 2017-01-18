(in-package "ACL2S")
(include-book "pete-des")

;; This file includes only events needed to understand DES, our simple
;; discrete-event simulation system. All of the supporting theorems
;; can be found in the included book.

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
                 (set-equiv (double-rewrite mem) (double-rewrite mem-equiv)))
            (set-equiv (step-events ev tm mem)
                       (step-events ev tm mem-equiv))))

 (defthm step-memory-congruence
   (implies (and (memoryp mem)
                 (memoryp mem-equiv)
                 (eventp ev)
                 (timep tm)
                 (set-equiv (double-rewrite mem) (double-rewrite mem-equiv)))
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


;; Optimized Discrete-Event Simulation System
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

;; State of OptDES consists of the current time, the ordered list of
;; timed-events to execute and the memory.
(defdata odes-state
  (record (tm . time)
          (otevs . o-lo-te)
          (mem . memory)))

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


;; We show OptDES refines DES as follows:

;; 1. We first define HoptDES, a machine obtained by augmenting a
;; state of OptDES with a history component.

;; 2. Next we show that OptDES refines HoptDES 

;; 3. Finally we show that HoptDES refines DES.

;; We then appeal to the transitivity property of skipping refinement to
;; infer that OptDES refines DES. 


;; Step 1: Define HoptDES

;; A state of the HoptDES consists of the current time, the ordered
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

;; The transition function of HoptDES is obtained by modifying
;; odes-transf, the transition function of OptDES such that the
;; history component of the state records the past information.
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

(defunbc A (s w)
  "A binary relation between OptDES and HoptDES"
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

;; A state of OptDES is good if it has a valid list of timed-events.
(defunbc good-odes-statep (s)
  "good odes state recognizer"
  :input-contract t
  (and (odes-statep s)
       (valid-lo-tes (odes-state-otevs s) (odes-state-tm s))))

;; A state of HoptDES is good if it has a valid list of timed-events
;; and the history is good.
(defunbc good-hstatep (s)
  :input-contract t
  (and (hstatep s)
       (valid-lo-tes (hstate-otevs s) (hstate-tm s))
       (good-histp s)))

;; History is good if it records a time, an ordered list of
;; timed-events, and a memory which when "steped" results in the
;; current state.

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


;; Step 2: To show that OptDES refines HoptDES under the refinement
;; map P we first show that the refinement map P agrees with A.

(defthm P-good
  (implies (good-odes-statep s)
           (A s (P s))))

;; Next we show that A is a LWFSK on the disjoint union of HoptDES and
;; OptDES. Since both machines neither stutter or skip with respect to
;; each other, we ignore defining rankt and C. Also since both
;; machines are deterministic we have simplified the theorem by
;; dropping the existential quantifier in LWFSK2a . We can show that
;; there is a bisimulation relation between OptDES and
;; HoptDES. However, showing that A is a LWFSK suffices for our
;; purpose.

(defthm A-is-a-LWFSK
  (implies (and (good-odes-statep s)
                (good-hstatep w)
                (A s w))
           (A (odes-transf s)
              (hodes-transf w))))

 (defthm good-odes-inductive
   (implies (good-odes-statep s)
            (good-odes-statep (odes-transf s))))


(defthm good-hstate-inductive
  (implies (good-hstatep s)
           (good-hstatep (hodes-transf s))))

;; Step 3: Next we show that HoptDES refines DES under the refinement
;; map R
(defunc R (s)
  "A refinement map from an OptDES state to a DES state"
  :input-contract (hstatep s)
  :output-contract (des-statep (R s))
  (des-state (hstate-tm s) (hstate-otevs s) (hstate-mem s)))

;; We provide as witness a binary relation B and show that it is an
;; SKS relation.
(defunbc B (s w)
  "SKS relation between an OptDES state and a DES state"
  :input-contract t
  (and (good-hstatep s)
       (good-des-statep w)
       (des-state-equal (R s) w)))

;; First we show that the refinement map R agrees with B.
(defthm R-good
  (implies (good-hstatep s)
           (B s (R s))))

;; Next we show that B is an LWFSK on the disjoing union of HoptDES
;; and DES. Since both machines do not stutter, we ignore rankt. We
;; define as witness a binary relation C and rankls that satisfy
;; LWFSK2.

;; Informally, xCy holds if y can reach a state that is related to x
;; by B. This is true if x and y are related by B or else the list of
;; timed-events and the memory in y are (set) equal to the list of
;; timed-events and the memory in a predecessor of x and the current
;; time of y is less or equal to the current time of x.

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

(defunc rankls (y x)
  "rank function"
  :input-contract (and (des-statep y) (hstatep x))
  :output-contract (natp (rankls y x))
  (nfix (- (+ (hstate-tm x)
              (len (events-at-tm (des-state-tevs y) (hstate-tm x))))
           (des-state-tm y))))

;; Next we show that B is an LWFSK.
(defthm B-is-a-LWFSK
  (implies (and (good-hstatep s)
                (good-des-statep w)
                (B s w))
           (or (lwfsk2a (hodes-transf s) w)
               (lwfsk2d (hodes-transf s) w)))
  :rule-classes nil)

(defun-sk lwfsk2a (u w)
  (exists v
    (and (good-des-statep v)
         (good-hstatep u)
         (good-des-statep w)
         (B u v)
         (spec-transp w v))))

(defun-sk lwfsk2d (u w)
  (exists v
    (and (good-des-statep v)
         (good-hstatep u)
         (good-des-statep w)
         (C u v)
         (spec-transp w v))))

(defthmd C-is-a-witness
  (implies (and (good-hstatep x)
                (good-des-statep y)
                (C x y)
                (not (B x y)))
           (lwfsk2f x y)))

(defun-sk lwfsk2f (x y)
  (exists z
    (and (good-hstatep x)
         (good-des-statep y)
         (good-des-statep z)
         (spec-transp y z)
         (C x z)
         (< (rankls z x) (rankls y x)))))

(defthm good-des-statep-inductive
  (implies (and (good-des-statep w)
                (des-statep v)
                (spec-transp w v))
           (good-des-statep v)))

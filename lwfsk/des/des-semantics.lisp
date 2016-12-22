(set-inhibit-warnings "invariant-risk")
(local (include-book "data-structures/set-theory" :dir :system))


;; DES system

(defun storep (st)
  (declare (xargs :guard t))
  (and (alistp st)
       (acl2::setp-equal  st)))

(register-type store
               :predicate storep
               :enumerator nth-true-list)

(defdata event nat)
(defdata event-list (listof event))
(defdata pair (cons nat event))

(defun get-event (ep)
  (declare (xargs :guard (pairp ep)))
  (cdr ep))

(defun get-event-time (ep)
  (declare (xargs :guard (pairp ep)))
  (car ep))

(defdata lofp (alistof nat event))

(defun schp (l)
  (declare (xargs :guard t))
  (and (lofpp l)
       (acl2::setp-equal l)))

(register-type sch
               :predicate schp
               :enumerator nth-true-list)
           
(defun valid-timestamps (E ct f)
  "checks if all events are scheduled to execute at time greater (or
greater equal if flag f = false ) to ct"
  (declare (xargs :guard (and (schp E) (natp ct) (booleanp f))))
  (if (endp E)
      t
    (b* ((ep (car E))
         (et (get-event-time ep)))
      (and (if f (> et ct) (>= et ct))
           (valid-timestamps (cdr E) ct f)))))


;; execution of an event is modeled as an uninterpreted function. It
;; takes the current time and the current store as input and returns
;; an updated store and a list of new events that are scheduled to be
;; executed at some time > ct. to be added into sch.

(encapsulate
 ((execute-event (ev ct st) (mv t t))
  ; ev-const is a "special" event used to record that no event was
  ; picked in the predecessor state (refer to impl-step function
  ; below)"
  (ev-const () t))

 (local (defun ev-const ()
          0))
 
 (local (defun execute-event (ev ct st)
          (declare (ignore ev ct))
          (mv nil st)))

 (defthm execute-event-contract
   (mv-let
    (evl up-st)
    (execute-event ev ct st)
    (implies (storep st)
             (and (schp evl)
                  (valid-timestamps evl ct t)
                  (storep up-st)))))
  
 (defthm ev-const-contract
   (eventp (ev-const)))
 
 (defthm ev-const-does-not-change-st-E
   (mv-let (new-ev up-st)
           (execute-event (ev-const) ct st)
           (and (equal new-ev nil)
                (equal up-st st))))

 )

;; state of DES


;; I enforce the the valid-timestamps condition in the good-state
;; definition.  Is there a natural way to express dependence between
;; two fields in a record in defdata ?

(defdata sstate
  (record  (ct . nat)
           (E . sch)
           (st . store)))

(defun events-at-ct (E ct)
    "returns a list of pairs in E scheduled to execute at ct"
  (declare (xargs :guard (and (schp e) (natp ct))))
  (if (endp e)
      nil
    (if (equal (get-event-time (car e)) ct)
        (cons (car e)
              (events-at-ct (cdr e) ct))
      (events-at-ct (cdr e) ct))))

(defun rmv-event (ep E)
  "remove ep from E"
  (declare (xargs :guard (and (pairp ep) (schp E))))
  (if (endp E)
      nil
    (if (equal ep (car E))
        (cdr E)
      (cons (car E) (rmv-event ep (cdr E))))))

(defun add-event (ep E)
  "add ep to E"
  (declare (xargs :guard (and (pairp ep) (schp E))))
  (if (endp E)
      (list ep)
    (if (equal ep (car E))
        E
      (cons (car E) (add-event ep (cdr E))))))

(defun add-events (l E)
  "add events pair in l to E"
  (declare (xargs :guard (and (lofpp l)  (schp E))
                  :verify-guards nil))
  (if (endp l)
      E
    (add-event (car l) (add-events (cdr l) E))))

(defun-sk exists-ev-at-ct (w v)
  (exists ep
    (let ((ct (sstate-ct w))
          (E (sstate-E w))
          (st (sstate-st w))
          (ev (get-event ep)))
      (and (acl2::member-equal ep (events-at-ct E ct))
           (mv-let (new-evs up-st)
                   (execute-event ev ct st)
                   (let* ((up-E (rmv-event (cons ct ev) E))
                          (up-E (add-events new-evs up-E)))
                     (equal v (sstate ct up-E up-st))))))))
    
(defun spec-relation (w v)
  (let ((w-ct (sstate-ct w))
        (w-E (sstate-E w))
        (w-st (sstate-st w)))
    (if (not (events-at-ct w-E w-ct))
        (equal v (sstate (1+ w-ct) w-E w-st))
      (exists-ev-at-ct w v))))


;; OptDES

(defun e-< (p1 p2)
  (declare (xargs :guard (and (pairp p1) (pairp p2))))
  (let ((t1 (get-event-time p1))
        (e1 (get-event p1))
        (t2 (get-event-time p2))
        (e2 (get-event p2)))
    (or (< t1 t2)
        (and (equal t1 t2) (< e1 e2)))))

(defthm e-<-transitivity
  (implies (and (e-< p1 p2)
                (e-< p2 p3))
           (e-< p1 p3)))

(defthm e-<-not-reflexive
  (not (e-< p p)))

(defthm e-<-asymmetric
  (implies (and (pairp p1) (pairp p2)
                 (e-< p1 p2))
            (not (e-< p2 p1))))
 
(defthm e-<-trichotomy
  (implies (and (pairp p1) (pairp p2)
                (not (e-< p1 p2))
                (not (equal p1 p2)))
           (e-< p2 p1)))

(defun orderedp (l)
  "l is an ordered list of pairs"
  (declare (xargs :guard (lofpp l)))
  (cond ((atom l)
         (equal l nil))
        ((atom (cdr l))
         (equal (cdr l) nil))
        (t (let ((p1 (car l))
                 (p2 (cadr l)))
             (and (e-< p1 p2)
                  (orderedp (cdr l)))))))

(in-theory (disable e-<))

;; TODO: note that orderedp implies setp hence the definition of ischp
;; can be simplified to (and (lofpp x)  (orderedp x))
(defun ischp (x)
  (declare (xargs :guard t))
  (and (schp x)
       (orderedp x)))

(register-type isch
               :predicate ischp
               :enumerator nth-true-list)

(defdata istate
  (record (ct . nat)
          (E . isch)
          (st . store)
          ;; history
          (evh . event)
          (eth . nat)
          (sth . store)
          (Eh . isch)))

(defun rmv-event-pq (E)
  (declare (xargs :guard (ischp E)))
  (cdr E))

(defun pick-event-pq (E)
  (declare (xargs :guard (ischp E)))
  (car E))

(defun insert-event (ep E)
  "insert event pair ep into E"
  (declare (xargs :guard (and (pairp ep) (ischp E))))
  (if (endp E)
      (list ep)
    (cond ((equal ep (car E))
           E)
          ((e-< ep (car E))
           (cons ep E))
          (t (cons (car E) (insert-event ep (cdr E)))))))

(defun insert-events (l E)
  "insert list l of event-pairs in E"
  (declare (xargs :guard (and (lofpp l) (ischp E))
                  :verify-guards nil))
  (if (endp l)
      E
    (insert-event (car l) (insert-events (cdr l) E))))

(defun impl-step (s)
  (declare (xargs :guard (istatep s)
                  :verify-guards nil))
  (let ((ct (istate-ct s))
        (E (istate-E s))
        (st (istate-st s)))
    (if (endp E)
        (istate (1+ ct) E st (ev-const) ct st nil)
      (b* ((ep (pick-event-pq E))
           ((mv new-ev up-st) (execute-event (get-event ep) ct st))
           (up-E (rmv-event-pq E))
           (up-E (insert-events new-ev up-E))
           (up-ct (get-event-time ep)))
        (istate up-ct up-E up-st  (get-event ep) (get-event-time ep) st E)))))

(defun ref-map (s)
  (declare (xargs :guard  (istatep s)))
  (sstate (istate-ct s) (istate-E s) (istate-st s)))


(defthm ref-map-contract
  (implies (istatep s)
           (sstatep (ref-map s)))
  :hints (("goal" :in-theory (e/d () (sstate istate-ct istate-E istate-st)))))

(defthm ref-map-rewrite
  (implies (istatep s)
           (and (equal (sstate-ct (ref-map s)) (istate-ct s))
                (equal (sstate-E (ref-map s)) (istate-E s))
                (equal (sstate-st (ref-map s)) (istate-st s)))))

(in-theory (disable ref-map))

(defun B (s w)
  (declare (xargs :guard (and (istatep s) (sstatep w))))
  (and (equal (sstate-ct (ref-map s)) (sstate-ct w))
       (equal (sstate-st (ref-map s)) (sstate-st w))
       (acl2::set-equiv (sstate-E (ref-map s)) (sstate-E w))))

(defun C (x y)
  (declare (xargs :guard (and (sstatep y) (istatep x))))
  (and (valid-timestamps (sstate-E y) (istate-ct x) nil)
       (or (and (<= (sstate-ct y) (istate-ct x))
                (equal (sstate-st y) (istate-sth x))
                (acl2::set-equiv (sstate-E y) (istate-Eh x)))
           (B x y))))

(defun rankls (y x)
  (declare (xargs :guard (and (sstatep y) (istatep x))))
  (nfix (- (+ (istate-ct x) (len (events-at-ct (sstate-E y) (istate-ct x))))
           (sstate-ct y))))

(defun igood-statep (s)
  (declare (xargs :guard t
                  :verify-guards nil))
  (and (istatep s)
       (valid-timestamps (istate-E s) (istate-ct s) nil)
       ;; the last event picked for execution must be scheduled to
       ;; execute at the current time (istate-ct s)
       (equal (istate-eth s) (istate-ct s))
       ;; Eh is a good schedular, i.e. the timestamps are valid and
       ;;  (eth evh) must be the first element in Eh
       (valid-timestamps (istate-Eh s) (istate-eth s) nil)
       (equal (car (istate-Eh s)) (cons (istate-eth s) (istate-evh s)))
       ;; TODO: member condition below is implied by the above
       ;; condition. Prove an appropriate lemma and remove it.
       (acl2::member-equal (cons (istate-eth s) (istate-evh s)) (istate-Eh s))
       ;; the store and E of s are results of executing the event evh
       ;; on the store sth
       (mv-let (new-evs up-st)
               (execute-event (istate-evh s) (istate-ct s) (istate-sth s))
               (and (equal (istate-st s) up-st)
                    ;; following is "equal" because a set has a unique
                    ;; representation as a ordered list.
                    (equal (istate-E s) (insert-events
                                         new-evs
                                         (rmv-event-pq (istate-Eh s))))))))
(defun sgood-statep (s)
  (declare (xargs :guard t
                  :verify-guards nil))
  (and (sstatep s)
       (valid-timestamps (sstate-E s) (sstate-ct s) nil)))


;; proof of LWFSK

;; The required lemmas are proven in des-thms.lisp. The following
;; definitions/theorems are indication of the proof structure. Several
;; hints are ignored for clarity. So we do no expect to admit the form
;; below. 


;; Let s be an istate, s--> u the two proof obligations are there
;;  exists a v such that uBv (LWFSK2a holds) or there exists a v such
;;  that uCv (LWFSK2d holds)

;; We consider two cases 1. there is an event in s.E to be executed at
;; current time s.ct 2. There are no events in s.E to be executed at
;; current time s.ct. In the first case we construct a witness v such
;; that uBv holds. In the second case we construct a witness such that
;; uCv holds. In both cases we show that the witness is a successor of
;; (ref-map s).

(defun B-witness-v-event-at-ct (ev w)
  (declare (xargs :guard (and (eventp ev) (sstatep w))
                  :verify-guards nil))
 " ev is an event that is choosen in w to be executed at the current
   time"
  (b* (((mv new-evs up-st) (execute-event ev (sstate-ct w) (sstate-st w)))
       (up-E (rmv-event (cons (sstate-ct w) ev) (sstate-E w)))
       (up-E (add-events new-evs up-E))
       (v (sstate (sstate-ct w) up-E up-st)))
    v))

(defun B-witness-v-noevent-at-ct (w)
  (declare (xargs :guard (sstatep w)))
  (sstate (1+ (sstate-ct w)) (sstate-E w) (sstate-st w)))

;; TODO consider the following alternative definition as it
;; illustrates the dependence of the witness on s"

;; (defun B-witness-v-event-at-ct (s)
;; ;  (declare (xargs :guard (and (eventp ev) (sstatep w))))
;;  " ev is an event that is choosen in w to be executed at the current
;;    time"
;;  (b* ((u (impl-step s))
;;       (w (ref-map s))
;;       (ev (istate-evh u))
;;       ((mv new-evs up-st) (execute-event ev (sstate-ct w) (sstate-st w)))
;;       (up-E (rmv-event (cons (sstate-ct w) ev) (sstate-E w)))
;;       (up-E (add-events new-evs up-E))
;;       (v (sstate (sstate-ct w) up-E up-st)))
;;    v))

;; (defun B-witness-v-noevent-at-ct (s)
;;   (declare (xargs :guard (istatep s)))
;;   (let ((w (ref-map s)))
;;     (sstate (1+ (sstate-ct w)) (sstate-E w) (sstate-st w))))


(encapsulate
 ()

 
 (local (defthm l1
   (implies (and (consp l)
                 (ischp l))
            (and (pairp (car l))
                 (ischp (cdr l))))
   :hints (("goal" :in-theory (enable ischp)))))
 
 (defthmd impl-step-contract
   (implies (istatep s)
            (istatep (impl-step s)))
   :hints (("goal" :in-theory (enable get-event))))

 
 (local (defthmd B-events-at-ct
          (let* ((u (impl-step s))
                 (ev (get-event (pick-event-pq (istate-E s))))
                 (w (ref-map s))
                 (v (B-witness-v-event-at-ct ev w)))
            (implies (and (istatep s)
                          (igood-statep s)
                          (events-at-ct (istate-E s) (istate-ct s)))
                     (and (spec-relation w v)
                          (B u v))))
          :hints (("goal" :in-theory (union-theories '() (theory 'minimal-theory))
                   :use ((:instance B-constraints-events-at-ct)
                         (:instance impl-step-contract))))))

 (local (defthmd B-constraints-noevents-at-ct
          (let* ((u (impl-step s))
                 (w (ref-map s))
                 (v (B-witness-v-noevent-at-ct w)))
            (implies (and (istatep s)
                          (igood-statep s)
                          (not (events-at-ct (istate-E s) (istate-ct s))))
                     (and (spec-relation w v)
                          (C u v))))))

 (defun-sk B-witness-exists-1 (s)
  (exists v
    (and (spec-relation (ref-map s) v)
         (B (impl-step s) v))))
 
 (defun-sk B-witness-exists-2 (s)
   (exists v
     (and (spec-relation (ref-map s) v)
          (C (impl-step s) v))))
 
 (defthm B-constraints
   (implies (and (istatep s)
                 (igood-statep s))
            (or (B-witness-exists-1 s)
                (B-witness-exists-2 s)))
   :hints (("goal" :cases ((events-at-ct (istate-E s) (istate-ct s)))
            :use ((:instance B-witness-exists-1-suff (v (B-witness-v-event-at-ct
                                                         (get-event (pick-event-pq (istate-E s)))
                                                         (ref-map s))))
                  (:instance B-constraints-events-at-ct)
                  (:instance b-constraints-noevents-at-ct)
                  (:instance B-witness-exists-2-suff (v (B-witness-v-noevent-at-ct (ref-map s)))))
            :in-theory  (disable igood-statep istatep
                                 spec-relation B C ischp storep eventp
                                 b-witness-exists-1
                                 b-witness-exists-2
                                 B-witness-v-noevent-at-ct
                                 B-witness-v-event-at-ct
                                 ref-map pick-event-pq impl-step)))
   :rule-classes nil)
 )
            

;;  Next we show that C and rankls satisfy conditions in the second
;;  universal quantifier in LWFSK, i.e if xCy then either xBy or there
;;  exist a z such that xCz and rankls(z,x) < rankls(y, x)

;; Let xCy and ~(xBy). We consider two cases: 1. y.ct = x.ct 2. y.ct
;; <= y.ct. In each case we define a witness z and show that xCz holds
;; and the rank decreases. In each case we also show that z is a
;; successor of y, i.e (spec-relation y z).


(encapsulate
 ()
 (defun witness-x-ct=y-ct (x y)
          ;; (declare (xargs :guard (and (istatep x) (sstatep y))
          ;;                 :verify-guards nil))
   (b* ((ct (sstate-ct y))
        (E (sstate-E y))
        (st (sstate-st y))
        (eth (istate-eth x))
        (evh (istate-evh x))
        (eph (cons eth evh))
        ((mv new-evs up-st) (execute-event evh ct st))
        (up-E (rmv-event eph E))
        (up-E (add-events new-evs up-E))
        (z (sstate ct up-E up-st)))
     z))

 
 (local (defthmd c-spec-relation-2b
          (implies (and (istatep x)
                        (igood-statep x)
                        (sstatep y)
                        (C x y)
                        (not (B x y))                
                        (equal (istate-ct x) (sstate-ct y)))
                   (spec-relation y (witness-x-ct=y-ct x y)))))

 (defun witness-y-ct<-x-ct (y)
   (declare (xargs :guard (sstatep y)))
   (let* ((z-ct (sstate-ct y))
          (z-E (sstate-E y))
          (z-st (sstate-st y))
          (z (sstate (1+ z-ct) z-E z-st)))
     z))

 (local (defthmd spec-relation-no-event-at-ct
          (implies (and (istatep x)
                        (igood-statep x)
                        (sstatep y)
                        (sgood-statep y)
                        (not (events-at-ct (sstate-E y) (sstate-ct y)))
                        (C x y))
                   (spec-relation y (witness-y-ct<-x-ct y)))))

 (local (defthmd c-lemma-1
          (let ((z (if (< (sstate-ct y) (istate-ct x))
                       (witness-y-ct<-x-ct  y)
                     (witness-x-ct=y-ct x y))))
            (implies (and (istatep x)
                          (igood-statep x)
                          (sstatep y)
                          (sgood-statep y) 
                          (C x y)
                          (not (B x y)))
                     (C x z)))
          :hints (("goal" :in-theory (union-theories '() (theory 'minimal-theory))
                   :use ((:instance c-constraints-1))))))

 (local (defthmd c-lemma-2
          (let ((z (if (< (sstate-ct y) (istate-ct x))
                       (witness-y-ct<-x-ct  y)
                     (witness-x-ct=y-ct x y))))
            (implies (and (istatep x)
                          (igood-statep x)
                          (sstatep y)
                          (sgood-statep y) 
                          (C x y)
                          (not (B x y)))
                     (< (rankls z x) (rankls y x))))
          :hints (("goal" :in-theory (union-theories '() (theory 'minimal-theory))
                   :use ((:instance c-constraints-2))))))


 (defthmd c-constraints
   (let ((z (if (< (sstate-ct y) (istate-ct x))
                (witness-y-ct<-x-ct  y)
              (witness-x-ct=y-ct x y))))
     (implies (and (istatep x)
                   (igood-statep x)
                   (sstatep y)
                   (sgood-statep y) 
                   (C x y)
                   (not (B x y)))
              (and (C x z)
                   (< (rankls z x) (rankls y x)))))
   :hints (("goal" :in-theory (union-theories '() (theory 'minimal-theory))
            :use ((:instance c-lemma-1)
                  (:instance c-lemma-2)))))
 )

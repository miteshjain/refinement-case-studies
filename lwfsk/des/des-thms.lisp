
(encapsulate
 ()
 (local (include-book "std/osets/membership" :dir :system))
 (in-theory (enable get-event get-event-time acl2::<< natp acl2::lexorder alphorder e-<))
 
 (local (defthm l1
        (implies (and (pairp p1) (pairp p2)
                      (e-< p1 p2))
                 (acl2::<< p1 p2))))

 (local
  (defthm l2
    (implies (and (lofpp x) (orderedp x))
             (set::setp x))
    :hints (("goal" :induct (orderedp x)
             :in-theory (enable set::setp)))))

 (local
  (defthm l3
   (implies (set::setp X)
            (iff (acl2::member-equal e X)
                   (set::in e X)))
   :hints (("goal" :in-theory (enable set::subset set::head set::empty set::in
                                      set::setp set::tail )))))
   
 (local
  (defthm l4
   (implies (and (lofpp x) (lofpp y) (set::setp x) (set::setp y))
            (equal  (acl2::subsetp-equal x y)
                    (set::subset x y)))
    :hints (("goal" :in-theory (enable set::subset set::head set::empty set::in set::setp
                                       set::tail acl2::subsetp-equal acl2::member-equal)))))
   
 (local
  (defthm double-containment-osets
   ;; std/osets/membership.lisp
   (implies (and (set::setp X)
                 (set::setp Y))
            (equal (equal X Y)
                   (and (set::subset X Y)
                        (set::subset Y X))))
   :hints (("goal" :in-theory (enable set::double-containment)))))

  (local (in-theory (disable get-event get-event-time acl2::<< natp acl2::lexorder alphorder l4)))


  (local
   (defthm double-containment
     (implies (and (lofpp x) (lofpp y) (orderedp x) (orderedp y))
              (equal (equal x y)
                     (and (acl2::subsetp-equal x y)
                          (acl2::subsetp-equal y x))))
     :hints (("goal" :do-not-induct t
              :use ((:instance l4 (x y) (y x))
                    (:instance l4 (x x ) (y y)))))))

 (defthm orderedp-set-equal-is-equal
      (implies (and (lofpp x) (lofpp y) (orderedp x) (orderedp y))
               (equal (equal x y)
                      (acl2::set-equiv x y)))
      :hints (("goal" :in-theory (e/d (acl2::set-equiv) (double-containment))
               :use ((:instance double-containment)))))

(defthm ischp-set-equal-is-equal
  (implies (and (ischp x) (ischp y))
           (equal (equal x y)
                  (acl2::set-equiv x y)))
  :hints (("goal" :in-theory (e/d (ischp schp) (orderedp-set-equal-is-equal))
           :use ((:instance orderedp-set-equal-is-equal)))))

)

(defthm events-at-ct-contract
  (implies (and (schp E) (natp ct))
           (lofpp (events-at-ct E ct)))
  :hints (("goal" :in-theory (enable get-event get-event-time))))

(defthm schp-=>lofpp
   (implies (schp l)
            (lofpp l))
   :rule-classes (:rewrite  :forward-chaining))

(defthm schp-=>setp
   (implies (schp l)
            (acl2::setp-equal l))
   :rule-classes (:rewrite  :forward-chaining))

 (defthm lofpp-car-pairp
   (implies (and (lofpp l)
                 (consp l))
            (and (pairp (car l))
                 (lofpp (cdr l))))
   :rule-classes (:rewrite  :forward-chaining))

 (defthm schp-car-pairp
   (implies (and (schp l)
                 (consp l))
            (and (pairp (car l))
                 (schp (cdr l))))
   :rule-classes (:rewrite  :forward-chaining))


(defthm set-equiv-cons
  (implies (acl2::set-equiv E1 (cons ep E2))
           (consp E1))
  :hints (("goal" :use ((:instance acl2::set-equiv-implies-equal-consp-1
                                     (x-equiv E1) (x (cons ep E2)))))))




(defthm rmv-event-subset-eq
  (acl2::subsetp-equal (rmv-event ev E) E))


(encapsulate
 ()
 (local (defthm l1
          (implies (and (not (equal x y))
                        (member-eq y l))
                   (member-eq y (rmv-event x l)))))
 (defthm rmv-event-preserves-subset
   (implies (and (acl2::setp-equal E1) (acl2::setp-equal E2)
                 (acl2::subsetp-equal (double-rewrite E1) (double-rewrite E2)))
            (acl2::subsetp-equal (rmv-event ev E1)
                                 (rmv-event ev E2)))
   :hints (("goal" :in-theory (enable acl2::subsetp-equal
                                      acl2::setp-equal rmv-event acl2::member-equal))))
 )

(defthmd rmv-event-congruence-setequiv
  (implies (and (acl2::setp-equal E1) (acl2::setp-equal E2)
                (acl2::set-equiv (double-rewrite E1) (double-rewrite E2)))
           (acl2::set-equiv (rmv-event ep E1)
                            (rmv-event ep E2)))
  :hints (("goal" :in-theory (enable acl2::set-equiv))))

(encapsulate
 ()
 (local 
  (defthm l1
    (implies (and (acl2::setp-equal E1) (acl2::setp-equal (cons ep E2))
                  (acl2::set-equiv E1 (cons ep E2))
                  (consp E1))
             (acl2::set-equiv (rmv-event ep E1) E2))
    :hints (("goal" :in-theory (enable rmv-event)
             :use ((:instance rmv-event-congruence-setequiv
                              (ep ep) (E1 E1) (E2 (cons ep E2))))))))

 (defthm rmv-event-congruence-setequal-corollary
    (implies (and (acl2::setp-equal E1) (acl2::setp-equal (cons ep E2))
                  (acl2::set-equiv E1 (cons ep E2))
                  (consp E1))
             (acl2::set-equiv (rmv-event ep E1) E2))
    :hints (("goal" :in-theory (enable rmv-event)
             :use ((:instance rmv-event-congruence-setequiv
                              (ep ep) (E1 E1) (E2 (cons ep E2)))))))
 )
  
           
(defthm rmv-event-no-duplicate
  (implies (no-duplicatesp-equal E)
           (no-duplicatesp-equal (rmv-event ev E))))

(defthm rmv-event-setp
  (implies (acl2::setp-equal E)
           (acl2::setp-equal (rmv-event ev E)))
  :hints (("goal" :in-theory (enable acl2::setp-equal))))
            
(defthm rmv-event-contract
  (implies (schp E)
           (schp (rmv-event ev E))))

(in-theory (disable rmv-event-no-duplicate rmv-event-setp))

(defthmd add-event-contract-1a
  (implies (and (pairp ev)  (no-duplicatesp-equal E))
           (no-duplicatesp-equal (add-event ev E))))

(defthmd add-event-contract-1b
  (implies (and (pairp ev)  (acl2::setp-equal E))
           (no-duplicatesp-equal (add-event ev E)))
    :hints (("goal" :in-theory (e/d (acl2::setp-equal
                                     add-event-contract-1a)()))))

(defthmd add-event-contract-1
  (implies (and (pairp ev)  (schp E))
           (no-duplicatesp-equal (add-event ev E)))
  :hints (("goal" :in-theory (e/d (add-event-contract-1b)(pairp)))))

(defthm add-event-contract-2
  (implies (and (pairp ev)  (schp E))
           (true-listp (add-event ev E))))

(defthm add-event-contract-3
  (implies (and (pairp ev)  (schp E))
           (acl2::setp-equal (add-event ev E)))
  :hints (("goal" :in-theory (e/d (acl2::setp-equal) (schp pairp))
           :use ((:instance add-event-contract-2)
                 (:instance add-event-contract-1))
           :do-not-induct t)))


(defthmd add-event-contract-4
  (implies (and (pairp ev)  (schp E))
           (lofpp (add-event ev E)))
  :hints (("goal" :in-theory (e/d () (pairp)))))

(defthm add-event-contract
  (implies (and (pairp ev)  (schp E))
           (schp (add-event ev E)))
  :hints (("goal" :in-theory (e/d (acl2::setp-equal schp) (pairp)))))

(in-theory (disable add-event-contract-1a add-event-contract-1b
                    add-event-contract-1 add-event-contract-2
                    add-event-contract-3 add-event-contract-4))
                    

(defthm add-events-contract
  (implies (and (schp l)  (schp E))
           (schp (add-events l  E)))
  :hints (("goal" :in-theory (disable  (:rewrite acl2::default-less-than-1)
                                       (:rewrite lofpp-car-pairp)
                                       (:rewrite schp-=>lofpp)
                                       (:rewrite schp-=>setp)
                                       (:rewrite schp-car-pairp)))))



(defthm add-event-subset-eq
  (acl2::subsetp-equal  E (add-event ev E)))

(defthm add-event-preserves-subset
  (implies (and (acl2::setp-equal E1) (acl2::setp-equal E2)
                (acl2::subsetp-equal (double-rewrite E1) (double-rewrite E2)))
           (acl2::subsetp-equal (add-event ev E1)
                                (add-event ev E2)))
  :hints (("goal" :in-theory (enable acl2::subsetp-equal acl2::setp-equal add-event ))))

(defthmd add-event-congruence-setequal
  (implies (and (acl2::setp-equal E1) (acl2::setp-equal E2)
                (acl2::set-equiv (double-rewrite E1) (double-rewrite E2)))
           (acl2::set-equiv (add-event ev E1)
                            (add-event ev E2)))
  :hints (("goal" :in-theory (enable acl2::set-equiv))))

(in-theory (disable add-event-subset-eq add-event-preserves-subset))

(encapsulate
 ()
 (local
  (defthm l1
    (implies (and (acl2::setp-equal E1) (acl2::setp-equal (cons x E2))
                  (acl2::set-equiv E1 (cons x E2))
                  (consp E1))
             (acl2::set-equiv (add-event x E1) (cons x E2)))
  :hints (("goal" :in-theory (enable add-event)
           :use ((:instance add-event-congruence-setequal
                            (ev x) (E1 E1) (E2 (cons x E2))))))))
 
 (defthm add-event-congruence-setequal-corollary
  (implies (and (acl2::setp-equal E1) (acl2::setp-equal (cons x E2))
                (acl2::set-equiv E1 (cons x E2)))
           (acl2::set-equiv (add-event x E1) (cons x E2)))
  :hints (("goal" :in-theory (disable add-event)
           :use ((:instance l1)
                 (:instance set-equiv-cons)))))
 )


(encapsulate
 ()

 (local (in-theory (disable schp (:rewrite add-events-contract)
                            (:rewrite schp-=>setp)
                            (:rewrite schp-car-pairp))))

 (defthm add-events-congruence-setequal
   (implies (and (acl2::setp-equal E1) (acl2::setp-equal E2) (schp l) (schp e1) (schp e2)
                 (acl2::set-equiv (double-rewrite E1) (double-rewrite E2)))
            (acl2::set-equiv (add-events l E1)
                             (add-events l E2)))
   :hints (("subgoal *1/3''" 
            :use ((:instance add-event-congruence-setequal
                             (ev (car l))
                             (E1 (add-events (cdr l) E1))
                             (E2 (add-events (cdr l) E2)))
                  (:instance add-events-contract (l (cdr l)) (e e1))
                  (:instance add-events-contract (l (cdr l)) (e e2))
                  (:instance schp-=>setp (l (add-events (cdr l) E1)))
                  (:instance schp-=>setp (l (add-events (cdr l) E2)))))))
 )




(defthm orderedp-member-equal
  (implies (orderedp (cons x l))
           (not (member-equal x l)))
  :hints (("goal" :in-theory (e/d (member-equal) ( pairp natp) ))))

(defthm orderedp-=>-no-dupl
  (implies (orderedp l)
           (no-duplicatesp-equal l))
  :hints (("goal" :in-theory (e/d (acl2::setp-equal) (pairp lofpp )))))

(defthm orderedp-is-true-listp
  (implies (orderedp l) (true-listp l))
  :rule-classes (:forward-chaining))

(defthm orderedp-=>-setp
  (implies (orderedp l)
           (acl2::setp-equal l))
    :hints (("goal" :in-theory (e/d (acl2::setp-equal) (orderedp)))))


(in-theory (disable  orderedp-=>-no-dupl orderedp-is-true-listp))

(defthm insert-car
  (implies (and (pairp ep) (lofpp l)
                (consp l)
                (not (equal (car (insert-event ep l))
                            (car l))))
      (equal (car (insert-event ep l)) ep))
 :hints (("goal" :in-theory (e/d () ( pairp)))))
  

(defthm insert-event-is-lofp
  (implies (and (pairp ep) (ischp E))
           (lofpp (insert-event ep E)))
  :hints (("goal" :in-theory (e/d () ( e-< pairp)))))

(defthm insert-event-preserves-priority-queue
  (implies (and (pairp ep) (ischp E))
           (orderedp (insert-event ep E)))
  :hints (("goal" :in-theory (e/d () ( e-< pairp)))
          ("Subgoal *1/6.1" :in-theory (disable insert-car)
           :use ((:instance insert-car (ep ep) (l (cdr E)))))))

(defthm insert-event-is-a-setp
  (implies (and (pairp ep) (ischp E))
           (acl2::setp-equal (insert-event ep E)))
  :hints (("goal" :use ((:instance insert-event-preserves-priority-queue)
                        (:instance orderedp-=>-setp (l E)))
           :in-theory (disable pairp ischp orderedp-=>-setp insert-event-preserves-priority-queue))))

(defthm insert-event-is-ischp
  (implies (and (pairp ep) (ischp E))
           (ischp (insert-event ep E)))
  :hints (("goal" :use ((:instance insert-event-preserves-priority-queue)
                        (:instance orderedp-=>-setp (l E)))
           :in-theory (disable pairp ischp orderedp-=>-setp insert-event-preserves-priority-queue))))

(in-theory (disable insert-event-is-lofp insert-event-is-a-setp insert-car))

(defthmd E-subset-eq-insert-event
  (implies (pairp E)
           (acl2::subsetp-equal E (insert-event ep E))))




(defthmd insert-event-congruence-setequal
  (implies (and (ischp E1) (ischp E2)
                (acl2::set-equiv (double-rewrite E1) (double-rewrite E2)))
           (equal (insert-event ev E1)
                  (insert-event ev E2)))
  :hints (("goal" :in-theory (disable ischp insert-event
                                      ischp-set-equal-is-equal
                                      acl2::set-equiv-is-an-equivalence)
           :use ((:instance ischp-set-equal-is-equal (x E1 ) (y E2))))))


(defthm insert-events-contract
  (implies (and (lofpp l)
                (ischp E))
           (ischp (insert-events l E)))
  :hints (("goal" :in-theory (disable ischp 
                                      (:rewrite schp-=>setp)
                                      (:rewrite schp-car-pairp)))))

;; (defthmd insert-existing-event-nochange
;;   (implies (and (pairp ev) (ischp E)
;;                 (acl2::member-equal ev E))
;;            (equal (insert-event ev E)
;;                   E))
;;   :hints (("goal" :in-theory (e/d (acl2::member-equal) ()))))

;; (defthmd l-subset-E-insert-events-unchanged
;;   (implies (and (lofpp l) (ischp E)
;;                 (acl2::subsetp-equal l E))
;;            (equal (insert-events l E)
;;                   E))
;;   :hints (("goal" :in-theory (e/d (acl2::subsetp-equal insert-existing-event-nochange) ()))))


(encapsulate
 ()

 (local (in-theory (disable (:rewrite schp-=>setp)
                            (:rewrite schp-car-pairp)
                            e-< pairp)))

 (local (defthm insert-subset
          (implies (and (pairp ep) (lofpp l))
                   (subsetp-equal l (insert-event ep l)))))

 (local (defthm insert-event-member
          (implies (and (pairp ep) (lofpp l))
                   (member-equal ep (insert-event ep l)))))
 
 (local (defthm insert-preserves-subset
          (implies (and (pairp ep) (lofpp l1) (lofpp l2)
                        (subsetp-equal l1 l2))
                   (subsetp-equal (insert-event ep l1)
                                  (insert-event ep l2)))))

 (local (defthmd insert-preserves-set-equiv
          (implies (and (pairp ep) (lofpp l1) (lofpp l2)
                        (acl2::set-equiv (double-rewrite l1) l2))
                   (acl2::set-equiv (insert-event ep l1)
                                    (insert-event ep l2)))
          :hints (("goal" :in-theory (e/d (acl2::set-equiv) (pairp eventp natp))))))

 (local (defthm add-subset
          (implies (and (pairp ep) (lofpp l))
                   (subsetp-equal l (add-event ep l)))))

 (local (defthm add-event-member
          (implies (and (pairp ep) (lofpp l))
                   (member-equal ep (add-event ep l)))))
 
 (local (defthm add-preserves-subset
          (implies (and (pairp ep) (lofpp l1) (lofpp l2)
                        (subsetp-equal l1 l2))
                   (subsetp-equal (add-event ep l1)
                                  (add-event ep l2)))))

 (local (defthmd add-preserves-set-equiv
          (implies (and (pairp ep) (lofpp l1) (lofpp l2)
                        (acl2::set-equiv (double-rewrite l1) l2))
                   (acl2::set-equiv (add-event ep l1)
                                    (add-event ep l2)))
          :hints (("goal" :in-theory (e/d (acl2::set-equiv) (pairp eventp natp))))))

 (local (defthm add-event-cons 
          (subsetp-equal (add-event ep l)
                         (cons ep l))))

 (local (defthm insert-event-cons 
          (subsetp-equal (insert-event ep l)
                         (cons ep l))))


 (in-theory (disable ACL2::DEFAULT-LESS-THAN-1 
                     ACL2::DEFAULT-LESS-THAN-2))
 

 (local (defthmd insert-event-subset-add-event
          (implies (and (schp s)
                        (pairp ep))
                   (subsetp-equal (insert-event ep s)
                                  (add-event ep s)))
          :hints (("goal" :in-theory (e/d (subsetp-equal)
                                          ((:rewrite schp-=>setp)
                                           (:rewrite schp-car-pairp))
                                          (pairp eventp natp))))))

 (local (defthm l1
          (subsetp-equal (add-event e1 l)
                         (cons e1 (cons e2 l)))))
 
 (local (defthmd add-event-subset-insert-event
          (implies (and (schp s)
                        (pairp ep))
                   (subsetp-equal (add-event ep s)
                                  (insert-event ep s)))
          :hints (("goal" :in-theory (e/d ()
                                          (pairp eventp natp))
                   :induct (add-event ep s)))))

 (local (defthmd add-event-seteq-insert-event-1
          (implies (and (schp s)
                        (pairp ep))
                   (acl2::set-equiv (add-event ep s)
                                    (insert-event ep s)))
          :hints (("goal" :in-theory (e/d (acl2::set-equiv) (pairp schp))
                   :use ((:instance add-event-subset-insert-event)
                         (:instance insert-event-subset-add-event))))))

 (local (defthmd add-event-seteq-insert-event
          (implies (and (schp s)
                        (ischp i)
                        (acl2::set-equiv (double-rewrite i) (double-rewrite s))
                        (pairp ep))
                   (acl2::set-equiv (add-event ep s)
                                    (insert-event ep i)))
          :hints (("goal" :in-theory (e/d () (pairp ischp schp insert-event-congruence-setequal))
                   :use ((:instance add-event-seteq-insert-event-1)
                         (:instance insert-preserves-set-equiv (l1 s) (l2 i)))
                   :do-not-induct t))))

 (local (in-theory (disable insert-event-congruence-setequal add-events-congruence-setequal)))

 
 (defthmd add-events-seteq-insert-events
   (implies (and (schp s)
                 (ischp i)
                 (acl2::set-equiv (double-rewrite i) (double-rewrite s))
                 (schp l))
            (acl2::set-equiv (insert-events l i)
                             (add-events l s)))
   :hints (("goal" :in-theory (e/d ()
                                   (schp ischp pairp eventp
                                         natp add-event insert-event
                                         ))
            :induct (insert-events l i))
           ("Subgoal *1/2.1" :in-theory (disable schp ischp  pairp)
            :use ((:instance add-event-seteq-insert-event
                             (ep (car l)) (s (add-events (cdr l) s))
                             (i (insert-events (cdr l) i)))
                  (:instance add-events-contract (l (cdr l)) (E S))))))
 )
 


(skip-proofs
 (defthm igood-statep-inductive
   (implies (igood-statep s)
            (igood-statep (impl-step s)))))


(defthm valid-timestamps-cons
  (implies (and (> t1 t2)  
                (valid-timestamps E t2 f))
           (valid-timestamps (cons (cons t1 ev) E) t2 f))
  :hints (("goal" :induct (valid-timestamps E ct f)
           :in-theory (enable get-event-time))))

(defthm valid-timestamps-events-at-ct
  (implies (and (> t1 t2)
                (valid-timestamps E t1 f))
           (not (events-at-ct E t2))))

(defthm events-at-ct-cons-1
  (implies (and (not (equal t2 t1))
                (not (events-at-ct E t1)))
           (not (events-at-ct (cons (cons t2 ev) E) t1)))
    :hints (("goal" :in-theory (enable get-event-time))))


(defthm events-at-ct-cons
  (implies (and (> t2 t1)
                (valid-timestamps E t2 f))
           (not (events-at-ct (cons (cons t2 ev) E) t1)))
  :hints (("goal" :in-theory (e/d () (valid-timestamps-events-at-ct
                                      events-at-ct-cons-1))
           :use ((:instance  valid-timestamps-events-at-ct)
                 (:instance events-at-ct-cons-1)))))


;; Begin proof for B constraints.


(in-theory (enable get-event-time))

(defthm events-at-ct-top-of-queue-1
  (implies (and (orderedp E)
                (events-at-ct E ct)
                (valid-timestamps E ct nil))
           (equal (get-event-time (car E)) ct))
  :hints (("goal" :in-theory (enable e-<)
           :induct (and (orderedp E) (events-at-ct E ct)))))

(defthm events-at-ct-top-of-queue
  (implies (and (ischp E)
                (events-at-ct E ct)
                (valid-timestamps E ct nil))
           (equal (get-event-time (car E)) ct))
  :hints (("goal" :in-theory (e/d (ischp) (get-event-time)))))

(defthm no-events-at-ct-top-of-queue-1
  (implies (and (orderedp E)
                (lofpp E)
                (consp E)
                (natp ct)
                (not (events-at-ct E ct))
                (valid-timestamps E ct nil))
           (> (get-event-time (car E)) ct))
  :hints (("goal" :in-theory (enable get-event-time e-<)
           :induct (and (orderedp E) (events-at-ct E ct))))
  :rule-classes (:rewrite :linear))

(defthm no-events-at-ct-top-of-queue
  (implies (and (ischp E)
                (consp E)
                (natp ct)
                (not (events-at-ct E ct))
                (valid-timestamps E ct nil))
           (> (get-event-time (car E)) ct))
  :hints (("goal" :in-theory (e/d (ischp) (get-event-time))))
  :rule-classes (:rewrite :linear))

(defthm events-at-ct-memberp-E
  (implies (and (ischp E)
                (events-at-ct E ct)
                (valid-timestamps E ct nil))
           (acl2::member-equal  (car E) (events-at-ct E ct)))
  :hints (("goal" :in-theory (e/d (acl2::memberp-equal)
                                  (events-at-ct-top-of-queue ischp
                                   natp valid-timestamps get-event
                                   get-event-time))
           :use ((:instance events-at-ct-top-of-queue))
           :do-not-induct t)))
            
(defthm events-at-ct-memberp-E-1
  (implies (and (acl2::member-equal ep (events-at-ct E ct))
                (valid-timestamps E ct nil))
           (events-at-ct E ct))
  :hints (("goal" :in-theory (enable acl2::memberp-equal))))

(in-theory (disable get-event get-event-time istate istate-ct istate-e
                    istate-st rmv-event sstate sstate-ct sstate-e
                    sstate-st natp))


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

(defthmd B-witness-v-event-at-ct-related-to-w
  (implies (and (sstatep w)
                (events-at-ct (sstate-E w) (sstate-ct w))
                (acl2::member-equal (pick-event-pq E) (events-at-ct (sstate-E w) (sstate-ct w))))
           (spec-relation w (B-witness-v-event-at-ct (get-event (pick-event-pq E)) w)))
  :hints (("goal" :in-theory (disable exists-ev-at-ct-suff)
           :use ((:instance exists-ev-at-ct-suff (ep (pick-event-pq E)) (w w)
                            (v (B-witness-v-event-at-ct (get-event (pick-event-pq E)) w)))))))

(defthmd B-witness-v-event-at-ct-related-to-w-1
  (let* ((ev (get-event (pick-event-pq (istate-E s))))
         (v (B-witness-v-event-at-ct ev (ref-map s))))
    (implies (and (istatep s)
                  (valid-timestamps (sstate-E (ref-map s)) (sstate-ct (ref-map s)) nil)
                  (events-at-ct (sstate-E (ref-map s)) (sstate-ct (ref-map s))))
             (spec-relation (ref-map s) v)))
  :hints (("goal" :use ((:instance events-at-ct-memberp-E (E (sstate-E (ref-map s)))
                                   (ct (sstate-ct (ref-map s))) )
                        (:instance B-witness-v-event-at-ct-related-to-w
                                   (w (ref-map s)) (E (sstate-E (ref-map s)))))
           :in-theory (disable exists-ev-at-ct-suff
                               b-witness-v-event-at-ct-related-to-w
                               spec-relation
                               B-witness-v-event-at-ct
                               events-at-ct-memberp-E
                               events-at-ct-memberp-E-1))))

(defthm igood-statep-=>=valid-timestamps
  (implies (igood-statep s)
           (valid-timestamps (istate-E s) (istate-ct s) nil)))


(defthm ischp-=>-schp
  (implies (ischp x)
           (schp x))
  :rule-classes (:rewrite))

(defthm cdr-car-schp
 (implies (and (schp x)
               (consp x))
          (eventp (get-event (car x))))
 :hints (("goal" :in-theory (enable get-event ))))

(defthm car-car-schp
 (implies (and (schp x)
               (consp x))
          (natp (get-event-time (car x))))
 :hints (("goal" :in-theory (enable get-event-time ))))

      
(defthm rmv-event-pq-contract
  (implies (ischp e)
           (ischp (rmv-event-pq e)))
  :hints (("goal" :cases ((consp e))
           :in-theory (enable rmv-event-pq ischp))))

;; B-constraint in case  (events-at-ct (istate-E s) (istate-ct s))
(encapsulate
 ()
 (in-theory (enable add-events-contract))
 
 (defthmd B-constraints-1a
   (let* ((ev (get-event (pick-event-pq (istate-E s))))
          (w (ref-map s))
          (v (B-witness-v-event-at-ct ev w)))
     (implies (and (istatep s)
                   (igood-statep s)
                   (events-at-ct (istate-E s) (istate-ct s)))
              (spec-relation w v)))
   :hints (("goal" :use ((:instance B-witness-v-event-at-ct-related-to-w-1))
            :in-theory (e/d() (B-witness-v-event-at-ct
                               igood-statep
                               events-at-ct spec-relation
                               events-at-ct-memberp-E-1
                               get-event)))))

 (local (in-theory (disable events-at-ct storep eventp istate-eth igood-statep
                            istate-eh valid-timestamps RMV-EVENT-PQ SCHP ISCHP
                            events-at-ct-top-of-queue)))
 
 (local
  (defthmd B-constraints-1b-1
    (let* ((u (impl-step s))
           (ev (get-event (pick-event-pq (istate-E s))))
           (w (ref-map s))
           (v (B-witness-v-event-at-ct ev w)))
      (implies (and (istatep s)
                    (istatep u)
                    (igood-statep s)
                    (events-at-ct (istate-E s) (istate-ct s)))
               (equal (sstate-ct (ref-map u)) (sstate-ct v))))
    :hints (("goal" :in-theory (e/d () (get-event istate-evh
                                                  istate-sth
                                                  events-at-ct-top-of-queue))
             :use ((:instance events-at-ct-top-of-queue
                              (E (istate-E s)) (ct (istate-ct s))))))))

 (local
  (defthmd B-constraints-1b-2
    (let* ((u (impl-step s))
           (ev (get-event (pick-event-pq (istate-E s))))
           (w (ref-map s))
           (v (B-witness-v-event-at-ct ev w)))
      (implies (and (istatep s)
                    (istatep u)
                    (igood-statep s)
                    (CONSP (ISTATE-E s))
                    (events-at-ct (istate-E s) (istate-ct s)))
               (equal (sstate-st (ref-map u)) (sstate-st v))))
    :hints (("goal" :use ((:instance events-at-ct-top-of-queue
                                     (E (istate-E s)) (ct (istate-ct s))))))))

 (local
  (defthm l1
    (implies (and (istatep s)
                  (events-at-ct (istate-e s) (istate-ct s))
                  (valid-timestamps (istate-e s) (istate-ct s) nil))
             (equal (RMV-EVENT (CONS (ISTATE-CT S)
                                     (GET-EVENT (CAR (ISTATE-E S))))
                               (ISTATE-E S))
                    (RMV-EVENT-PQ (ISTATE-E S))))
    :hints (("goal" :in-theory (enable get-event rmv-event rmv-event-pq igood-statep get-event-time)
             :use ((:instance events-at-ct-top-of-queue
                              (E (istate-E s)) (ct (istate-ct s))))))))

 (local
  (defthmd B-constraints-1b-3
    (let* ((u (impl-step s))
           (ev (get-event (pick-event-pq (istate-E s))))
           (w (ref-map s))
           (v (B-witness-v-event-at-ct ev w)))
      (implies (and (istatep s)
                    (istatep u)
                    (igood-statep s)
                    (events-at-ct (istate-E s) (istate-ct s)))
               (acl2::set-equiv (sstate-E (ref-map u)) (sstate-E v))))
    :hints (("goal" :use ((:instance events-at-ct-top-of-queue
                                     (E (istate-E s)) (ct (istate-ct s)))
                          (:instance add-events-seteq-insert-events
                                     (l (MV-NTH 0
                                                (EXECUTE-EVENT (GET-EVENT (CAR (ISTATE-E S)))
                                                               (ISTATE-CT S)
                                                               (ISTATE-ST S))))
                                     (i (RMV-EVENT-PQ (ISTATE-E S)))
                                     (s (RMV-EVENT (CONS (ISTATE-CT S)
                                                         (GET-EVENT (CAR (ISTATE-E S))))
                                                   (ISTATE-E S)))))))))

 (local
  (defthmd B-constraints-1b
   (let* ((u (impl-step s))
          (ev (get-event (pick-event-pq (istate-E s))))
          (w (ref-map s))
          (v (B-witness-v-event-at-ct ev w)))
     (implies (and (istatep s)
                   (istatep u)
                   (igood-statep s)
                   (events-at-ct (istate-E s) (istate-ct s)))
              (B u v)))
   :hints (("goal" :in-theory (enable B)
            :use ((:instance B-constraints-1b-1)
                  (:instance B-constraints-1b-2)
                  (:instance B-constraints-1b-3))))))

 

 (defthmd B-constraints-events-at-ct
   (let* ((u (impl-step s))
          (ev (get-event (pick-event-pq (istate-E s))))
          (w (ref-map s))
          (v (B-witness-v-event-at-ct ev w)))
     (implies (and (istatep s)
                   (istatep u)
                   (igood-statep s)
                   (events-at-ct (istate-E s) (istate-ct s)))
              (and (spec-relation w v)
                   (B u v))))
   :hints (("goal" :in-theory (disable spec-relation B igood-statep
                                       B-witness-v-event-at-ct
                                       pick-event-pq impl-step)
            :use ((:instance B-constraints-1a)
                  (:instance B-constraints-1b)))))

 )


;; B-constraint in case  (not (events-at-ct (istate-E s) (istate-ct s)))

(defthmd B-witness-v-noevent-at-ct-related-to-w
  (implies (and (sstatep (ref-map s))
                (not (events-at-ct (sstate-E (ref-map s)) (sstate-ct (ref-map s)))))
           (spec-relation (ref-map s) (B-witness-v-noevent-at-ct  (ref-map s)))))


(defthm get-event-time-contract
  (implies (pairp ep)
           (natp (get-event-time ep)))
  :hints (("goal" :in-theory (enable get-event-time)))
  :rule-classes (:rewrite :forward-chaining))


(encapsulate
 ()
 
 (local (in-theory (disable events-at-ct storep eventp istate-eth
                            igood-statep istate-eh valid-timestamps
                            RMV-EVENT-PQ SCHP ISCHP
                            events-at-ct-top-of-queue-1
                            events-at-ct-top-of-queue
                            no-events-at-ct-top-of-queue-1
                            no-events-at-ct-top-of-queue)))

 (local
  (defthm bla-1
    (implies (and (natp t1) (natp t2) (< t1 t2))
             (<= (1+ t1) t2))))

 

 (local (in-theory (disable (:rewrite acl2::default-less-than-1)
                            (:rewrite acl2::default-less-than-2))))

 (local (defthm l1
          (let* ((u (impl-step s)))
            (implies (and (istatep s)
                          (igood-statep s)
                          (not (events-at-ct (istate-E s) (istate-ct s))))
                     (<= (1+ (istate-ct s)) (istate-ct u))))
          :hints (("goal" :cases ((consp (istate-E s)))
                   :in-theory (e/d () (igood-statep))
                   :use ((:instance no-events-at-ct-top-of-queue
                                    (E (istate-E s)) (ct (istate-ct s))))))))
 (local
  (defthmd B-constraints-1b-1
    (let* ((u (impl-step s))
           (w (ref-map s))
           (v (B-witness-v-noevent-at-ct w)))
      (implies (and (istatep s)
                    (igood-statep s)
                    (not (events-at-ct (istate-E s) (istate-ct s))))
               (<= (sstate-ct v) (istate-ct u))))
    :hints (("goal" :cases ((consp (istate-E s)))
             :in-theory (e/d () (igood-statep impl-step)))
            ("subgoal 1.2.2" :use ((:instance l1))))))

 
 (local 
  (defthmd B-constraints-1b-2
    (let* ((u (impl-step s))
           (w (ref-map s))
           (v (B-witness-v-noevent-at-ct w)))
      (implies (and (istatep s)
                    (igood-statep s)
                    (not (events-at-ct (istate-E s) (istate-ct s))))
               (equal (sstate-st v) (istate-sth u))))
    :hints (("goal" :use ((:instance no-events-at-ct-top-of-queue
                                     (E (istate-E s)) (ct (istate-ct s))))
             :in-theory (disable sstate-st istate-sth no-events-at-ct-top-of-queue)))))


 (local
  (defthmd B-constraints-1b-3
    (let* ((u (impl-step s))
           (w (ref-map s))
           (v (B-witness-v-noevent-at-ct w)))
      (implies (and (istatep s)
                    (igood-statep s)
                    (not (events-at-ct (istate-E s) (istate-ct s))))
               (and (acl2::set-equiv (sstate-E v) (istate-Eh u)))))
    :hints (("goal" :use ((:instance no-events-at-ct-top-of-queue
                                     (E (istate-E s)) (ct (istate-ct s))))
             :in-theory (disable sstate-E  no-events-at-ct-top-of-queue)))))

  (local (defthmd l2
          (implies (and (orderedp E) (lofpp E)
                        (consp E)
                        (>= (get-event-time (car E)) ct))
                   (valid-timestamps E ct nil))
            :hints (("goal" :in-theory (enable e-< valid-timestamps)
           :induct (and (orderedp E) (valid-timestamps E ct nil))))))

 (local
  (defthm B-constraints-1b-4
    (let* ((u (impl-step s))
           (w (ref-map s))
           (v (B-witness-v-noevent-at-ct w)))
      (implies (and (istatep s)
                    (igood-statep s)
                    (not (events-at-ct (istate-E s) (istate-ct s))))
               (valid-timestamps (sstate-E v) (istate-ct u) nil)))
    :hints (("goal" :in-theory (enable valid-timestamps igood-statep)
             :use ((:instance l2 (E (istate-E s)) (ct (GET-EVENT-TIME (CAR (ISTATE-E S))))))))))


(local
  (defthmd B-constraints-1b-5
   (let* ((w (ref-map s))
          (v (B-witness-v-noevent-at-ct w)))
     (implies (and (istatep s)
                   (igood-statep s)
                   (not (events-at-ct (istate-E s) (istate-ct s))))
              (spec-relation w v)))))



 (defthmd B-constraints-noevents-at-ct
   (let* ((u (impl-step s))
          (w (ref-map s))
          (v (B-witness-v-noevent-at-ct w)))
     (implies (and (istatep s)
                   (igood-statep s)
                   (not (events-at-ct (istate-E s) (istate-ct s))))
              (and (spec-relation w v)
                   (C u v))))
   :hints (("goal" :in-theory (disable spec-relation B igood-statep
                                       B-witness-v-noevent-at-ct
                                       pick-event-pq impl-step)
            :use ((:instance B-constraints-1b-1)
                  (:instance B-constraints-1b-2)
                  (:instance B-constraints-1b-3)
                  (:instance B-constraints-1b-4)
                  (:instance B-constraints-1b-5)))))
 )


;; B-constraints end

;;; begin proof for C constrains
   

(defthm
  member-equal-set-equiv
  (implies (acl2::set-equiv acl2::a acl2::b)
           (iff (member-equal acl2::x acl2::a)
                (member-equal acl2::x acl2::b)))
  :rule-classes nil
  :hints
  (("goal" :do-not-induct t
    :in-theory (enable acl2::set-equiv acl2::memberp-equal)
    ;;TODO possibly the hints belowcan be removed
    :use ((:instance acl2::memberp-equal-subsetp-equal ;; 
                     (acl2::x acl2::x)
                     (acl2::a acl2::a)
                     (acl2::b acl2::b))
          (:instance acl2::memberp-equal-subsetp-equal
                     (acl2::x acl2::x)
                     (acl2::a acl2::b)
                     (acl2::b acl2::a))))))

(encapsulate
 ()

  (local 
   (defthm ep-in-events-at-ct
    (acl2::member-equal (cons ct ev)
                         (events-at-ct (cons (cons ct ev) E) ct))
    :hints (("goal" :in-theory (enable  events-at-ct get-event get-event-time)
             :induct (events-at-ct E ct)))))

 (defthm ep-in-events-at-ct-1
   (implies (acl2::member-equal (cons ct ev) E)
            (acl2::member-equal (cons ct ev) (events-at-ct E ct)))
   :hints (("goal" :in-theory (enable  events-at-ct get-event get-event-time)
            :induct (events-at-ct E ct))))

 (local (defthm memberp-=>-not-nil
          (implies (acl2::member-equal x l)
                   l)
          ;; :hints (("goal" :in-theory (enable acl2::memberp-equal)))
  :rule-classes ()))

 (local (in-theory (disable get-event get-event-time istate istate-ct
                            istate-e istate-st rmv-event sstate
                            sstate-ct sstate-e sstate-st natp istate
                            istate-ct istate-E istate-Eh istate-eth
                            istate-evh istate-st e-<-transitivity
                            e-<-not-reflexive e-<-asymmetric
                            e-<-trichotomy
                            no-events-at-ct-top-of-queue
                            insert-event-congruence-setequal )))



 (local
  (defthm event-at-ct-in-y-lemma
    (let ((eph (cons ct (istate-evh x))))
      (implies (and (istatep x)
                    (acl2::member-equal eph (istate-Eh x)) ;; from igood-statep
                    (sstatep y)
                    (acl2::set-equiv (sstate-E y) (istate-Eh x))) ;; from C
               (events-at-ct (sstate-E y) ct)))
    :hints (("goal" :in-theory (disable  ep-in-events-at-ct-1 istate-Eh)
             :use ((:instance member-equal-set-equiv
                              (a (sstate-E y)) (b (istate-Eh x))
                              (x (cons ct (istate-evh x))))
                   (:instance ep-in-events-at-ct-1
                              (E (sstate-E y))
                              (ev (istate-evh x))
                              (ct ct))
                   (:instance memberp-=>-not-nil
                              (x (istate-evh x))
                              (l (events-at-ct (sstate-E y) ct)))))))
  )

 

 (local (defthm igood-statep=>memberp
          (implies (igood-statep x)
                   (acl2::member-equal (cons (istate-eth x) (istate-evh x)) (istate-Eh x)))))

 (local (defthm igood-statep=>eth=ct
          (implies (igood-statep x)
                   (equal (istate-eth x) (istate-ct x)))))
 
 (local (defthm c-E-setequal
          (implies (and (C x y) (not (B x y)))
                   (acl2::set-equiv (sstate-E y) (istate-Eh x)))))

 (defthm event-at-ct-in-y
   (implies (and (istatep x)
                 (igood-statep x)
                 (sstatep y)
                 (C x y)
                 (not (B x y))
                 (equal (istate-ct x) (sstate-ct y))) 
            (events-at-ct (sstate-E y) (sstate-ct y)))
   :hints (("goal" :in-theory (disable B C 
                                       c-E-setequal igood-statep
                                       igood-statep=>eth=ct
                                       igood-statep=>memberp
                                       ACL2::SET-EQUAL-REFLEXIVE)
            :use ((:instance event-at-ct-in-y-lemma (ct (istate-eth x)))
                  (:instance c-E-setequal)
                  (:instance igood-statep=>eth=ct)
                  (:instance igood-statep=>memberp)))))
 )


(defun witness-x-ct=y-ct (x y)
;   (declare (xargs :guard (and (istatep x) (sstatep y))))
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


(encapsulate
 ()
  (local (in-theory (disable get-event get-event-time istate istate-ct
                            istate-e istate-st rmv-event sstate ischp
                            schp sstate-ct sstate-e sstate-st natp
                            istate istate-ct istate-E istate-Eh
                            istate-eth istate-evh istate-st
                            e-<-transitivity e-<-not-reflexive
                            e-<-asymmetric e-<-trichotomy
                            no-events-at-ct-top-of-queue
                            insert-event-congruence-setequal)))

 (local
  (defthmd c-spec-relation-2b-1-lemma
    (implies (and (istatep x)
                  (igood-statep x)
                  (sstatep y)
                  (acl2::set-equiv (sstate-E y) (istate-Eh x))
                  (equal (istate-ct x) (sstate-ct y)))
             (acl2::member-equal (cons (istate-eth x) (istate-evh x)) (events-at-ct (sstate-E y) (sstate-ct y))))
    :hints (("goal" :in-theory (e/d () (B events-at-ct exists-ev-at-ct
                                          istate-Eh istate-Evh istate-sth
                                          rmv-event))
             :use ((:instance member-equal-set-equiv
                              (a (sstate-E y)) (b (istate-Eh x))
                              (x (cons (sstate-ct y) (istate-evh x))))
                   (:instance ep-in-events-at-ct-1
                              (E (sstate-E y))
                              (ev (istate-evh x))
                              (ct (sstate-ct y)))))))
  )


 (local (defthm igood-statep=>eth=ct
          (implies (igood-statep x)
                   (equal (istate-eth x) (istate-ct x)))))

 (local (defthm igood-statep=>memberp
          (implies (igood-statep x)
                   (member-equal (cons (istate-eth x) (istate-evh x)) (istate-Eh x)))))
 
 (local (defthm c-E-setequal
          (implies (and (C x y) (not (B x y)))
                   (acl2::set-equiv (sstate-E y) (istate-Eh x)))))

 (local
  (defthm c-spec-relation-2b-1
    (implies (and (istatep x)
                  (igood-statep x)
                  (sstatep y)
                  (C x y)
                  (not (B x y))
                  (equal (istate-ct x) (sstate-ct y)))
             (member-equal (cons (sstate-ct y) (istate-evh x)) (events-at-ct (sstate-E y) (sstate-ct y))))
    :hints (("goal" :in-theory (disable B C 
                                       c-E-setequal igood-statep
                                       igood-statep=>memberp
                                       c-spec-relation-2b-1-lemma
                                       ACL2::SET-EQUAL-REFLEXIVE)
            :use ((:instance c-spec-relation-2b-1-lemma)
                  (:instance c-E-setequal)
                  (:instance igood-statep=>memberp))))))

 (local (defthm bla
          (equal (get-event (cons ct ev))
                 ev)
          :hints (("goal" :in-theory (enable get-event)))))
 
 (local
  (defthmd c-spec-relation-2b-2
    (implies (and (istatep x)
                  (igood-statep x)
                  (sstatep y)
                  (equal (istate-ct x) (sstate-ct y)))
             (mv-let (new-evs up-st)
                     (execute-event (get-event (cons (sstate-ct y) (istate-evh x)))
                                               (sstate-ct y) (sstate-st y))
                     (let* ((up-e (rmv-event (cons (sstate-ct y) (istate-evh x)) (sstate-E y)))
                            (up-e (add-events new-evs up-e)))
                       (equal (witness-x-ct=y-ct x y)
                              (sstate (sstate-ct y) up-e up-st)))))))

 
 (local
  (defthmd c-spec-relation-2b-3
    (implies (and (istatep x)
                  (igood-statep x)
                  (sstatep y)
                  (C x y)
                  (not (B x y))
                  (equal (istate-ct x) (sstate-ct y)))
             (exists-ev-at-ct y (witness-x-ct=y-ct x y)))
    :hints (("goal" :in-theory (disable exists-ev-at-ct-suff exists-ev-at-ct
                                        witness-x-ct=y-ct
                                        ACL2::SUBSETP-EQUAL-REFLEXIVE
                                        ACL2::SUBSETP-MEMBER
                                        c-spec-relation-2b-1 igood-statep sstatep istatep
                                        c-spec-relation-2b-2 B sstate-ct istate-ct
                                        istate-Eh C)
             :use ((:instance c-spec-relation-2b-2)
                   (:instance c-spec-relation-2b-1)
                   (:instance exists-ev-at-ct-suff
                              (ep (cons (sstate-ct y) (istate-evh x)))
                              (w y) (v (witness-x-ct=y-ct x y))))))))


 (defthmd c-spec-relation-2b
   (implies (and (istatep x)
                 (igood-statep x)
                 (sstatep y)
                 (C x y)
                 (not (B x y))                
                 (equal (istate-ct x) (sstate-ct y)))
            (spec-relation y (witness-x-ct=y-ct x y)))
   :hints (("goal" :in-theory (disable exists-ev-at-ct-suff exists-ev-at-ct
                                       igood-statep sstatep istatep
                                       B sstate-ct istate-ct
                                       istate-Eh C)
            :use ((:instance c-spec-relation-2b-3)
                  (:instance event-at-ct-in-y)))))


 )

;; Case y.ct < x.ct

(defun witness-y-ct<-x-ct (y)
    (declare (xargs :guard (sstatep y)))
    (let* ((z-ct (sstate-ct y))
           (z-E (sstate-E y))
           (z-st (sstate-st y))
           (z (sstate (1+ z-ct) z-E z-st)))
      z))


;; TODO: takes lot of time  53+ seconds
(defthmd spec-relation-no-event-at-ct
  (implies (and (istatep x)
                (igood-statep x)
                (sstatep y)
                (sgood-statep y)
                (not (events-at-ct (sstate-E y) (sstate-ct y)))
                (C x y))
            (spec-relation y (witness-y-ct<-x-ct y))))
 
;; xCz holds
(defthmd c-witness-x-ct<-y-ct
  (implies (and (istatep x)
                (igood-statep x)
                (sstatep y)
                (C x y)
                (not (B x y))                
                (< (sstate-ct y) (istate-ct x)))
           (C x (witness-y-ct<-x-ct  y)))
  :hints (("goal" :in-theory (disable igood-statep sstatep istatep B ref-map istate-Eh))))


(encapsulate
 ()

 (local (defthmd l1
          (implies (and (acl2::setp-equal l) (acl2::setp-equal l-equiv)
                        (acl2::set-equiv l l-equiv))
                   (acl2::set-equiv (rmv-event (car l) l-equiv)
                                    (rmv-event (car l) l)))
          :hints (("goal" :use ((:instance rmv-event-congruence-setequiv
                                           (ep (car l)) (E1 l) (E2 l-equiv)))))))

 (local (defthmd l2
          (implies (and (acl2::setp-equal l) (acl2::setp-equal l-equiv)
                        (acl2::set-equiv l l-equiv))
                   (acl2::set-equiv (rmv-event (car l) l-equiv)
                                    (cdr l)))
          :hints (("goal" :in-theory (enable rmv-event)
                   :use ((:instance l1))))))
          
 (defthmd xlemma-6
   (implies (and (istatep x) (sstatep y) (schp l)
                 (acl2::set-equiv (sstate-E y) (istate-eh x)))
            (acl2::set-equiv (add-events l (rmv-event (car (istate-eh x)) (sstate-E y)))
                             (insert-events l (cdr (istate-eh x)))))
   :hints (("goal" :use
            ((:instance l2 (l (istate-eh x)) (l-equiv (sstate-E y)))
             (:instance add-events-seteq-insert-events
                        (i (cdr (istate-eh x)))
                        (s (rmv-event (car (istate-eh x)) (sstate-E y))) (l l))
             (:instance schp-car-pairp (l (istate-eh x))))
            :in-theory (e/d (add-events-contract insert-events-contract )
                            (add-events-congruence-setequal
                             add-events insert-events istate-eh  schp-car-pairp)))))
 )
    

(encapsulate
 ()
(in-theory (disable get-event get-event-time istate istate-ct istate-e
                            istate-st rmv-event sstate sstate-ct
                            sstate-e sstate-st natp istate istate-ct
                            istate-E istate-Eh istate-eth istate-evh
                            istate-st istate-sth e-<-transitivity
                            e-<-not-reflexive e-<-asymmetric
                            e-<-trichotomy
                            no-events-at-ct-top-of-queue
                            insert-event-congruence-setequal e-<
                            eventp ischp storep insert-events-contract
                            ischp-=>-schp schp))

;; very fragile 
(local (defthmd c-witness-x-ct-=-y-ct
  (implies (and (istatep x)
                (igood-statep x)
                (sstatep y)
                (C x y)
                (not (B x y))                
                (equal (sstate-ct y) (istate-ct x)))
           (B x (witness-x-ct=y-ct x y)))
  :hints (("goal" :in-theory (disable sstatep istatep ref-map ischp
                                       istate-Eh schp
                                       execute-event-contract))
          ("subgoal 6" :in-theory (disable add-events-contract)
           :use ((:instance add-events-contract
                            (l (mv-nth 0 (execute-event (istate-evh x)
                                                        (istate-ct x) (istate-sth x))))
                            (E (rmv-event (car (istate-eh x)) (sstate-e y))))
                 (:instance execute-event-contract (ev (istate-evh x)) (ct (istate-ct x))
                            (st (istate-sth x)))))
          ("subgoal 5" :in-theory (disable add-events-contract)
           :use ((:instance add-events-contract
                            (l (mv-nth 0 (execute-event (istate-evh x)
                                                        (istate-ct x) (istate-sth x))))
                            (E (rmv-event (car (istate-eh x)) (sstate-e y))))
                 (:instance execute-event-contract (ev (istate-evh x)) (ct (istate-ct x))
                            (st (istate-sth x)))
                 (:instance xlemma-6
                            (l (mv-nth 0 (execute-event (istate-evh x)
                                                        (istate-ct x) (istate-sth x)))))))
          ("subgoal 4":in-theory (disable add-events-contract execute-event-contract)
           :use ((:instance add-events-contract
                            (l (mv-nth 0 (execute-event (istate-evh x)
                                                        (istate-ct x) (istate-sth x))))
                            (E (rmv-event (car (istate-eh x)) (sstate-e y))))
                 (:instance execute-event-contract (ev (istate-evh x)) (ct (istate-ct x))
                            (st (istate-sth x)))))
          ("subgoal 3":in-theory (disable add-events-contract execute-event-contract)
           :use ((:instance add-events-contract
                            (l (mv-nth 0 (execute-event (istate-evh x)
                                                        (istate-ct x) (istate-sth x))))
                            (E (rmv-event (car (istate-eh x)) (sstate-e y))))
                 (:instance execute-event-contract (ev (istate-evh x)) (ct (istate-ct x))
                            (st (istate-sth x)))))
          ("subgoal 2" :in-theory (disable add-events-contract)
           :use ((:instance add-events-contract
                            (l (mv-nth 0 (execute-event (istate-evh x)
                                                        (istate-ct x) (istate-sth x))))
                            (E (rmv-event (car (istate-eh x)) (sstate-e y))))
                 (:instance execute-event-contract (ev (istate-evh x)) (ct (istate-ct x))
                            (st (istate-sth x)))
                 (:instance xlemma-6
                            (l (mv-nth 0 (execute-event (istate-evh x)
                                                        (istate-ct x) (istate-sth x)))))))
          ("subgoal 1":in-theory (disable add-events-contract execute-event-contract)
           :use ((:instance add-events-contract
                            (l (mv-nth 0 (execute-event (istate-evh x)
                                                        (istate-ct x) (istate-sth x))))
                            (E (rmv-event (car (istate-eh x)) (sstate-e y))))
                 (:instance execute-event-contract (ev (istate-evh x)) (ct (istate-ct x))
                            (st (istate-sth x))))))))


;; (encapsulate
;;  ()
;;  (local (in-theory (enable valid-timestamps)))

 (local
  (defthm valid-timestamps-cons2 
    (implies (valid-timestamps (cons ep E) ct f)
             (and (valid-timestamps E ct f)
                  (>= (get-event-time ep) ct)))))

 (local (defthmd valid-timestamps-add-event-1
          (implies (and (schp E) (booleanp f)
                        (valid-timestamps E t2 nil)
                        (>= t1 t2))
                   (valid-timestamps (add-event (cons t1 ev) E) t2 nil))
          :hints (("goal" :in-theory (enable get-event-time get-event)))))

 (local (in-theory (disable schp)))
 
 (local (defthmd induction-hyps-lemma-1
          (implies (and (schp E)
                        (schp x) 
                        (booleanp f) (natp t1) (natp t2) (pairp ep)
                        (valid-timestamps (add-events x E) t2 f)
                        (> (get-event-time ep) t2))
                   (valid-timestamps (add-event ep (add-events x E)) t2 f))
          :hints (("goal" :use ((:instance valid-timestamps-add-event-1 (E (add-events x E))))
                   :in-theory (enable get-event-time)))))

 (local (defthmd valid-timestamps-add-events
          (implies (and (booleanp f) (schp l) (schp E)
                        (valid-timestamps l t1 f)
                        (valid-timestamps E t2 f)
                        (natp t1) (natp t2)
                        (> t1 t2))
                   (valid-timestamps (add-events l E) t2 f))
          :hints (("goal" :induct (add-events l E))
                  ("Subgoal *1/2.1.1" :use ((:instance induction-hyps-lemma-1
                                                       (x l2) (E E) (ep l1) (t2 t2) (f f))
                                            (:instance valid-timestamps-cons2
                                                       (ep l1) (E l2) (ct t1))
                                            (:instance schp-car-pairp (l (cons l1 l2))))
                   :in-theory (disable pairp induction-hyps-lemma-1 valid-timestamps-cons2)))))


  (local (defthmd valid-timestamps-subsetp
           (implies (and (acl2::subsetp-equal vq uq)
                         (valid-timestamps uq ct f))
                    (valid-timestamps vq ct f))
           :hints (("goal" :in-theory (enable acl2::subsetp-equal)))))


 (local (defthmd l1
          (implies (and (sstatep y)
                        (valid-timestamps (sstate-E y) (sstate-ct y) f))
                   (valid-timestamps (rmv-event ev (sstate-E y)) (sstate-ct y) f))
          :hints (("goal" :use ((:instance rmv-event-subset-eq)
                                (:instance valid-timestamps-subsetp
                                           (vq (rmv-event ev (sstate-E y)))
                                           (uq (sstate-E y))
                                           (ct (sstate-ct y))))))))
           
 (local (defthmd l2
          (implies (and (natp ct) (schp E))
                   (equal (valid-timestamps E ct t)
                          (valid-timestamps E (1+ ct) nil)))
          :hints (("goal" :induct (lofpp E)
                   :in-theory (enable e-< valid-timestamps get-event-time)))))

 (local (defthmd valid-timestamps-add-events-1
          (let ((l (mv-nth 0 (execute-event (istate-evh x)
                                            (sstate-ct y) (sstate-st y))))
                (E (rmv-event (car (istate-eh x)) (sstate-E y)))
                (t2 (sstate-ct y)))
            (implies (and (istatep x)
                          (sstatep y)
                          (valid-timestamps l (1+ (sstate-ct y)) nil )
                          (valid-timestamps E t2 nil))
                     (valid-timestamps (add-events l E) t2 nil)))
          :hints (("goal" :use ((:instance valid-timestamps-add-events
                                           (l (mv-nth 0 (execute-event (istate-evh x)
                                                                       (sstate-ct y) (sstate-st y))))
                                           (E (rmv-event (car (istate-eh x)) (sstate-E y)))
                                           (t2 (sstate-ct y))
                                           (t1 (1+ (sstate-ct y)))
                                           (f nil)))
                   :in-theory (disable eventp ischp
                                       valid-timestamps-add-events storep
                                       acl2::default-plus-2)))))

 (local (defthm igood-statep-car-Eh
          (implies (igood-statep s)
           (equal (car (istate-eh s))
                  (cons (istate-eth s) (istate-evh s))))
          :hints (("goal" :in-theory (enable igood-statep)))))

 ;; C-witness valid-timestamps condition

 (local (in-theory (enable l1)))
 (local (defthmd c-witness-x-ct-=-y-ct-valid-timestamp
   (implies (and (istatep x)
                 (igood-statep x)
                 (sstatep y)
                 (sgood-statep y)
                 (C x y)
                 (not (B x y))                
                 (equal (sstate-ct y) (istate-ct x)))
            (valid-timestamps (sstate-E (witness-x-ct=y-ct x y)) (istate-ct x) nil))
   :hints (("goal" :in-theory (e/d (sgood-statep witness-x-ct=y-ct)
                                   (istate-ct igood-statep C B
                                              ISTATEP-IMPLIES-CONSP
                                              SSTATEP-IMPLIES-CONSP
                                              sstate-ct istate-ct
                                              sstate-E sstate-st eventp
                                              ischp storep istate-eth
                                              istate-evh
                                              execute-event-contract
                                              igood-statep-car-Eh
                                              )))
           ("goal''"
            :use ((:instance valid-timestamps-add-events-1)
                  (:instance execute-event-contract
                             (ev (istate-evh x)) (ct (sstate-ct y)) (st (sstate-st y)))
                  (:instance l2
                             (E (mv-nth 0 (execute-event (istate-evh x)
                                                         (sstate-ct y) (sstate-st y))))
                             (ct (sstate-ct y)))))
           ("subgoal 2"
            :use ((:instance igood-statep-car-Eh (s x)))))))


(local (defthmd c-witness-x-ct-=-y-ct-final
   (implies (and (istatep x)
                 (igood-statep x)
                 (sstatep y)
                 (sgood-statep y)
                 (C x y)
                 (not (B x y))                
                 (equal (sstate-ct y) (istate-ct x)))
            (C x (witness-x-ct=y-ct x y)))
   :hints (("goal" :use ((:instance c-witness-x-ct-=-y-ct-valid-timestamp)
                         (:instance c-witness-x-ct-=-y-ct))
            :in-theory (disable istatep igood-statep sstatep sgood-statep B sstate-ct istate-ct)))))
             

(local (defthm case-exhaustive
  (implies (and (istate-ct x) (sstate-ct y)
                (C x y)
                (not (B x y)))
           (<= (sstate-ct y) (istate-ct x)))
  :hints (("goal" :in-theory (disable B)))))

(defthmd c-constraints-1
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
  :hints (("goal" :cases ((< (sstate-ct y) (istate-ct x)) (= (sstate-ct y) (istate-ct x)))
           :use ((:instance case-exhaustive)
                 (:instance c-witness-x-ct-=-y-ct-final)
                 (:instance c-witness-x-ct<-y-ct))
           :in-theory (disable sgood-statep igood-statep sstatep
                               istatep B ref-map istate-Eh istate-sth
                               witness-x-ct=y-ct
                               witness-y-ct<-x-ct))))
)

;; begin rankls

;; ;; next we show that rankls decreases.  Note that we only need to show
;; ;; this incase of xBy does not hold.

(encapsulate
 ()
 (local (in-theory (enable get-event-time rmv-event valid-timestamps)))

 (local (in-theory (enable (:rewrite acl2::default-less-than-1)
                           (:rewrite acl2::default-less-than-2))))

 (local (defthm  l1
   (<= (len (events-at-ct (rmv-event (cons ct ev) E) ct))
       (len (events-at-ct E ct)))))

 
 (local (defthm l2
   (implies (> t1 t2)
            (= (len (events-at-ct (add-event (cons t1 ev) E) t2))
               (len (events-at-ct E t2))))))

 
 (local (defthm rmv-event-len-decrease
          (<= (len (rmv-event ev E))
              (len E))
          :rule-classes :linear))

 (local (defthm l3a
   (implies (member-equal ep l)
            (< (len (rmv-event ep l))
               (len l)))))

 (local (defthm l3b
   (equal (events-at-ct (rmv-event ep E) ct)
          (rmv-event ep (events-at-ct E ct)))
   :hints (("goal" :do-not '(generalize)))))

 (local (defthm l3
   (implies (member-equal ep (events-at-ct E ct))
            (< (len (events-at-ct (rmv-event ep E) ct))
               (len (events-at-ct E ct))))
   :hints (("goal" :in-theory (disable member-equal l3a l3b
                                       acl2::subsetp-equal-reflexive
                                       (:rewrite acl2::subsetp-member . 1)
                                       (:rewrite acl2::subsetp-refl)
                                       (:type-prescription member-equal))
            :use ((:instance l3b)
                  (:instance l3a (l  (events-at-ct E ct)) (ep ep)))))))
 
 (local (defthm l4
   (implies (and (natp t1) (natp t2)
                 (valid-timestamps l t1 nil)
                 (> t1 t2))
            (= (len (events-at-ct (add-events l E) t2))
               (len (events-at-ct E t2))))))
                 
 (local (defthm l5
   (implies (and (natp t1) (natp t2)
                 (valid-timestamps l t1 nil)
                 (> t1 t2))
            (<= (len (events-at-ct (add-events l (rmv-event (cons t2 ev) E)) t2))
                (len (events-at-ct E t2))))))

 (local (defthm l6
   (implies (and (natp t1) (natp t2)
                 (valid-timestamps l t1 nil)
                 (member-equal ep (events-at-ct E t2))
                 (> t1 t2))
            (< (len (events-at-ct (add-events l (rmv-event ep E)) t2))
               (len (events-at-ct E t2))))))

 ;; BOZO: fix the definition of execute-event to use (1+ ct) and
 ;; remove the flag in valid-timestamps then I can get rid of this lemma
  (local (defthmd l7
                 (implies (and (natp ct) (schp E))
                   (equal (valid-timestamps E ct t)
                          (valid-timestamps E (1+ ct) nil)))
          :hints (("goal" :induct (lofpp E)
                   :in-theory (enable e-< valid-timestamps get-event-time)))))

  (local (defthm l8
   (implies (and (natp t2)
                 (schp l)
                 (valid-timestamps l t2 t)
                 (member-equal ep (events-at-ct E t2)))
            (< (len (events-at-ct (add-events l (rmv-event ep E)) t2))
               (len (events-at-ct E t2))))
   :hints (("goal" :in-theory (disable schp natp)
            :use ((:instance l7 (E l)
                             (ct t2))
                  (:instance l6 (t1 (1+ t2))))
            :do-not-induct t))))

 (local (defthm igood-statep-car-Eh
          (implies (igood-statep s)
           (equal (car (istate-eh s))
                  (cons (istate-eth s) (istate-evh s))))
          :hints (("goal" :in-theory (enable igood-statep)))))

 (local (defthm igood-statep-member
          (implies (igood-statep x)
                   (member-equal (cons (istate-eth x) (istate-evh x)) (istate-Eh x)))))
 
 (local (defthm igood-statep-eth
          (implies (igood-statep x)
                   (equal (istate-eth x) (istate-ct x)))))
 
 (local (defthm l9
          (implies (member-equal (cons ct ev) E)
            (member-equal (cons ct ev) (events-at-ct E ct)))))

 ;; In this case the number of events scheduled to execute at ct
;; decreases
(local (defthmd rankls-witness-x-ct=-y-ct
  (implies (and (istatep x)
                (igood-statep x)
                (sstatep y)
                (C x y)
                (not (B x y))
                (= (sstate-ct y) (istate-ct x)))
           (< (rankls (witness-x-ct=y-ct x y) x)
              (rankls y x)))
  :hints (("goal" :use ((:instance l8
                                   (l (mv-nth 0 (execute-event (istate-evh x) (sstate-ct y) (sstate-st y))))
                                    (t2 (istate-ct x))
                                   (ep (cons (istate-eth x) (istate-evh x)))
                                   (E (sstate-E y)))
                        (:instance l9
                                   (ct (istate-eth x)) (ev (istate-evh x)) (E (istate-E y)))
                        (:instance igood-statep-member))
           :in-theory (disable igood-statep istatep
                               igood-statep-member l1 l2 l3 l4 l5 l6
                               l7 l8 l9 sstatep B sstate-ct istate-ct)))))


(local (defthmd rankls-witness-y-ct<-x-ct
  (implies (and (istatep x)
                (igood-statep x)
                (sstatep y)
                (C x y)
                (not (B x y))
                (< (sstate-ct y) (istate-ct x)))
           (< (rankls (witness-y-ct<-x-ct y) x)
              (rankls y x)))
  :hints (("goal" :in-theory (disable istatep igood-statep sstatep  B sstate-ct istate-ct)))))

             

(local (defthm case-exhaustive
  (implies (and (istate-ct x) (sstate-ct y)
                (C x y)
                (not (B x y)))
           (<= (sstate-ct y) (istate-ct x)))
  :hints (("goal" :in-theory (disable B)))))

(defthmd c-constraints-2
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
  :hints (("goal" :cases ((< (sstate-ct y) (istate-ct x)) (= (sstate-ct y) (istate-ct x)))
           :use ((:instance case-exhaustive)
                 (:instance rankls-witness-y-ct<-x-ct)
                 (:instance rankls-witness-x-ct=-y-ct))
           :in-theory (disable sgood-statep igood-statep sstatep
                               istatep B ref-map istate-Eh istate-sth
                               witness-x-ct=y-ct
                               witness-y-ct<-x-ct rankls))))

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
  :hints (("goal" :use ((:instance c-constraints-1)
                        (:instance c-constraints-2))
           :in-theory (disable sgood-statep igood-statep sstatep
                               istatep B C ref-map istate-Eh istate-sth
                               witness-x-ct=y-ct
                               witness-y-ct<-x-ct rankls))))
)



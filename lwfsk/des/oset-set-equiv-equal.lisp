(in-package "ACL2S")
;; The following proof follows the strategy developed in std/oset. We
;; include the books to reason about sets and therefore omit some of
;; the lemmas in the oset-books.

(encapsulate
 nil
(local (in-theory (disable te-< te-<-definition-rule)))
(local (in-theory (enable o-lo-tep-definition-rule)))

 (local (defthm head-tail-order-contrapositive
          (implies (and (o-lo-tep X)
                        (not (te-< (car X) (car (cdr X)))))
                   (endp (cdr X)))))

 (local (defthm head-minimal-2
          (implies (and (o-lo-tep X) (timed-eventp a)
                        (member-equal a X))
                   (not (te-< a (car X))))
          :hints(("Goal"
                  :in-theory (enable member-equal)))))

 (local (defthm empty-subset
          (implies (endp X)
                   (subsetp-equal X Y))))

 (local (defthm empty-subset-2
          (implies (endp Y)
                   (equal (subsetp-equal X Y)
                          (endp X)))))

 (local (defthm in-tail-expand
          (implies (o-lo-tep X)
                   (iff (member-equal a (cdr X))
                        (and (member-equal a X)
                             (not (equal a (car X))))))))

 (local (defthm head-minimal
          (implies (and (o-lo-tep X) (timed-eventp a)
                        (te-< a (car X)))
                   (not (member-equal a X)))
          :hints(("Goal"
                  :in-theory (enable member-equal)))))

 (local (defthm subset-membership-tail
          (implies (and (o-lo-tep X) (o-lo-tep Y)
                        (subsetp-equal X Y)
                        (member-equal a (cdr X)))
                   (member-equal a (cdr Y)))))

 (local (defthmd double-containment-lemma-head
          (implies (and (o-lo-tep X) (o-lo-tep Y)
                        (subsetp-equal X Y)
                        (subsetp-equal Y X))
                   (equal (car X) (car Y)))
          :hints (("Goal" 
                   :in-theory (enable subsetp-equal)))))

 (local (defthmd double-containment-lemma-in-tail
          (implies (and (o-lo-tep X)
                        (o-lo-tep Y)
                        (subsetp-equal X Y)
                        (subsetp-equal Y X))
                   (implies (member-equal a (cdr X))   ; could be "equal" instead,
                            (member-equal a (cdr Y)))) ; but that makes loops.
          :hints(("Goal" :in-theory (enable subsetp-equal)
                  :use ((:instance in-tail-expand (a a) (X X))
                        (:instance in-tail-expand (a a) (X Y)))))))

 (local (defthm head-unique
          (implies (o-lo-tep X)
                   (not (member-equal (car X) (cdr X))))
          :hints(("Goal"
                  :in-theory (enable member-equal)))))

 (local (defthm head-not-in-tail
          (implies  (o-lo-tep (cons x1 x2))
                    (not (member-equal x1 x2)))
          :hints (("Goal" :in-theory (disable head-unique)
                   :use ((:instance head-unique (X (cons x1 x2))))))))

 (local (in-theory (enable double-containment-lemma-in-tail)))

 (local (defthm x1
          (implies (and (subsetp-equal x (cons a y))
                        (not (member-equal  a x)))
                   (subsetp-equal x y))
          :hints(("Goal" :in-theory (e/d (subsetp-equal) ())))))

 (local (defthmd double-containment-lemma-tail
          (implies (and (o-lo-tep X)
                        (o-lo-tep Y)
                        (subsetp-equal X Y)
                        (subsetp-equal Y X))
                   (subsetp-equal (cdr X) (cdr Y)))
          :hints(("Goal" :in-theory (e/d (subsetp-equal) (o-lo-tep-definition-rule))))))

 (local (defun double-tail-induction (X Y)
          (declare (xargs :guard (and (o-lo-tep X) (o-lo-tep Y))))
          (if (or (endp X) (endp Y))
              (list X Y)
            (double-tail-induction (cdr X) (cdr Y)))))
 
 (local (defthm double-containment-is-equality-lemma
          (IMPLIES (AND (NOT (OR (ENDP X) (ENDP Y)))
                        (IMPLIES (AND (SUBSETP-EQUAL (CDR X) (CDR Y))
                                      (SUBSETP-EQUAL (CDR Y) (CDR X)))
                                 (EQUAL (EQUAL (CDR X) (CDR Y)) T))
                        (O-LO-TEP X)
                        (O-LO-TEP Y)
                        (SUBSETP-EQUAL X Y)
                        (SUBSETP-EQUAL Y X))
                   (EQUAL (EQUAL X Y) T))
          :hints(("Goal"
                  :use ((:instance double-containment-lemma-tail
                                   (X X) (Y Y))
                        (:instance double-containment-lemma-tail
                                   (X Y) (Y X))
                        (:instance double-containment-lemma-head
                                   (X X) (Y Y)))))))

 (local (defthmd double-containment-is-equality
          (implies (and (o-lo-tep X)
                        (o-lo-tep Y)
                        (subsetp-equal X Y)
                        (subsetp-equal Y X))
                   (equal (equal X Y) t))
          :hints(("Goal"
                  :induct (double-tail-induction X Y)))))

 (local (defthm double-containment
          (implies (and (o-lo-tep X)
                        (o-lo-tep Y))
                   (equal (equal X Y)
                          (and (subsetp-equal X Y)
                               (subsetp-equal Y X))))
          :rule-classes ((:rewrite :backchain-limit-lst 1))
          :hints(("Goal" :use (:instance double-containment-is-equality)))))
   
  (defthm o-lo-tep-set-equiv-is-equal
    (implies (and (o-lo-tep x) (o-lo-tep y))
             (equal (equal x y)
                    (set-equiv x y)))
    :hints (("goal" :in-theory (e/d (set-equiv) (double-containment))
             :use ((:instance double-containment)))))

  (in-theory (disable o-lo-tep-set-equiv-is-equal))
 )

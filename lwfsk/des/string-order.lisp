#|

Date: Tue Jan 3 2017
Author: Pete Manolios

Description: Theorems showing that strings form a total
order under string<. 

|#

(in-package "ACL2S")

(defthm string<-asymmetric
  (implies (and (stringp s1) 
                (stringp s2)
                (string< s1 s2))
           (not (string< s2 s1)))
  :hints (("goal" :in-theory (e/d (string<)))))

(defthm string<-transitive
  (implies (and (stringp s1)
                (stringp s2) 
                (stringp s3)
                (string< s1 s2)
                (string< s2 s3))
           (string< s1 s3))
  :hints (("goal" :in-theory (e/d (string<)))))

(defthm string<-trichotomy
  (implies (and (stringp s1)
                (stringp s2)
                (not (string< s1 s2)))
           (iff (string< s2 s1)
                (not (equal s1 s2))))
  :hints (("goal"
           :in-theory (e/d (string<) (coerce-inverse-2))
           :use ((:instance coerce-inverse-2 (acl2::x s1))
                 (:instance coerce-inverse-2 (acl2::x s2))))))

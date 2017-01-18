#|

Author: Pete Manolios
Date: 2017-01-02 

This is a preliminary version of a project to add
simple "higher-order" capabilities to ACL2.

This is done with the use of macros. My focus is on adding
support for common types of idioms, all without any extensions to
ACL2.

This file contains a subset of the current version of
higher-order.lisp.

I wanted the ability to generate strings in ACL2 in a way that is
as convenient as doing it in lisp with format.  After some
experimentation, involving looking at fmt, fms, etc and the
string versions, writing code to do it, and considering just
doing it in raw lisp, I found pretty, which is great because it
doesn't need state and is a logic-mode function.

The reason I wanted this capability is so that I can generate
names using lambdas, in case users don't want to define 
the functions used for map, reduce and filter.

I went through a few versions of the definitions below and 
decided the current definitions are a good stopping point.

Here are some of the considerations, in no particular order.

1. I added the ability to name the generated functions, which
gives us some flexibility when defining higher-order functions.

2. I use fixed variable names, such as l, in the functions I
define. That doesn't seem to pose any problems, but I should
check.

3. I added support for anonymous functions. They are obviously
useful and reduce clutter. However, since one has to mention then
in both create-map* and map* (and similarly for reduce and
filter), once the functions require more than a line or two, it
is best to just define them.

4. It would be nice to not require the user to even write
the (create-map/reduce/filter* ...) forms, but to do that I need
to check when evaluating a map* form whether the create-map* form
was already generated. I can't do that in a robust way without a
lot of raw lisp hacking and it isn't worth it.

5. I should add create-...* and ...* definitions for other
higher-order functions. It would be useful to have a version of
reduce that doesn't need a base element and instead just have a
contract that the input type is a non-empty list.

|#

(in-package "ACL2S")
(include-book "std/strings/pretty" :dir :system)

(defun to-string (l)
  (if (endp l)
      ()
    (cons (str::pretty
           (car l)
           :config
           (str::make-printconfig
            :flat-right-margin 100000
            :home-package (pkg-witness "ACL2S")))
    (to-string (cdr l)))))

(defun l-to-string (l)
  (intern-in-package-of-symbol
   (string-append-lst (to-string l))
   'x))

; (l-to-string '(a - b - c - d))
; (l-to-string '(a - (lambda (x) (+ 1 x)) - b - c - d))

(defmacro create-map* (fun lst-type return-type &rest rst)
  (b* ((name (assoc-equal :name rst))
       (name (and name (second name)))
       (mname (or name fun))
       (f* (l-to-string `(map *-* ,mname)))
       (fixed-vars-types (assoc-equal :fixed-vars rst))
       (fixed-vars-types
        (and fixed-vars-types (second fixed-vars-types)))
       (fixed-vars (strip-cars (strip-cdrs fixed-vars-types)))
       (ic (if fixed-vars-types
               (append `(and (,lst-type l)) fixed-vars-types)
             `(,lst-type l)))
       (args `(l ,@fixed-vars))
       (oc `(,return-type (,f* ,@args))))
      `(defunc ,f* ,args
         :input-contract ,ic
         :output-contract ,oc
         (if (endp l)
             ()
           (cons (,fun (car l) ,@fixed-vars)
                 (,f* (cdr l) ,@fixed-vars))))))

(defmacro map* (fun lst &rest rst)
  (let ((f* (l-to-string `(map *-* ,fun))))
    `(,f* ,lst ,@rst)))

#|
;Examples

(defdata lol (listof true-list))
(defdata lon (listof nat))
(defdata lor (listof rational))

:trans1 (create-map* len lolp lonp)
(create-map* len lolp lonp)
(create-map* rev lolp lolp)

(defdata llol (listof lol))

(create-map* map*-*rev llolp llolp)
:trans1 (create-map* 1+ lorp lorp)

; and now I can write things like

(map* len '((1) (1 2)))
(map* rev '((0 1) (1 2)))
(map* map*-*rev '(((0 1) (1 2)) ((3 4))))

(len (map* len '((1) (1 2))))

:trans1 (create-map* + lorp lorp 
                     (:fixed-vars ((rationalp y))) (:name +y))
:trans1 (create-map* (lambda (x) (+ x 3)) lorp lorp)

(create-map* + lorp lorp 
             (:fixed-vars ((rationalp y))) (:name +y))

(create-map* (lambda (x) (+ x 3)) lorp lorp)

; Notice that I use the name +y here, not +
(map* +y '(1/2 -2 -17/2) 3)
(map* (lambda (x) (+ x 3)) '(1/2 -2 -17/2))
|#

(defmacro create-map2* (fun lst1-type lst2-type return-type &rest rst)
  (b* ((name (assoc-equal :name rst))
       (name (and name (second name)))
       (mname (or name fun))
       (f* (l-to-string `(map2 *-* ,mname)))
       (fixed-vars-types (assoc-equal :fixed-vars rst))
       (fixed-vars-types
        (and fixed-vars-types (second fixed-vars-types)))
       (fixed-vars (strip-cars (strip-cdrs fixed-vars-types)))
       (ic (append `(and (,lst1-type l1) (,lst2-type l2)) fixed-vars-types))
       (args `(l1 l2 ,@fixed-vars))
       (oc `(,return-type (,f* ,@args))))
      `(defunc ,f* ,args
         :input-contract ,ic
         :output-contract ,oc
         (if (or (endp l1)
                 (endp l2))
             ()
           (cons (,fun (car l1) (car l2) ,@fixed-vars)
                 (,f* (cdr l1) (cdr l2) ,@fixed-vars))))))

(defmacro map2* (fun lst1 lst2 &rest rst)
  (let ((f* (l-to-string `(map2 *-* ,fun))))
    `(,f* ,lst1 ,lst2 ,@rst)))

#|
;Examples

:trans1 (create-map2* + lorp lorp lorp)
(create-map2* + lorp lorp lorp)
(create-map2* * lorp lorp lorp)
(create-map2* * lorp lorp lorp (:name 2*))
(create-map2* * lorp lorp lorp (:name *2))

(map2* +  '(1 1/2 4 2) '(-3 2 1/2 1))
(map2* *  '(1 1/2 4 2) '(-3 2 1/2 1))
(map2* 2* '(1 1/2 4 2) '(-3 2 1/2 1))
(map2* *2 '(1 1/2 4 2) '(-3 2 1/2 1))

(map2* + 
       (map2* * '(1 1/2 4 2) '(-3 2 1/2 1))
       (map2* + '(1 1/2 4 2) '(-3 2 1/2 1)))
       
|#

(defmacro create-reduce* (fun base-type lst-type &rest rst)
  (b* ((name (assoc-equal :name rst))
       (name (and name (second name)))
       (mname (or name fun))
       (f* (l-to-string `(reduce *-* ,mname)))
       (fixed-vars-types (assoc-equal :fixed-vars rst))
       (fixed-vars-types (and fixed-vars-types (second fixed-vars-types)))
       (fixed-vars (strip-cars (strip-cdrs fixed-vars-types)))
       (ic (append `(and (,base-type e) (,lst-type l) ,@fixed-vars-types)))
       (args `(e l ,@fixed-vars))
       (oc `(,base-type (,f* ,@args))))
      `(defunc ,f* ,args
         :input-contract ,ic
         :output-contract ,oc
         (if (endp l)
             e
           (,fun (car l) (,f* e (cdr l) ,@fixed-vars) ,@fixed-vars)))))

(defmacro reduce* (fun base-element l &rest rst)
  (let ((f* (l-to-string `(reduce *-* ,fun))))
    `(,f* ,base-element ,l ,@rst)))


#|

; Examples

:trans1 (create-reduce* + rationalp lorp)
:trans1 (create-reduce* 
         + rationalp lorp
         (:fixed-vars ((rationalp x) (rationalp y)))
         (:name 2+))

(create-reduce* + rationalp lorp)
(create-reduce* 
         + rationalp lorp
         (:fixed-vars ((rationalp x) (rationalp y)))
         (:name 2+))

(1+ (reduce* + 0 (map* len '((1) (1 2) (1 2 3) (1 2 3 4)))))

(1+ (reduce* 2+ 0 (map* len '((1) (1 2) (1 2 3) (1 2 3 4))) 0 0))
(1+ (reduce* 2+ 0 (map* len '((1) (1 2) (1 2 3) (1 2 3 4))) 1 2))

(create-reduce* (lambda (x y) (+ x y 2)) rationalp lorp)

(1+ (reduce* (lambda (x y) (+ x y 2)) 0 (map* len '((1) (1 2) (1 2 3) (1 2 3 4)))))

(defun foo (l)
  (1+ (reduce* + 0 (map* len l))))

(foo '((1) (2 3)))

|#

(defmacro create-filter* (fun lst-type &rest rst)
  (b* ((name (assoc-equal :name rst))
       (name (and name (second name)))
       (mname (or name fun))
       (f* (l-to-string `(filter *-* ,mname)))
       (fixed-vars-types (assoc-equal :fixed-vars rst))
       (fixed-vars-types (and fixed-vars-types (second fixed-vars-types)))
       (fixed-vars (strip-cars (strip-cdrs fixed-vars-types)))
       (ic (if fixed-vars-types
               (append `(and (,lst-type l)) fixed-vars-types)
             `(,lst-type l)))
       (args `(l ,@fixed-vars))
       (oc `(,lst-type (,f* ,@args))))
      `(defunc ,f* ,args
         :input-contract ,ic
         :output-contract ,oc
         (cond ((endp l) ())
               ((,fun (car l) ,@fixed-vars)
                (cons (car l) (,f* (cdr l) ,@fixed-vars)))
               (t (,f* (cdr l) ,@fixed-vars))))))

(defmacro filter* (fun lst &rest rst)
  (let ((f* (l-to-string `(filter *-* ,fun))))
    `(,f* ,lst ,@rst)))

#|

; Examples

:trans1 (create-filter* <= lorp (:fixed-vars ((rationalp y))))
(create-filter* <= lorp (:fixed-vars ((rationalp y))))

:trans1 (create-filter* (lambda (x) (<= x 3)) lorp)
(create-filter* (lambda (x) (<= x 3)) lorp)

(map* len '((1) (1 2) (1 2 3) (1 2 3 4)))
(filter* <= (map* len '((1) (1 2) (1 2 3) (1 2 3 4))) 2)
(filter* <= (map* len '((1) (1 2) (1 2 3) (1 2 3 4))) 4)

(filter* <= (map* len '((1) (1 2) (1 2 3) (1 2 3 4))) 3)
(filter* (lambda (x) (<= x 3))
         (map* len '((1) (1 2) (1 2 3) (1 2 3 4))))

(defunc len-less (l y)
  :input-contract (and (true-listp l) (natp y))
  :output-contract (booleanp (len-less l y))
  (<= (len l) y))

:trans1 (create-filter* len-less lolp (:fixed-vars ((natp y))))
(create-filter* len-less lolp (:fixed-vars ((natp y))))

:trans1 (create-filter* (lambda (x) (<= (len x) 3)) lolp)
(create-filter* (lambda (x) (<= (len x) 3)) lolp)

(filter* len-less '((1) (1 2) (1 2 3) (1 2 3 4)) 2)
(filter* len-less '((1) (1 2) (1 2 3) (1 2 3 4)) 4)

(filter* len-less '((1) (1 2) (1 2 3) (1 2 3 4)) 3)
(filter* (lambda (x) (<= (len x) 3))
         '((1) (1 2) (1 2 3) (1 2 3 4)))
 
|#

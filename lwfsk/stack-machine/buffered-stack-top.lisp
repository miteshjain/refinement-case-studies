(in-package "ACL2S")

;; This file includes only events needed to understand STK, our simple
;; stack machine All of the supporting theorems can be found in the
;; included book.

;; Data definitions for STK

;; An element in a stack
(defdata el all)

;; A stack is a list of elements
(defdata stack (listof el))

;; An operation on stack
(defdata op-name (oneof 'push 'pop 'top 'nop))

;; An instruction of the stack machine
(defdata inst
  (record (op . op-name)
          (arg . el)))

;; An instruction returns a record consisting of a value and the
;; updated stack.
(defdata retvalue
  (record (value . el)
          (stk . stack)))

;; A list of instructions
(defdata inst-mem (listof inst))

;; State of STK machine consists of the program counter, an
;; instruction memory and a stack.
(defdata sstate
  (record (pc . nat)
          (imem . inst-mem)
          (stk . stack)))

(defconst *empty-stack* 'empty)
(defconst *ignore-value* 'ignorev)

(defunc mpush (el stk)
 :input-contract (and (stackp stk) (elp el))
 :output-contract (retvaluep (mpush el stk))
 (retvalue el (cons el stk)))

(defunc mpop (stk)
  "pop an element from the stk"
  :input-contract (stackp stk)
  :output-contract (retvaluep (mpop stk))
  (if (consp stk)
      (retvalue (car stk) (cdr stk))
    (retvalue *empty-stack* stk)))
  
(defunc mtop (stk)
  "top leaves the stack unchanged."
  :input-contract (stackp stk)
  :output-contract (retvaluep (mtop stk))
  (if (consp stk)
      (retvalue (car stk) stk)
    (retvalue *empty-stack* stk)))

(defunc mnop (stk)
  "no-op instruction"
  :input-contract (stackp stk)
  :output-contract (retvaluep (mnop stk))
  (retvalue *ignore-value* stk))

(defunc stk-step-inst (inst stk)
  "returns next state of stk "
 :input-contract (and (instp inst) (stackp stk))
 :output-contract (stackp (stk-step-inst inst stk))
 (let ((op (inst-op inst)))
   (let ((retv (cond ((equal op 'push)
                      (mpush (inst-arg inst) stk ))
                     ((equal op 'pop)
                      (mpop stk))
                     ((equal op 'top)
                      (mtop stk))
                     ((equal op 'nop)
                      (mnop stk))
                     (t (retvalue *ignore-value* stk)))))
     (retvalue-stk retv))))

(defunc spec-step (s)
  "single step STK machine"
  :input-contract (sstatep s)
  :output-contract (sstatep (spec-step s))
  (let* ((pc (sstate-pc s))
         (imem (sstate-imem s))
         (inst (nth pc imem))
         (stk (sstate-stk s)))
    (if (instp inst)
        (sstate  (1+ pc) imem (stk-step-inst inst stk))
      (sstate (1+ pc) imem  stk))))

(defunc spec-run (w k)
  :input-contract (and (sstatep w) (natp k))
  :output-contract (sstatep (spec-run w k))
  (if (zp k)
      w
    (spec-run (spec-step w) (1- k))))

;; BSTK Machine (implementation)

(encapsulate
 (((ibuf-capacity) => *))
 (local (defun ibuf-capacity ()
          2))

 (defthm ibuf-cap>=2
   (and (natp (ibuf-capacity))
           (>= (ibuf-capacity) 2))
   :rule-classes (:rewrite :type-prescription))

 )

(defunbc ibufp (l)
  :input-contract t
  (and (inst-memp l)
       (<= (len l) (ibuf-capacity))))

;; State of BSTK machine
(defdata istate
  (record (pc . nat)
          (imem . inst-mem)
          (ibuf . ibufp)
          (stk . stack)))

(defunc impl-internal-ibuf-step (inst ibuf)
  "enque the inst in ibuf"
 :input-contract (and (instp inst) (ibufp ibuf) (< (len ibuf) (ibuf-capacity)))
 :output-contract (ibufp (impl-internal-ibuf-step inst ibuf))
  (append ibuf (list inst)))

(defunc impl-observable-stk-step (stk ibuf)
  "state of the stk when BSTK takes an observable step (i.e. does not
  stutter) by executing all instructions enqueued in ibuf"
  :input-contract (and (stackp stk) (inst-memp ibuf))
  :output-contract (stackp (impl-observable-stk-step stk ibuf))
  (if (endp ibuf)
      stk
    (impl-observable-stk-step (stk-step-inst (car ibuf) stk)
                              (cdr ibuf))))

(defunc impl-observable-ibuf-step (inst)
  "next state of ibuf when BSTK does not stutter"
  :input-contract (instp inst)
  :output-contract (ibufp (impl-observable-ibuf-step inst))
  (if (equal (inst-op inst) 'top)
      nil
    (list inst)))

(defunbc stutterp (inst ibuf)
  "BSTK stutters if ibuf is not full or the current instruction is not 'top"
  :input-contract (and (instp inst) (ibufp ibuf))
  (and (< (len ibuf) (ibuf-capacity))
       (not (equal (inst-op inst) 'top))))

(defunc impl-step (s)
  "A step of BSTK machine"
  :input-contract (istatep s)
  :output-contract (istatep (impl-step s))
  (let* ((pc (istate-pc s))
         (imem (istate-imem s))
         (stk (istate-stk s))
         (ibuf (istate-ibuf s)) 
         (inst (nth pc imem)))
    (if (instp inst)
        (let ((nxt-pc (1+ pc))
              (nxt-stk (if (stutterp inst ibuf)
                           stk
                         (impl-observable-stk-step stk ibuf)))
              (nxt-ibuf (if (stutterp inst ibuf)
                            (impl-internal-ibuf-step inst ibuf)
                          (impl-observable-ibuf-step inst))))
          (istate nxt-pc imem nxt-ibuf nxt-stk ))
      (let ((nxt-pc (1+ pc))
            (nxt-stk (impl-observable-stk-step stk ibuf))
            (nxt-ibuf nil))
        (istate nxt-pc imem nxt-ibuf nxt-stk)))))

(defunc impl-run (s n)
  :input-contract (and (istatep s) (natp n))
  :output-contract (istatep (impl-run s n))
  (if (zp n)
      s
    (impl-run (impl-step s) (1- n))))

(defunc commited-istate (s)
  :input-contract (istatep s)
  :output-contract (istatep (commited-istate s))
  (let* ((stk (istate-stk s))
         (imem (istate-imem s))
         (ibuf (istate-ibuf s))
         (pc (istate-pc s))
         (cpc (nfix (- pc (len ibuf)))))
    (istate cpc imem nil stk )))

(defunbc good-istatep (s)
  "if it is reachable from a commited-state in |ibuf| steps"
  :input-contract t
  (and (istatep s)
       (>= (istate-pc s) (len (istate-ibuf s)))
       (let* ((cs (commited-istate s))
              (s-cs (impl-run cs (len (istate-ibuf s)))))
         (equal s-cs s))))
           
(defthm good-istatep-inductive
  (implies (good-istatep s)
           (good-istatep (impl-step s))))

;; BSTK augmented with history

(defdata history
  (record (valid . boolean)
          (pre . istate)))

(defdata Hstate
  (record (s . istate)
          (h . history)))

(defunc H-step (s)
  "transition function HSTK machine"
  :input-contract (hstatep s)
  :output-contract (hstatep (h-step s))
  (let* ((x (hstate-s s))
         (y (impl-step x)))
    (hstate y (history t x))))

;; HBSTK refines BSTK
(defunc P (s)
  :input-contract (hstatep s)
  :output-contract (istatep (P s))
  (istate (istate-pc (hstate-s s))
          (istate-imem (hstate-s s))
          (istate-ibuf (hstate-s s))
          (istate-stk (hstate-s s))))

(defunc Rc (s)
  :input-contract (istatep s)
  :output-contract (sstatep (Rc s))
  (let* ((stk (istate-stk s))
         (imem (istate-imem s))
         (pc (istate-pc s))
         (ibuf (istate-ibuf s))
         (ibuflen (len ibuf))
         (rpc (nfix (- pc ibuflen))))
    (sstate rpc imem stk)))

(defunc R (s)
  "Refinement map"
  :input-contract (hstatep s)
  :output-contract (sstatep (R s))
  (Rc (P s)))

(defunbc good-histp (s)
  :input-contract (hstatep s)
  (let* ((h (hstate-h s))
         (h-valid (history-valid h))
         (pre (history-pre h)))
    (implies h-valid
             (and (good-istatep pre)
                  (equal (impl-step pre) (hstate-s s))))))
  
(defunbc good-hstatep (s)
  :input-contract t
  (and (hstatep s)
       (good-istatep (hstate-s s))
       (good-histp s)))

(defthm good-hstatep-inductive
  (implies (and (good-hstatep s))
           (good-hstatep (H-step s))))

(defunbc B (s w)
  :input-contract t
  (and (good-hstatep s)
       (sstatep w)
       (equal (R s) w)))
  
(defunc rankt (s)
  "rank of an istate s is capacity of ibuf - #inst in ibuf"
  :input-contract (hstatep s)
  :output-contract (natp (rankt s))
  (nfix (- (ibuf-capacity) (len (istate-ibuf (hstate-s s))))))

(defun-sk spec-reachp (w v)
  (exists k
    (and (natp k)
         (equal (spec-run w k) v)))
  :witness-dcls ((declare (xargs :guard (and (sstatep w) (sstatep v))
                                 :verify-guards nil))))

(defunbc C (x y)
   :input-contract t
   (and (good-hstatep x)
        (sstatep y)
        (history-valid (hstate-h x))
        (<= (sstate-pc y)
            (sstate-pc (R x)))
        (spec-reachp (Rc (history-pre (hstate-h x))) y)))

(defunc rankls (y x)
  "number of steps y is away from r.x, a state that is related to x by B"
  :input-contract (and (sstatep y) (hstatep x))
  :output-contract (natp (rankls y x))
  (let ((y-pc (sstate-pc y))
        (x-pc (sstate-pc (R x))))
    (nfix (- x-pc y-pc))))

(defthm B-is-a-LWFSK
  (implies (and (good-hstatep s)
                (sstatep w)
                (B s w))
           (or (lwfsk2b s (H-step s) w)
               (lwfsk2d (H-step s) w))))


(defunbc lwfsk2b (s u w)
  :input-contract (and (hstatep s) (hstatep u) (sstatep w))
  (and (B u w)
       (< (rankt u) (rankt s))))

(defunbc lwfsk2d (u w)
  :input-contract (and (hstatep u) (sstatep w))
  (C u (spec-step w)))

(defthmd C-is-good
  (implies (and (C x y)
                (not (B x y)))
           (lwfsk2f x y)))

(defunbc lwfsk2f (x y)
  :input-contract (and (hstatep x) (sstatep y))
  (let ((z (spec-step y)))
    (and (C x z)
         (< (rankls z x) (rankls y x)))))

(defpackage steenrod
  (:use #:cl #:optima #:iter ))
(in-package #:steenrod)

(declaim (optimize (debug 3)))

;;; some utilities
(defun partial (fn &rest args)
  "Partially applies fn to args. Returns the function (fn arg1 arg2 ... argn _____): x1...xk -> (fn arg1 ... argn x1 ... xk)."
  (lambda (&rest inner-args)
    (apply fn (append args inner-args))))

(defun comp (&rest fns)
  (match fns
    (nil #'identity)
    ((list f) f)
    ((list f g) (lambda (&rest args)
		  (funcall f (apply g args))))
    (_ (reduce #'comp fns :from-end t)))) ;:from-end? is that right?

(defmacro afn (args &body body)
  `(labels ((self (,@args)
	      ,@body))
     #'self))

(defmacro aif (test true &optional false)
  `(let ((it ,test))
     (if it ,true ,false)))

(defmacro sif2 (test true &optional false)
  (alexandria:with-gensyms (one two)
    `(symbol-macrolet ((sit ,test))
       (multiple-value-bind (,one ,two) ,test
	   (if (or ,one ,two)
	       ,true ,false)))))

(defmacro aand (&rest args)
  (cond ((null args) t)
	((null (cdr args)) (car args))
	(t `(aif ,(car args) (aand ,@(cdr args))))))


(defun sgn (num exp)
  "Computes (-1)^num and uses it as the coefficient of exp."
  (if (evenp num) exp (list '-1 exp)))

(defun make-simplex (seq) (list :simplex (coerce seq 'vector)))
(defun verts (simplex) (second simplex))
(defun dim (simplex) (1- (length (verts simplex))))
(defun standard-simp (dim)
  (make-simplex (apply #'vector (iter (for i from 0 to dim) (collect i)))))

(def-morphism boundary (simplex)
  "Computes the boundary of a simplex"
  (let ((verts (verts simplex)))
    (if (<= (length verts) 1) 0
	(cons '+
	      (iter (for v in-vector verts)
		    (for sgn first 0 then (1+ sgn))
		    (collect
			(sgn sgn (make-simplex (remove v verts)))))))))
;;; boundary relies on stuff defined much later

;; (defun make-tensor (arg1 arg2)
;;   (let ((arg1 (dummy-coef arg1))
;; 	(arg2 (dummy-coef arg2)))
;;    (match (list arg1 arg2)
;;      ((or (list (list k 0) _) (list _ (list j 0))) 0)
;;      ((list (list k x) (list z y)) (list (* k z) (list :tensor x y))))))

;;; arbitrary arity tensor products
(defun make-tensor (&rest args)
  (let ((args (mapcar #'dummy-coef args)))
    (if (some (lambda (x)
		(destructuring-bind (_ vec) x
		  (declare (ignorable _))
		  (eql vec 0)))
	   args)
	0 (list (reduce #'* (mapcar #'car args))
		(cons :tensor (mapcar #'second args))))))

(defun left (tensor) (second tensor))
(defun right (tensor) (third tensor))

(def-morphism flip (simp)
  (match simp
    (0 0)
    ((list :tensor x y) (sgn (* (dim x) (dim y)) (make-tensor y x)))))

;;; fixed arity = 2 
(defun tensor-p (x)
  (match x
    ((list :tensor _ _) t)
    (0 t)
    (_ nil)))

(defun gen-tensor-p (x)
  (match x
    ((list* :tensor _) t)
    (0 t)
    (_ nil)))

;;; working up to tidy
(defun plus-p (expr)
  (match expr
    ((list* '+ _) t)
    (_ nil)))

(defun dummy-coef (arg)
  (match arg
    ((guard (list k _) (numberp k)) arg)
    (_ (list 1 arg))))

(defun combine-like-terms (terms)
  (let ((terms (mapcar #'dummy-coef terms)))
   (match terms
     ((list* head _) 
      (let ((likep (lambda (arg) (equalp (second arg) (second head)))))
	(cons (list (reduce #'+ (mapcar #'car (remove-if-not likep terms)))
		    (second head))
	      (combine-like-terms (remove-if likep terms)))))
     (nil nil))))

(defun tidy (expr)
  (match expr
    ((list '+) 0)
    ((list '+ x) x)
    ((list* '+ rest)
     (cons '+
	   (let ((nonzero (remove 0 (mapcar #'tidy rest))))
	     (combine-like-terms
	      (append (mapcan #'cdr (remove-if-not #'plus-p nonzero))
		      (remove-if #'plus-p nonzero))))))
    ((list 0 _) 0)
    ((guard (list scalar 0) (numberp scalar)) 0)
    ((guard (list scalar (list* '+ rest)) (numberp scalar)) ;distributivity
     (cons '+ (mapcar (lambda (x) (list scalar (tidy x))) rest)))
    ((guard (list s1 (list s2 thing)) (and (numberp s1) (numberp s2)))
     (list (* s1 s2) (tidy thing)))
    ((list :tensor (list* '+ sum) x)
     (cons '+ (mapcar (lambda (summand) (make-tensor summand x)) sum )))
    ((list :tensor x (list* '+ sum))
     (cons '+ (mapcar (lambda (summand) (make-tensor x summand)) sum )))
    ((or (list :delta _ 0 _) (list :delta _ _ 0)) 0)
    ((list :delta n (list a x) y) (list a (list :delta n x y)))
    ((list :delta n y (list a x)) (list a (list :delta n y x)))
    ((list :delta n (list* '+ summands) y)
     (cons '+ (mapcar (lambda (summand)
			(list :delta n summand y))
		      summands)))
    ((list :delta n y (list* '+ summands))
     (cons '+ (mapcar (lambda (summand)
			(list :delta n y summand))
		      summands)))
    ((list* car cdr) (if cdr (cons car (mapcar #'tidy cdr))))
    (_ expr)))

(defun reduce-mod (base expr)
  (match base
    (nil expr)
    (1 (error "base cannot be 1"))
    (_ (match expr
	 ((guard (list k vec) (numberp k)) (list (mod k base) (reduce-mod base vec)))
	 ((list* '+ summands) (cons '+ (mapcar (partial #'reduce-mod base) summands)))
	 (_ expr)))))

(defparameter *base* 2)

(defun remove-1 (lst)
  (match lst
    ((list 1 vec) vec)
    ((list* '+ vecs) (cons '+ (mapcar #'remove-1 vecs)))
    (_ lst)))

(defun mega-tidy (lst)
  (let ((tidied (reduce-mod *base* (tidy lst))))
    (if (equalp lst tidied)
	(if (= *base* 2) (remove-1 lst)
	    lst)
	(mega-tidy tidied))))

(defun flatten-tensors (expr)
  (match expr
    ((list* :tensor args)
     (mapcan (lambda (x)
	       (match x
		 ((list* :tensor stuff) stuff)
		 (_ (list x))))
	     (cons :tensor (flatten-tensors args))))
    ((list* op stuff) (cons op (mapcar #'flatten-tensors stuff)))
    (_ expr)))

(defun op-p (op) (or (member op '(+ -)) (numberp op)))

;;; with fixed arity tensors
(defun make-callable (fn-exp)
  "Creates a function as defined by a symbolic linear combination of functions"
  (match fn-exp
    ((list :tensor f g)
     (afn (x)
       (let ((f (make-callable f))
	     (g (make-callable g)))
	 (match x
	   (0 0)
	   ((list :tensor y z) (make-tensor (funcall f y)
					    (funcall g z)))

	   ((guard (list* op expr) (op-p op))	;linearity
	    (list op (mapcar #'self expr)))))))
    ((list* 'comp fs) (reduce #'comp
    			     (mapcar (lambda (f) (lambda (x) (call f x)))
    				     fs)))
    ((guard (list* op exp) (op-p op))
     (lambda (arg)
       (cons op (mapcar (lambda (f) (funcall (make-callable f) arg)) exp))))
    (_ fn-exp)))

;;; general arity tensors 
;; (defun make-callable (fn-exp)
;;   "Creates a function as defined by a symbolic linear combination of functions"
;;   (match fn-exp
;;     ((list* :tensor maps)
;;      (afn (x)
;;        (let ((maps (mapcar #'make-callable maps)))
;; 	 (match x
;; 	   (0 0)
;; 	   ((list :tensor fns) (apply #'make-tensor
;; 				      (lambda ())))

;; 	   ((guard (list* op expr) (op-p op))	;linearity
;; 	    (list op (mapcar #'self expr)))))))
;;     ((list* 'comp fs) (reduce #'comp
;;     			     (mapcar (lambda (f) (lambda (x) (call f x)))
;;     				     fs)))
;;     ((guard (list* op exp) (op-p op))
;;      (lambda (arg)
;;        (cons op (mapcar (lambda (f) (funcall (make-callable f) arg)) exp))))
;;     (_ fn-exp)))

(defun extend-morphism (fn)
  "Extends a function on a basis to a morphism"
  (afn (expr)
   (match expr
     (0 0)
     ((list* '+ rest) (cons '+ (mapcar #'self rest)))
     ((guard (list n vec) (numberp n)) (list n (self vec)))
     (_ (funcall fn expr)))))

(defun call (fn-exp sexp)
  (mega-tidy (funcall (extend-morphism (make-callable fn-exp)) sexp)))

(defmacro def-morphism (name (arg) &body body)
  `(defun ,name (,arg)
     (labels ((,name (,arg)
		,@body))
       (call #',name ,arg))))

(defun small-phi (k simp)
  (let ((dim (dim simp)))
    (if (= k (aref (verts simp) dim))		;is this check sufficient
	0
	(let* ((verts (verts simp))
	      (face (make-simplex (concatenate 'vector verts (list k)))))
	  (sgn (1+ dim) face)))))

(defun big-phi (k base)
  (let* ((phi-k (partial #'call (partial #'small-phi k)))
	 (id-tensor-phi (sgn (dim (left base))
			     (call (make-tensor #'identity phi-k) base)))) ;whaaat
    ;; justin smith did this though
    (if (zerop (dim (right base)))
	(list '+ id-tensor-phi
	      (make-tensor (funcall phi-k (left base)) ;already uses call
			   (make-simplex (vector k))))
	id-tensor-phi)))

(defparameter *cache* (make-hash-table :test 'equalp))

(defun alexander-whitney (simp)
  (flet ((simpify (list) (make-simplex (apply #'vector list))))
    (cons '+
	  (iter (for n from 0 to (dim simp))
		(collect
		    (make-tensor
		     (simpify (iter (for i from 0 to n) (collect i)))
		     (simpify (iter (for i from n to (dim simp))
				    (collect i)))))))))

(defun xi-base (ei simp)
  (let* ((dim (dim simp))
	 (phi-k (partial #'big-phi (aref (verts simp) (dim simp)))))
    (match (list ei dim)
      ((list 0 0) (make-tensor simp simp))
      ((list _ 0) 0)
      ;; ((list 0 _) (alexander-whitney simp)) ;I'm doing this in xi-base-memo. Probably bad organization
      ((list _ _)
       (let ((left-recur (xi (1- ei) simp))
	     (right-recur (xi ei (call #'boundary simp))))
	 (list '+
	       (call phi-k (list '+ left-recur (sgn ei (flip left-recur)))) ;phi on outside
	       (sgn ei (call phi-k right-recur))))))))  ;sgn dim? sgn ei? sgn k?

(defun on-simplices (fn expr)
  (match expr
    ((list :simplex _)
     (funcall fn expr))
    ((list* op rest)
     (cons op (mapcar (partial #'on-simplices fn) rest)))
    (_ expr)))

(defun map-simplex (simp expr)
  (on-simplices 
   (lambda (reduced-simplex)
     (aif (verts reduced-simplex)
      (make-simplex (map 'vector (lambda (x) (aref (verts simp) x)) it))
      0))
   expr))

(defun xi-base-memo (ei simp)
  (if (= ei 0) (alexander-whitney simp)  ;if it's alexander-whitney, no need to memoize
      (sif2 (gethash (list ei simp) *cache*) sit
	    (setf sit (mega-tidy (xi-base ei simp))))))

;;; this makes a huge difference in terms of performance
(defun xi-base-uniformed (ei simp)
  (map-simplex
   simp
   (let ((simp (standard-simp (dim simp))))
     (xi-base-memo ei simp))))

(defun xi (ei exp)
  (call (partial #'xi-base-uniformed ei) exp))

(defun verts-to-bitstring (verts)
  (iter (for i in-vector verts) (sum (ash 1 (1- i)))))

;;; to convert to a different base 
;; (let ((cl:*print-radix* t)
;; 		(cl:*print-base* 16))
;; 	    (pprint (on-simplices (comp #'verts-to-bitstring #'verts)
;; 				  (xi 0 (standard-simp 30)))))
;;; todo---
;;; make coefficients work
;;; simplices as bitstrings? This will be necessary for represntation eventually
;;; perfect hash simplices -> bitstrings? 
;;; coassociativity works! 

;;; coassociativity!
;; (mega-tidy
;; 	   (list '+ (flatten-tensors (call (make-tensor #'identity (partial #'xi 0)) (xi 0 (standard-simp 60))))
;; 		 (list -1
;; 		       (flatten-tensors (call (make-tensor (partial #'xi 0) #'identity) (xi 0 (standard-simp 60)))))))
;;; => 0 

(defun permute (perm seq)
  (let ((perm (append perm (list (car perm)))))
    (flet ((lookup (ind)
	     (aif (second (member ind perm)) it ind)))
      (iter (for i from 1 to (length seq))
	    (collect (nth (1- (lookup i)) seq))))))

(defun permute-tensor (perm tens)
  (cons :tensor (permute perm (cdr tens))))


;;; optrees
;;;  1 2 3
;;;  \/ /
;;; 1 \/
;;;  0 \
;;; (:delta 0 (:delta 1 1 2) 3)

(defun degree (tree)
  (match tree
    ((list :delta n x y) (+ n (degree x) (degree y)))
    (_ 0)))

(def-morphism derivative (tree)
  (match tree
    ((list :delta 0 x y) `(+ (:delta 0 ,(derivative x) ,y)
			     (:delta 0 ,x ,(derivative y))))
    ((list :delta n x y) `(+ (:delta ,(1- n) ,x ,y)
			     ,(sgn n `(:delta ,(1- n) ,y ,x))
			     (:delta ,n ,(derivative x) ,y)
			     (:delta ,n ,y ,(derivative y))))
    (_ 0)))
;;; this is not quite right 

(defun optree-leaves (tree)
  (match tree
    ((list* :delta _ args) (apply #'append (mapcar #'optree-leaves args)))
    (_ (list tree))))

(defun call-optree (tree simp)
  (labels ((place (x y simp)
	     (call (make-tensor (partial #'walk-optree x)
				(partial #'walk-optree y))
		   simp))
	   (walk-optree (tree simp)
	     (match tree
	       ((list :delta n x y) (call (partial #'place x y) (xi n simp)))
	       (_ simp))))
   (call
    (lambda (expr)
      (cons :tensor
	    (mapcar #'car (sort (mapcar #'cons (cdr expr) (optree-leaves tree))
				#'< :key #'cdr))))
    (flatten-tensors (call (partial #'walk-optree tree) simp)))))

(defun red (x y z) `(:delta 0 (:delta 1 ,x ,y) ,z))
(defun blue (x y z) `(:delta 0 ,x (:delta 1 ,y ,z)))
(defun green (x y z) `(:delta 1 (:delta 0 ,x ,y) ,z))
(defun yellow (x y z) `(:delta 1 ,x (:delta 0 ,y ,z)))

(defun test-cycle (simp)
  (mega-tidy
   (list '+
	 (call-optree (blue 1 2 3) simp)
	 (call-optree (red 2 1 3) simp)
	 (call-optree (green 1 3 2) simp))))

;; (defun test-cycle (simp)
;;   (mega-tidy
;;    (list '+
;; 	 (call-optree (blue 1 3 2) simp)
;; 	 (call-optree (yellow 2 1 3) simp)
;; 	 (call-optree (red 1 2 3) simp))))


;;; How to show steps? 

;;; jacobi identity:
;;; (1 + r + r^2) (1 tensor d) d ___ = 0
;;; d = TDelta1 + Delta1
;; (defun jacobi-test (simp)
;;   (flet ((d (x) (list '+ (flip (xi 1 d)) (xi 1 d))))))

;;; step operad
(defun split (n step)
  (match n
    (1 (list (list step)))
    (_ (iter (for i from 0 below (length step))
	     (appending (mapcar (partial #'cons (subseq step 0 (1+ i)))
				(split (1- n) (subseq step i))))))))

(defun tally (list)
  (let ((hash (make-hash-table)))
    (dolist (x list)
      (incf (gethash x hash 0)))
    hash))

;;; http://stackoverflow.com/questions/3210177/in-common-lisp-how-to-define-a-generic-data-type-specifier-like-list-of-intege
;; (defun elements-are-of-type (seq type)
;;   (every (lambda (x) (typep x type)) seq))
;; (deftype list-of (type)
;;   (let ((predicate (gensym)))
;;     (setf (symbol-function predicate)
;; 	  (lambda (seq) (elements-are-of-type seq type)))
;;     `(and list (satisfies ,predicate))))

;;; this works but i wish it were more abstract 
(defun join-two-specific (join-op split0 split1)
  (if (endp join-op) nil
      (match (list join-op split0 split1)
	((list (list* 0 join-cdr) (list* car0 cdr0) _)
	 (append car0 (join-two-specific join-cdr cdr0 split1)))
	((list (list* 1 join-cdr) _ (list* car1 cdr1))
	 (append car1 (join-two-specific join-cdr split0 cdr1))))))

(defun join-two (join-op step0 step1)
  (let* ((step1 (mapcar (partial #'+ (length step0)) step1))
	 (tallies (tally join-op)))
    (cons '+
	  (mapcan (lambda (x1)
		    (mapcar (lambda (x0)
			      (join-two-specific join-op x0 x1))
			    (split (gethash 0 tallies) step0)))
		  (split (gethash 1 tallies) step1)))))
;;; this assumes each input will start at zero, and hit
;;; every level from 0 ... dim of the step-op

(defun points (size max)
  (declare (type (integer 0) size max))
  (match (list size max)
    ((list 0 _) (list nil))
    (_ (iter (for i from 0 to max)
	     (appending (mapcar (partial #'cons i) (points (1- size) i)))))))
;;; this is a bad name
;;; the variable names are bad too.

(defun make-step (list)
  (declare (type list list))
  (list :step list))

(defun step-act-specific (dim step act-spec)
  "Performs an action indicated by step on a standard simplex of dimension dim by switching levels as dictated by act-spec. To compute the action of step, you must compute all necessary values of act-spec."
  (let* ((step (second step))
	 (result (make-array (1+ (reduce #'max step)) :initial-element nil)))
    (labels ((recur (i step act-spec)
	       (cond ((or (endp step) (> i dim)) result)
		     ((aand (car (aref result (car step))) (= it i)) nil)
		     (t (push i (aref result (car step)))
			(if (aand act-spec (= i (car it)))
			    (recur i (cdr step) (cdr act-spec))
			    (recur (1+ i) step act-spec))))))
      (map 'list #'reverse (recur 0 step act-spec)))))
;;; there's an off by one error here, i.e. delta-1 [0 1] gives wrong thing

(defun step-act-dim (dim step-lin-comb)
  (call
   (lambda (step)
     (cons '+
	   (iter (for x in 
		      (remove-if #'not
				 (mapcar (comp (partial #'step-act-specific dim step) #'reverse)
					 (points (dim step) dim)))) ;polymorphic dim of steps? Already is!
		 (collect (cons :tensor (mapcar #'make-simplex x))))))
   step-lin-comb))

(defun step-act (step-lin-comb simp-lin-comb)
  (call (lambda (simp)
	  (map-simplex simp
	   (step-act-dim (dim simp) step-lin-comb)))
	simp-lin-comb))
;;; this ought to take a (linear comb of) simplex as an arg

(defun delta-i-step (n)
  (declare (type (integer 0) n))
  (make-step
   (iter (for i from 0 to (1+ n))
	 (collect (if (oddp i) 0 1)))))
;;; double check even or odd

(defun delta-n (n simp-lin-comb)
  (step-act (delta-i-step n) simp-lin-comb))
;;; still some issues in dim 2 or higher.
;;; I need to write a way to convert optrees to steps


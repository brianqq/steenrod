(defpackage steenrod
  (:use #:cl #:optima #:iterate #:checkl))
(in-package #:steenrod)

;;; som utilities
(defun partial (fn args)
  "Partially applies fn to args. Returns the function (fn arg1 arg2 ... argn _____): x1...xk -> (fn arg1 ... argn x1 ... xk)."
  (lambda (&rest inner-args)
    (apply fn args inner-args)))

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

(defun sgn (num exp)
  "Computes (-1)^num and uses it as the coefficient of exp."
  (if (evenp num) exp (list '-1 exp)))

(defun make-simplex (seq) (list :simplex seq))
(defun verts (simplex) (second simplex))
(defun dim (simplex) (1- (length (verts simplex))))
(defun standard-simp (dim)
  (make-simplex (apply #'vector (iterate (for i from 0 to dim) (collect i)))))

(def-morphism boundary (simplex)
  "Computes the boundary of a simplex"
  (let ((verts (verts simplex)))
    (if (<= (length verts) 1) 0
     (cons '+
	   (iterate (for v in-vector verts)
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
    ((list* car cdr) (if cdr (cons car (mapcar #'tidy cdr))))
    (_ expr)))

(defun mega-tidy (lst)
  (let ((tidied (tidy lst)))
    (if (equalp lst tidied) lst (mega-tidy tidied))))

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
     ((guard (list* op rest) (op-p op)) (cons op (mapcar #'self rest)))
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
     (iterate (for n from 0 to (dim simp))
	      (collect
		  (make-tensor
		   (simpify (iterate (for i from 0 to n) (collect i)))
		   (simpify (iterate (for i from n to (dim simp))
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
  (iterate (for i in-vector verts) (sum (ash 1 (1- i)))))

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
      (iterate (for i from 1 to (length seq))
	       (collect (nth (1- (lookup i)) seq))))))

(defun permute-tensor (perm tens)
  (cons :tensor (permute perm (cdr tens))))

(defun blue123 (x)
  (flatten-tensors
   (call (make-tensor #'identity (partial #'xi 1))
	 (xi 0 x))))

(defun red213 (x)
  (match (flatten-tensors
	  (call (make-tensor (partial #'xi 1) #'identity) (xi 0 x)))
    ((list :tensor a b c) (list :tensor b a c))))

(defpackage steenrod
  (:use #:cl #:optima #:iterate #:fare-memoization #:checkl))

(in-package #:steenrod)

(defun partial (fn args)
  "Partially applies fn to args. Returns the function (fn arg1 arg2 ... argn _____): x1...xk -> (fn arg1 ... argn x1 ... xk)."
  (lambda (&rest inner-args)
    (apply fn args inner-args)))

(defmacro afn (args &body body)
  `(labels ((self (,@args)
	      ,@body))
     #'self))

(defmacro aif (test true &optional false)
  `(let ((it ,test))
     (if it ,true ,false)))

(defmacro def-morphism (name (arg) &body body)
  `(defun ,name (,arg)
     (labels ((,name (,arg)
		,@body))
       (call #',name ,arg))))

(defun make-simplex (seq)
  (list :simplex seq))

(defun verts (simplex)
  (second simplex))

(defun dim (simplex) (1- (length (verts simplex))))

(defun standard-simp (dim)
  (make-simplex (apply #'vector (loop for i from 0 to dim collect i))))

(def-morphism boundary (simplex)
  "Computes the boundary of a simplex"
  (let ((verts (verts simplex)))
    (if (<= (length verts) 1) 0
     (cons '+
	   (iterate (for v in-vector verts)
		    (for sgn first nil then (not sgn))
		    (collect
			(let ((face (make-simplex (remove v verts))))
			  (if sgn `(-1 ,face) face))))))))

(defun dummy-coef (arg)
  (match arg
    ((guard (list k _) (numberp k)) arg)
    (_ (list 1 arg))))

(defun make-tensor (arg1 arg2)
  (let ((arg1 (dummy-coef arg1))
	(arg2 (dummy-coef arg2)))
   (match (list arg1 arg2)
     ((or (list (list k 0) _) (list _ (list j 0))) 0)
     ((list (list k x) (list z y)) (list (* k z) (list :tensor x y))))))

(defun left (tensor)
  (second tensor))
(defun right (tensor)
  (third tensor))

(def-morphism flip (simp)
  (match simp
    (0 0)
    ((list :tensor x y) (make-tensor y x))))

(defun tensor-p (x)
  (match x
    ((list :tensor _ _) t)
    (0 t)
    (_ nil)))

(defun op-p (op)
  (or (member op '(+ -)) (numberp op)))

(defun make-callable (fn-exp)
  "Interprets a function as defined by a symbolic linear combination of functions"
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
    ((guard (list* op exp) (op-p op))
     (lambda (arg)
       (cons op (mapcar (lambda (f) (funcall (make-callable f) arg)) exp))))
    (_ fn-exp)))

(defun extend-morphism (fn)
  "Extends a function on a basis to a morphism"
  (afn (expr)
   (match expr
     (0 0)
     ((guard (list* op rest) (op-p op)) (cons op (mapcar #'self rest)))
     (_ (funcall fn expr)))))

(defun tidy (expr)
  (match expr
    ((list '+) 0)
    ((list* '+ (list* '+ cdr) rest )  (append '(+) rest cdr)) ;must generalize
    ((list '+ x) x)
    ((list* '+ rest) (cons '+ (remove 0 (mapcar #'tidy rest))))
    ((list 0 _) 0)
    ((list 1 x) (tidy x))
    ((guard (list scalar 0) (numberp scalar)) 0)
    ((guard (list scalar (list* '+ rest)) (numberp scalar))  ;distributivity
     (cons '+ (mapcar (lambda (x) (list scalar (tidy x))) rest)))
    ((guard (list s1 (list s2 thing)) (and (numberp s1) (numberp s2)))
     (list (* s1 s2) (tidy thing)))
    ((list* car cdr) (if cdr (cons car (mapcar #'tidy cdr))))
    (_ expr)))

(defun call (fn-exp sexp)
  (tidy (funcall (extend-morphism (make-callable fn-exp)) sexp)))

(defun small-phi (k simp)
  (let ((dim (dim simp)))
    (if (= k (aref (verts simp) dim))		;is this check sufficient
	0
	(let* ((verts (verts simp))
	      (face (make-simplex (concatenate 'vector verts (list k)))))
	  (sgn (1+ dim) face)))))

(defun big-phi (k base)
  (let* ((phi-k (partial #'call (partial #'small-phi k)))
	 (id-tensor-phi (call (make-tensor #'identity phi-k) base)))
    (if (zerop (dim (right base)))
	(list '+ id-tensor-phi (make-tensor (funcall phi-k (left base))
					    (make-simplex (vector k))))
	id-tensor-phi)))

(defun sgn (num exp)
  (if (evenp num) exp (list '-1 exp)))

(defun xi-base (ei simp)
  (let* ((dim (dim simp))
	 (phi-k (partial #'big-phi (dim simp))))
    (match (list ei dim)
      ((list 0 0) (make-tensor simp simp))
      ((list _ 0) 0)
      ((list 0 _) (sgn dim (call phi-k (xi 0 (boundary simp)))))
      (_ (let ((left-recur (xi (1- ei) simp))
	       (right-recur (xi ei (boundary simp))))
	   (list '+
		 (list '+ (call phi-k left-recur) (call phi-k (flip left-recur)))
		 (sgn dim (call phi-k right-recur))))))))

(defun xi (ei exp)
  (call (partial #'xi-base ei) exp))



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
  (apply vector (loop for i from 0 to dim collect i)))

(defun boundary (simplex)
  "Computes the boundary of a simplex"
  (let ((verts (verts simplex)))
    (cons '+
	  (iterate (for v in-vector verts)
		   (for sgn first nil then (not sgn))
		   (collect
		       (let ((face (make-simplex (remove v verts))))
			   (if sgn `(- ,face) face)))))))

(defun make-tensor (arg1 arg2)
  (match (list arg1 arg2)
    ((or (list 0 _) (list _ 0)) 0)
    (_ (list :tensor arg1 arg2))))

(defun left (tensor)
  (second tensor))
(defun right (tensor)
  (third tensor)))

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
  (or (member op '(+ -)) (numberp op))))

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
     ((guard (list* op rest) (op-p op)) (cons op (mapcar #'self rest)))
     (_ (funcall fn expr)))))

(defun call (fn-exp sexp)
  (funcall (extend-morphism (make-callable fn-exp)) sexp))

(defun small-phi (k simp)
  (let ((dim (dim simp)))
    (if (< dim k) 			;is this check sufficient
	(let* ((sgn (oddp dim))
 	       (verts (verts simp))
	       (face (make-simplex (concatenate 'vector verts (list k)))))
	  (if sgn `(- ,face) face))
	0)))

(defun big-phi (k expr)
  (let ((phi-k (partial #'small-phi k)))
   (+ (call (make-tensor #'identity phi-k) expr)
      (if (= (dim (right expr)) 0)
	  (call
	   (make-tensor phi-k
			(lambda (x) (declare (ignore x)) (dim expr)))
	   expr)
	  0))))

(defun xi-base (ei simp)
  (let* ((dim (dim simp))
	 (st-simp ()))
   (if (= ei 0)
       (if (= dim 0)
	   (make-tensor simp simp)
	   0)
       (let ((left-recur (xi (1- ei) simp))
	     (right-recur (xi ei (boundary simp))))
	 (list '+
	       (big-phi dim (list '+ left-recur (flip left-recur)))
	       (if (oddp dim)
		   (- right-recur)
		   right-recur))))))

(defun xi (ei exp)
  (call (partial #'xi-base ei) exp))

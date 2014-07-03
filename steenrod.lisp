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

(defun make-simplex (seq)
  (list :simplex seq))

(defun verts (simplex)
  (second simplex))

(defun dim (simplex) (1- (length (verts simplex))))

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

(defun tensor-p (x)
  (match x
    ((list :tensor _ _) t)
    (0 t)
    (_ nil)))

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
	   ((list* op expr)	;linearity
	    (list op (mapcar #'self expr)))))))
    ((list* op exp)
     (lambda (arg)
       (cons op (mapcar (lambda (f) (funcall (make-callable f) arg)) exp))))
    (_ fn-exp)))

(defun extend-morphism (fn)
  "Extends a function on a basis to a morphism"
  (afn (expr)
   (match expr
     ((list* op rest)
      (cons op (mapcar #'self rest)))
     (_ (funcall fn expr)))))

(defun call-expr (fn-exp sexp)
  (funcall (extend-morphism (make-callable fn-expr)) sexp))

(defun small-phi (k simp)
  (let ((dim (dim simp)))
    (if (< dim k) 			;is this check sufficient
	(let* ((sgn (oddp dim))
 	       (verts (verts simp))
	       (face (make-simplex (concatenate 'vector verts (list k)))))
	  (if sgn `(- ,face) face))
	0)))


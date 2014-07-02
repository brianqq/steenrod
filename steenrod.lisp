(defpackage steenrod
  (:use #:cl #:optima #:iterate #:fare-memoization))

(in-package #:steenrod)

(defun partial (fn args)
  "Partially applies fn to args. Returns the function (fn arg1 arg2 ... argn _____): x1...xk -> (fn arg1 ... argn x1 ... xk)."
  (lambda (&rest inner-args)
    (apply fn args inner-args)))

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
  (list :tensor arg1 arg2))

(defun call (fn expr)
  "Extends functions defined on simplices by linearity"
  (match expr
    ((list :tensor x y)
     (match fn
       ((list :tensor f g) (make-tensor (call f x) (call g y)))
       (_ (error "not a tensor function"))))
    ((list* op rest)
     (cons op (mapcar (partial #'call fn) rest)))
    (_ (funcall fn expr))))

(defun small-phi (k simp)
  (let ((dim (dim simp)))
    (if (< dim k) 			;is this check sufficient
	(let* ((sgn (oddp dim))
 	       (verts (verts simp))
	       (face (make-simplex (concatenate 'vector verts (list k)))))
	  (if sgn `(- ,face) face))
	0)))


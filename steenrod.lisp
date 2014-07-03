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
    (if (<= (length verts) 1) 0
     (cons '+
	   (iterate (for v in-vector verts)
		    (for sgn first nil then (not sgn))
		    (collect
			(let ((face (make-simplex (remove v verts))))
			  (if sgn `(- ,face) face))))))))

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
    (if (= k (aref (verts simp) dim))		;is this check sufficient
	(let* ((sgn (oddp dim))
 	       (verts (verts simp))
	       (face (make-simplex (concatenate 'vector verts (list k)))))
	  (if sgn `(- ,face) face))
	0)))

(def-morphism big-phi (base)
  (let* ((k (dim (left base)))
	 (phi-k (partial #'small-phi k))
	 (id-tensor-phi (call (make-tensor #'identity phi-k) base)))
    (if (zerop k)
	(list '+ id-tensor-phi (make-tensor (funcall phi-k (left base))
					    (make-simplex (vector k))))
	id-tensor-phi)))

(defun sgn (num exp)
  (if (oddp num) (list '- exp) exp))

(defun xi-base (ei simp)
  (declare (optimize (debug 3)))
  (let* ((dim (dim simp)))
    (match (list ei dim)
      ((list 0 0) (make-tensor simp simp))
      ((list _ 0) 0)
      ((list 0 _) (sgn dim (big-phi (xi 0 (boundary simp)))))
      (_
       (let ((left-recur (xi (1- ei) simp))
	     (right-recur (sgn dim (xi ei (boundary simp)))))
	 (list '+
	       (big-phi (list '+ left-recur (flip left-recur)))
	       right-recur))))))

(defun xi (ei exp)
  (call (partial #'xi-base ei) exp))



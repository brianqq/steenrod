;;; proving <0 1 0 2 0> is not quadratic
;;; 
(defun  permute-step-basis (permutation step)
  (list :step (permute (second permutation) (second step))))

(permute-step-basis '(:perm (0 1)) '(:step (0 1)))

(defun permute-step (perm step)
  (call (partial #'permute-step-basis perm) step))

(permute-step '(+ (:perm (0 1))) '(+ (:step (0 1))))

;;; degree 4
(defparameter *pre-flip-deg4*
  (iter (for (_ x y z) in
	     '((join-two (:step (0 1))
		(:step (0 1 0 1))
		(:step (0))) 
	       (join-two (:step (0 1 0))
		(:step (0 1 0))
		(:step (0)))
	       (join-two (:step (0 1 0 1))
		(:step (0 1))
		(:step (0)))))
	(appending
	 (list (join-two x y z)
	       (join-two x (permute-step '(:perm (0 1)) y) z)))))

;;; deg 3
(defparameter *pre-flip-deg5*
  (iter (for (_ x y z) in
	     '((join-two (:step (0 1))
		(:step (0 1 0 1 0))
		(:step (0))) 
	       (join-two (:step (0 1 0))
		(:step (0 1 0 1))
		(:step (0)))
	       (join-two (:step (0 1 0 1))
		(:step (0 1 0))
		(:step (0)))
	       (join-two (:step (0 1 0 1 0))
		(:step (0 1))
		(:step (0)))))
	(appending
	 (list (join-two x y z)
	       (join-two x (permute-step '(:perm (0 1)) y) z)))))

(defparameter *s3* '((:perm ())
		     (:perm (0 1))
		     (:perm (0 2))
		     (:perm (1 2))
		     (:perm (0 1 2))
		     (:perm (0 2 1))))

(defun s3-act (steps)
  (mapcan (lambda (perm)
	    (mapcar (lambda (step)
		      (permute-step perm step))
		    steps))
	  *s3*))

(defparameter *deg4* (s3-act *pre-flip-deg4*))
(defparameter *deg5* (s3-act *pre-flip-deg5*))
(defparameter *bdd* (mapcar #'boundary *deg5*))

(defun get-leaves (exp)
  (let (acc)
    (labels ((walk (exp)
	       (match exp
		 ((list :step _) (push exp acc))
		 ((list* _) (mapc #'walk exp))
		 (_ nil))))
      (walk exp))
    acc))

(defparameter *deg4quad-basis* (remove-duplicates (append *deg4* *bdd*) :test #'equal))

(defparameter *all-things* (coerce
			    (remove-duplicates (get-leaves *deg4quad-basis*)
					       :test #'equal)
			    'vector))

(defparameter *pretty-basis*
  (iter (for eqn in
	     (iter (for eqn in *deg4quad-basis*)
		   (collect
		       (match eqn
			 ((list* '+ vecs) vecs)
			 (_ (list eqn))))))
	(collect
	    (iter (for vec in eqn)
		  (collect
		      (match vec
			((list :step _) (list 1 vec))
			(_ vec)))))))
  

(defun lookup (step)
  (position step *all-things* :test #'equal))

(defparameter *nrows* (length *all-things*))
(defparameter *ncols* (1+ (length *deg4quad-basis*)))
;;; row major order
;;; row: which step in all-things
;;; col: eqn/basis elt
(defparameter *matrix* (make-array (list *nrows* *ncols*)
				   :initial-element 0))
(iter (for eqn in *pretty-basis*)
      (for col from 0 below (length *pretty-basis*))
      (iter (for (a vec) in eqn)
	    (setf (aref *matrix* (lookup vec ) col) a)))

(setf (aref *matrix* (lookup '(:step (0 1 0 2 0))) (1- *ncols*)) 1)

(defmacro ssetf (&rest args)
  `(progn
     ,@(iter (for (x y) on args by #'cddr)
	     (collect
		 `(symbol-macrolet ((it ,x))
		    (setf it ,y))))))

(defmacro sreplace (thing new-thing)
  `(symbol-macrolet ((it ,thing))
     (replace it ,new-thing)))

(defun rows (mtx)
  (destructuring-bind (nrows ncols) (array-dimension mtx)
    (make-array
     nrows
     :initial-contents
     (iter (for r from 0 below nrows)
	   (collect
	       (make-array ncols
			   :displaced-to *matrix*
			   :displaced-index-offset (* r ncols)))))))

(defun swap-rows (mtx i j)
  (if (/= i j)
   (iter (for k from 0 below (array-dimension mtx 1))
	 (rotatef (aref mtx i k) (aref mtx j k)))))

(defun gauss-elim (mtx)
  (declare (optimize (safety 3) (speed 0) (debug 3)))
  (destructuring-bind (nrows ncols) (array-dimensions mtx)
    (let ((rows (rows mtx)))
     (iter (for i from 0 below (min nrows ncols))
	   (for pivot-pos = (position-if-not (lambda (x) (zerop (aref x i)))
					     rows :start i))
	   (when pivot-pos
	     (swap-rows mtx i pivot-pos)
	     (iter (for col from 0 below ncols)
		   (ssetf (aref mtx i col) (/ it (aref mtx i i))))
	     (iter (for j from 0 below nrows)
		   (for leading = (aref mtx j i))
		   (if (and (/= j i) (not (zerop leading)))
		       (sreplace (aref rows j)
				(map 'vector (lambda (x y) (- x (* y leading)))
				      it (aref rows i)))))))
     mtx)))

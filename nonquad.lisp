;;; proving <0 1 0 2 0> is not quadratic
;;; 
(defun  permute-step-basis (permutation step)
  (list :step (permute (second permutation) (second step))))

(permute-step-basis '(0 1) '(:step (0 1)))

(defun permute-step (perm step)
  (call (partial #'permute-step-basis perm) step))

(permute-step '(+ (:perm 0 1)) '(+ (:step (0 1))))

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
  (match exp 
    ((list* '+ args) (mapcan #'get-leaves args))
    ((list* :step _) (list exp)) 
    ((list* _) (get-leaves (cons '+ exp)))))

(defparameter *deg4quad-basis* (remove-duplicates (append *deg4* *bdd*) :test #'equal))

(defparameter *all-things* (coerce
			    (remove-duplicates (get-leaves *deg4quad-basis*)
					       :test #'equal)
			    'vector))

(defun get-pos (step)
  (position step *all-things* :test #'equal))

(defun translate (steps)
  (mapcar
   (lambda (vec)
     (match vec
       ((list* :step _) (list (get-pos vec)))
       ((list* + steps) (mapcar #'get-pos steps))))
   steps))

;;; row major order
;;; row: which step in all-things
;;; col=pow of 2: component in that row for col-th eqn in basis 
(defparameter *matrix* (make-array (length *all-things*) :initial-element 0))
(iter (for eqn in (translate *deg4quad-basis*))
      (for i first 0 then (1+ i)); pow of 2
      (iter (for vec in eqn)	 ; vec => row
	    (incf (aref *matrix* vec) (expt 2 i))))

(incf (aref *matrix* (get-pos '(:step (0 1 0 2 0)))) (expt 2 (length *all-things*)))

(defun n-bit (x n)
  (mod (ash x (- n)) 2))

(defun gauss-elim (mtx)
  (let ((len (length mtx)))
   (iter (for i from 0 below len)
	 (for pivot-pos = (position-if (lambda (x)
					 (= (n-bit x i) 1))
				       mtx 
				       :start i))
	 (when pivot-pos
	   (rotatef (aref mtx i) (aref mtx pivot-pos))
	   (iter (for j from 0 below len)
		 (if (and (/= j i)
			  (= (n-bit (aref mtx j) i) 1))
		     (setf (aref mtx j) (logxor (aref mtx i) (aref mtx j))))))))
  mtx)


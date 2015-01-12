(in-package #:steenrod)

(defun simplex-p (list)
  (and (eq (car list) :simplex)
       (vectorp (cadr list))))

(deftype simplex-type ()
  '(and list (satisfies simplex-p)))

(defun print-simplex (s simp)
  (format s "[~{~a~}]" (coerce (verts simp) 'list)))

;;; with spaces
;; (defun print-simplex (s simp)
;;   (format s "[~{~a~^ ~}]" (coerce (verts simp) 'list)))

(deftype tensor-type ()
  '(and list (satisfies gen-tensor-p)))

(defun print-tensor (s tensor)
  (format s "~{~{~a~}~^|~}" (iter (for x in (cdr tensor))
				  (collect (coerce (cadr x) 'list)))))

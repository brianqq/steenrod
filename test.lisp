(in-package #:steenrod)

(check () (make-tensor 0 'a))
(check () (make-tensor 'a 0))
(check () (make-tensor 'a 'b))

(check () (tensor-p 0))

(check ()
  (funcall (extend-morphism #'1+) '(+ ((* 5) 3) 2)))
(check ()
  (funcall (make-callable '(+ 1+ 1-)) 3))
(check ()
  (flip (make-tensor 'a 'b)))
(xi-base 2 (make-simplex #(0 1)))
(check ()
  (xi 0 (boundary (make-simplex #(0 1)))))
(check ()
  (standard-simp 0))
(check ()
  (standard-simp 1))
(check ()
  (dim (make-simplex #(0))))
(check ()
  (boundary (make-simplex #(0))))

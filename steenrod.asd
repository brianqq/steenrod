(asdf:defsystem #:steenrod
  :author "Brian Levy <brian_levy@brown.edu>"
  :depends-on (#:alexandria #:optima #:iterate #:fare-memoization)
  :components ((:file "steenrod")))

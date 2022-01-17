(set-option :produce-unsat-cores true)

(declare-const n Int)

(declare-fun margin (Int) Real)
(declare-fun target (Int) Real)
(declare-fun actual (Int) Real)
(declare-fun cool (Int) Bool)
(declare-fun heat (Int) Bool)
(declare-fun ok (Int) Bool)

; delta 0
(assert	(! (= (margin 0) 1.5) :named d0_h0))
(assert	(! (= (target 0) 70.0) :named d0_h1))
(assert (! (= (cool 0) (< (margin 0) (- (actual 0) (target 0)))) :named d0_h2))
(assert (! (= (heat 0) (> (- (margin 0)) (- (actual 0) (target 0)))) :named d0_h3))
(assert (! (=
	(ok 0) 
	(=>
		(or
			(> (- (target 0) (margin 0)) (actual 0))
			(> (actual 0) (+ (target 0) (margin 0))))
		(or (cool 0) (heat 0))
	)
) :named d0_h4))

(check-sat)

(assert (! (not (= (ok 0) true)) :named p0_h0))

(check-sat)
(get-unsat-core)
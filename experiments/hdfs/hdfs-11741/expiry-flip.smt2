; HDFS-11741 critical branch relation.
; Observed path: expiry >= receiveTime
; Flipped target: expiry < receiveTime

(set-logic QF_LIA)

(declare-const expiry Int)
(declare-const receiveTime Int)

; Both values are points on the non-negative runtime timeline.
(assert (>= expiry 0))
(assert (>= receiveTime 0))

(define-fun observedBranch () Bool (>= expiry receiveTime))
(define-fun flippedBranch () Bool (< expiry receiveTime))

(assert flippedBranch)
(check-sat)
(get-value (expiry receiveTime observedBranch flippedBranch))

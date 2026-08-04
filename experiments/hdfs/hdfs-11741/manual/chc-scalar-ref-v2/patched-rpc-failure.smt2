; HDFS-11741 with the real KeyManager expiry patch and a symbolic
; Balancer RPC failure before getRPC executes.
;
; Pure scalar target slice.  All 30 SystemState coordinates below correspond
; to source values, concrete nullable references (0 == Java null), or fields
; of those references.  nnQRef/rpcQRef/balQRef/hbQRef/dnQRef are the concrete
; results of allKeys.get(q), paired with the referenced BlockKey.expiryDate;
; they are not membership Booleans.  ekRef/ekId/ekExp is the real
; KeyManager.encryptionKey reference and its DataEncryptionKey fields. reqRef
; is the pending serialized request token, not an alias of the cached DEK.
;
; The RPC failure is an activation-local injectIOException branch before
; getRPC.  It starts with no outstanding successful response and stutters all
; program state.  No failure flag or counter is part of program state.
; AfterRpcFailure is a proof relation entered only by that branch; querying the
; target from this relation proves that every reported witness contains at
; least one RPC failure.

(set-logic HORN)
(set-option :fp.engine spacer)

; State order (all Int; reference 0 is null):
; wall elapsed K T q;
; nnCur nnNext nnSerial nnQRef nnQExp;
; rpcMsgRef rpcCur rpcQRef rpcQExp;
; balCur balQRef balQExp;
; hbMsgRef hbCur hbQRef hbQExp;
; dnCur dnQRef dnQExp;
; nextRef; ekRef ekId ekExp; reqRef reqKey.
(declare-rel Reach (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int))
(declare-rel AfterRpcFailure (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int))
(declare-rel BadAfterRpcFailure ())

(declare-var wall Int)
(declare-var elapsed Int)
(declare-var K Int)
(declare-var T Int)
(declare-var q Int)
(declare-var nnCur Int)
(declare-var nnNext Int)
(declare-var nnSerial Int)
(declare-var nnQRef Int)
(declare-var nnQExp Int)
(declare-var rpcMsgRef Int)
(declare-var rpcCur Int)
(declare-var rpcQRef Int)
(declare-var rpcQExp Int)
(declare-var balCur Int)
(declare-var balQRef Int)
(declare-var balQExp Int)
(declare-var hbMsgRef Int)
(declare-var hbCur Int)
(declare-var hbQRef Int)
(declare-var hbQExp Int)
(declare-var dnCur Int)
(declare-var dnQRef Int)
(declare-var dnQExp Int)
(declare-var nextRef Int)
(declare-var ekRef Int)
(declare-var ekId Int)
(declare-var ekExp Int)
(declare-var reqRef Int)
(declare-var reqKey Int)
(declare-var delta Int)
(declare-var injectIOException Int)

; Concrete workload initialization: q=17 is the initial current key.  NN,
; Balancer and DataNode hold distinct BlockKey objects for q, each expiring at
; 2*K+T.  No RPC/heartbeat message, DEK, or request exists yet.
(rule
  (=> (and (> K 0) (> T 0))
      (Reach 0 0 K T 17
             17 18 18 1 (+ (* 2 K) T)
             0 0 0 0
             17 2 (+ (* 2 K) T)
             0 0 0 0
             17 3 (+ (* 2 K) T)
             4 0 0 0 0 0)))

; Monotone environment clock (ordinary reachability).
(rule
  (=> (and
        (Reach wall elapsed K T q
               nnCur nnNext nnSerial nnQRef nnQExp
               rpcMsgRef rpcCur rpcQRef rpcQExp balCur
               balQRef balQExp hbMsgRef hbCur hbQRef
               hbQExp dnCur dnQRef dnQExp nextRef
               ekRef ekId ekExp reqRef reqKey)
        (> delta 0))
      (Reach (+ wall delta) (+ elapsed delta) K T q
             nnCur nnNext nnSerial nnQRef nnQExp
             rpcMsgRef rpcCur rpcQRef rpcQExp balCur
             balQRef balQExp hbMsgRef hbCur hbQRef
             hbQExp dnCur dnQRef dnQExp nextRef
             ekRef ekId ekExp reqRef reqKey)))

; Monotone environment clock (after a witnessed RPC failure).
(rule
  (=> (and
        (AfterRpcFailure wall elapsed K T q
                         nnCur nnNext nnSerial nnQRef nnQExp
                         rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                         balQRef balQExp hbMsgRef hbCur hbQRef
                         hbQExp dnCur dnQRef dnQExp nextRef
                         ekRef ekId ekExp reqRef reqKey)
        (> delta 0))
      (AfterRpcFailure (+ wall delta) (+ elapsed delta) K T q
                       nnCur nnNext nnSerial nnQRef nnQExp
                       rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                       balQRef balQExp hbMsgRef hbCur hbQRef
                       hbQExp dnCur dnQRef dnQExp nextRef
                       ekRef ekId ekExp reqRef reqKey)))

; One complete NameNode updateKeys activation (ordinary reachability).
(rule
  (=> (and
        (Reach wall elapsed K T q
               nnCur nnNext nnSerial nnQRef nnQExp
               rpcMsgRef rpcCur rpcQRef rpcQExp balCur
               balQRef balQExp hbMsgRef hbCur hbQRef
               hbQExp dnCur dnQRef dnQExp nextRef
               ekRef ekId ekExp reqRef reqKey)
        (> elapsed K))
      (Reach wall 0 K T q
             nnNext (+ nnSerial 1) (+ nnSerial 1) (ite (= (+ nnSerial 1) q) (+ nextRef 2) (ite (= nnNext q) (+ nextRef 1) (ite (= nnCur q) nextRef (ite (and (not (= nnQRef 0)) (< nnQExp wall)) 0 nnQRef)))) (ite (= (+ nnSerial 1) q) (+ wall (* 3 K) T) (ite (= nnNext q) (+ wall (* 2 K) T) (ite (= nnCur q) (+ wall K T) nnQExp)))
             rpcMsgRef rpcCur rpcQRef rpcQExp balCur
             balQRef balQExp hbMsgRef hbCur hbQRef
             hbQExp dnCur dnQRef dnQExp (+ nextRef 3)
             ekRef ekId ekExp reqRef reqKey)))

; One complete NameNode updateKeys activation (after a witnessed RPC failure).
(rule
  (=> (and
        (AfterRpcFailure wall elapsed K T q
                         nnCur nnNext nnSerial nnQRef nnQExp
                         rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                         balQRef balQExp hbMsgRef hbCur hbQRef
                         hbQExp dnCur dnQRef dnQExp nextRef
                         ekRef ekId ekExp reqRef reqKey)
        (> elapsed K))
      (AfterRpcFailure wall 0 K T q
                       nnNext (+ nnSerial 1) (+ nnSerial 1) (ite (= (+ nnSerial 1) q) (+ nextRef 2) (ite (= nnNext q) (+ nextRef 1) (ite (= nnCur q) nextRef (ite (and (not (= nnQRef 0)) (< nnQExp wall)) 0 nnQRef)))) (ite (= (+ nnSerial 1) q) (+ wall (* 3 K) T) (ite (= nnNext q) (+ wall (* 2 K) T) (ite (= nnCur q) (+ wall K T) nnQExp)))
                       rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                       balQRef balQExp hbMsgRef hbCur hbQRef
                       hbQExp dnCur dnQRef dnQExp (+ nextRef 3)
                       ekRef ekId ekExp reqRef reqKey)))

; NameNode getBlockKeys snapshot for the Balancer (ordinary reachability).
(rule
  (=> (and
        (Reach wall elapsed K T q
               nnCur nnNext nnSerial nnQRef nnQExp
               rpcMsgRef rpcCur rpcQRef rpcQExp balCur
               balQRef balQExp hbMsgRef hbCur hbQRef
               hbQExp dnCur dnQRef dnQExp nextRef
               ekRef ekId ekExp reqRef reqKey)
        (= rpcMsgRef 0))
      (Reach wall elapsed K T q
             nnCur nnNext nnSerial nnQRef nnQExp
             nextRef nnCur
             (ite (= nnQRef 0) 0 (+ nextRef 1)) nnQExp balCur
             balQRef balQExp hbMsgRef hbCur hbQRef
             hbQExp dnCur dnQRef dnQExp
             (ite (= nnQRef 0) (+ nextRef 1) (+ nextRef 2))
             ekRef ekId ekExp reqRef reqKey)))

; NameNode getBlockKeys snapshot for the Balancer (after a witnessed RPC failure).
(rule
  (=> (and
        (AfterRpcFailure wall elapsed K T q
                         nnCur nnNext nnSerial nnQRef nnQExp
                         rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                         balQRef balQExp hbMsgRef hbCur hbQRef
                         hbQExp dnCur dnQRef dnQExp nextRef
                         ekRef ekId ekExp reqRef reqKey)
        (= rpcMsgRef 0))
      (AfterRpcFailure wall elapsed K T q
                       nnCur nnNext nnSerial nnQRef nnQExp
                       nextRef nnCur
                       (ite (= nnQRef 0) 0 (+ nextRef 1)) nnQExp balCur
                       balQRef balQExp hbMsgRef hbCur hbQRef
                       hbQExp dnCur dnQRef dnQExp
                       (ite (= nnQRef 0) (+ nextRef 1) (+ nextRef 2))
                       ekRef ekId ekExp reqRef reqKey)))

; Balancer activation, injectIOException=false.  The response is consumed and
; the real addKeys effects update currentKey and the concrete q lookup.
; Successful Balancer activation
(rule
  (=> (and
        (Reach wall elapsed K T q
               nnCur nnNext nnSerial nnQRef nnQExp
               rpcMsgRef rpcCur rpcQRef rpcQExp balCur
               balQRef balQExp hbMsgRef hbCur hbQRef
               hbQExp dnCur dnQRef dnQExp nextRef
               ekRef ekId ekExp reqRef reqKey)
        (and (not (= rpcMsgRef 0)) (= injectIOException 0)))
      (Reach wall elapsed K T q
             nnCur nnNext nnSerial nnQRef nnQExp
             0 rpcCur rpcQRef rpcQExp rpcCur
             (ite (not (= rpcQRef 0)) rpcQRef (ite (and (not (= balQRef 0)) (< balQExp wall)) 0 balQRef)) (ite (not (= rpcQRef 0)) rpcQExp balQExp) hbMsgRef hbCur hbQRef
             hbQExp dnCur dnQRef dnQExp nextRef
             ekRef ekId ekExp reqRef reqKey)))

; Successful later Balancer activation
(rule
  (=> (and
        (AfterRpcFailure wall elapsed K T q
                         nnCur nnNext nnSerial nnQRef nnQExp
                         rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                         balQRef balQExp hbMsgRef hbCur hbQRef
                         hbQExp dnCur dnQRef dnQExp nextRef
                         ekRef ekId ekExp reqRef reqKey)
        (and (not (= rpcMsgRef 0)) (= injectIOException 0)))
      (AfterRpcFailure wall elapsed K T q
                       nnCur nnNext nnSerial nnQRef nnQExp
                       0 rpcCur rpcQRef rpcQExp rpcCur
                       (ite (not (= rpcQRef 0)) rpcQRef (ite (and (not (= balQRef 0)) (< balQExp wall)) 0 balQRef)) (ite (not (= rpcQRef 0)) rpcQExp balQExp) hbMsgRef hbCur hbQRef
                       hbQExp dnCur dnQRef dnQExp nextRef
                       ekRef ekId ekExp reqRef reqKey)))

; Balancer activation, injectIOException=true.  The hook throws before
; getRPC(), so rpcMsgRef must be null: no success response is produced or
; consumed.  Every program field stutters.  This is the only entry into the
; proof relation--failure history is not a SystemState coordinate.
; Witnessed activation-local Balancer RPC failure
(rule
  (=> (and
        (Reach wall elapsed K T q
               nnCur nnNext nnSerial nnQRef nnQExp
               rpcMsgRef rpcCur rpcQRef rpcQExp balCur
               balQRef balQExp hbMsgRef hbCur hbQRef
               hbQExp dnCur dnQRef dnQExp nextRef
               ekRef ekId ekExp reqRef reqKey)
        (and (= rpcMsgRef 0) (= injectIOException 1)))
      (AfterRpcFailure wall elapsed K T q
                       nnCur nnNext nnSerial nnQRef nnQExp
                       rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                       balQRef balQExp hbMsgRef hbCur hbQRef
                       hbQExp dnCur dnQRef dnQExp nextRef
                       ekRef ekId ekExp reqRef reqKey)))

; A later activation-local Balancer RPC failure
(rule
  (=> (and
        (AfterRpcFailure wall elapsed K T q
                         nnCur nnNext nnSerial nnQRef nnQExp
                         rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                         balQRef balQExp hbMsgRef hbCur hbQRef
                         hbQExp dnCur dnQRef dnQExp nextRef
                         ekRef ekId ekExp reqRef reqKey)
        (and (= rpcMsgRef 0) (= injectIOException 1)))
      (AfterRpcFailure wall elapsed K T q
                       nnCur nnNext nnSerial nnQRef nnQExp
                       rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                       balQRef balQExp hbMsgRef hbCur hbQRef
                       hbQExp dnCur dnQRef dnQExp nextRef
                       ekRef ekId ekExp reqRef reqKey)))


; NameNode heartbeat snapshot (ordinary reachability).
(rule
  (=> (and
        (Reach wall elapsed K T q
               nnCur nnNext nnSerial nnQRef nnQExp
               rpcMsgRef rpcCur rpcQRef rpcQExp balCur
               balQRef balQExp hbMsgRef hbCur hbQRef
               hbQExp dnCur dnQRef dnQExp nextRef
               ekRef ekId ekExp reqRef reqKey)
        (= hbMsgRef 0))
      (Reach wall elapsed K T q
             nnCur nnNext nnSerial nnQRef nnQExp
             rpcMsgRef rpcCur rpcQRef rpcQExp balCur
             balQRef balQExp nextRef nnCur
             (ite (= nnQRef 0) 0 (+ nextRef 1))
             nnQExp dnCur dnQRef dnQExp
             (ite (= nnQRef 0) (+ nextRef 1) (+ nextRef 2))
             ekRef ekId ekExp reqRef reqKey)))

; NameNode heartbeat snapshot (after a witnessed RPC failure).
(rule
  (=> (and
        (AfterRpcFailure wall elapsed K T q
                         nnCur nnNext nnSerial nnQRef nnQExp
                         rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                         balQRef balQExp hbMsgRef hbCur hbQRef
                         hbQExp dnCur dnQRef dnQExp nextRef
                         ekRef ekId ekExp reqRef reqKey)
        (= hbMsgRef 0))
      (AfterRpcFailure wall elapsed K T q
                       nnCur nnNext nnSerial nnQRef nnQExp
                       rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                       balQRef balQExp nextRef nnCur
                       (ite (= nnQRef 0) 0 (+ nextRef 1))
                       nnQExp dnCur dnQRef dnQExp
                       (ite (= nnQRef 0) (+ nextRef 1) (+ nextRef 2))
                       ekRef ekId ekExp reqRef reqKey)))

; DataNode addKeys activation (ordinary reachability).
(rule
  (=> (and
        (Reach wall elapsed K T q
               nnCur nnNext nnSerial nnQRef nnQExp
               rpcMsgRef rpcCur rpcQRef rpcQExp balCur
               balQRef balQExp hbMsgRef hbCur hbQRef
               hbQExp dnCur dnQRef dnQExp nextRef
               ekRef ekId ekExp reqRef reqKey)
        (not (= hbMsgRef 0)))
      (Reach wall elapsed K T q
             nnCur nnNext nnSerial nnQRef nnQExp
             rpcMsgRef rpcCur rpcQRef rpcQExp balCur
             balQRef balQExp 0 hbCur hbQRef
             hbQExp hbCur (ite (not (= hbQRef 0)) hbQRef (ite (and (not (= dnQRef 0)) (< dnQExp wall)) 0 dnQRef)) (ite (not (= hbQRef 0)) hbQExp dnQExp) nextRef
             ekRef ekId ekExp reqRef reqKey)))

; DataNode addKeys activation (after a witnessed RPC failure).
(rule
  (=> (and
        (AfterRpcFailure wall elapsed K T q
                         nnCur nnNext nnSerial nnQRef nnQExp
                         rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                         balQRef balQExp hbMsgRef hbCur hbQRef
                         hbQExp dnCur dnQRef dnQExp nextRef
                         ekRef ekId ekExp reqRef reqKey)
        (not (= hbMsgRef 0)))
      (AfterRpcFailure wall elapsed K T q
                       nnCur nnNext nnSerial nnQRef nnQExp
                       rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                       balQRef balQExp 0 hbCur hbQRef
                       hbQExp hbCur (ite (not (= hbQRef 0)) hbQRef (ite (and (not (= dnQRef 0)) (< dnQExp wall)) 0 dnQRef)) (ite (not (= hbQRef 0)) hbQExp dnQExp) nextRef
                       ekRef ekId ekExp reqRef reqKey)))

; Patched sender regeneration: encryptionKey is null or expired (ordinary reachability).
(rule
  (=> (and
        (Reach wall elapsed K T q
               nnCur nnNext nnSerial nnQRef nnQExp
               rpcMsgRef rpcCur rpcQRef rpcQExp balCur
               balQRef balQExp hbMsgRef hbCur hbQRef
               hbQExp dnCur dnQRef dnQExp nextRef
               ekRef ekId ekExp reqRef reqKey)
        (or (= ekRef 0) (< ekExp wall)))
      (Reach wall elapsed K T q
             nnCur nnNext nnSerial nnQRef nnQExp
             rpcMsgRef rpcCur rpcQRef rpcQExp balCur
             balQRef balQExp hbMsgRef hbCur hbQRef
             hbQExp dnCur dnQRef dnQExp (+ nextRef 2)
             nextRef balCur (+ wall T) (+ nextRef 1) balCur)))

; Patched sender regeneration: encryptionKey is null or expired (after a witnessed RPC failure).
(rule
  (=> (and
        (AfterRpcFailure wall elapsed K T q
                         nnCur nnNext nnSerial nnQRef nnQExp
                         rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                         balQRef balQExp hbMsgRef hbCur hbQRef
                         hbQExp dnCur dnQRef dnQExp nextRef
                         ekRef ekId ekExp reqRef reqKey)
        (or (= ekRef 0) (< ekExp wall)))
      (AfterRpcFailure wall elapsed K T q
                       nnCur nnNext nnSerial nnQRef nnQExp
                       rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                       balQRef balQExp hbMsgRef hbCur hbQRef
                       hbQExp dnCur dnQRef dnQExp (+ nextRef 2)
                       nextRef balCur (+ wall T) (+ nextRef 1) balCur)))

; Patched sender cache hit on a non-expired real DEK reference (ordinary reachability).
(rule
  (=> (and
        (Reach wall elapsed K T q
               nnCur nnNext nnSerial nnQRef nnQExp
               rpcMsgRef rpcCur rpcQRef rpcQExp balCur
               balQRef balQExp hbMsgRef hbCur hbQRef
               hbQExp dnCur dnQRef dnQExp nextRef
               ekRef ekId ekExp reqRef reqKey)
        (and (not (= ekRef 0)) (>= ekExp wall)))
      (Reach wall elapsed K T q
             nnCur nnNext nnSerial nnQRef nnQExp
             rpcMsgRef rpcCur rpcQRef rpcQExp balCur
             balQRef balQExp hbMsgRef hbCur hbQRef
             hbQExp dnCur dnQRef dnQExp (+ nextRef 1)
             ekRef ekId ekExp nextRef ekId)))

; Patched sender cache hit on a non-expired real DEK reference (after a witnessed RPC failure).
(rule
  (=> (and
        (AfterRpcFailure wall elapsed K T q
                         nnCur nnNext nnSerial nnQRef nnQExp
                         rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                         balQRef balQExp hbMsgRef hbCur hbQRef
                         hbQExp dnCur dnQRef dnQExp nextRef
                         ekRef ekId ekExp reqRef reqKey)
        (and (not (= ekRef 0)) (>= ekExp wall)))
      (AfterRpcFailure wall elapsed K T q
                       nnCur nnNext nnSerial nnQRef nnQExp
                       rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                       balQRef balQExp hbMsgRef hbCur hbQRef
                       hbQExp dnCur dnQRef dnQExp (+ nextRef 1)
                       ekRef ekId ekExp nextRef ekId)))

; Normal SASL receiver lookup consumes the request (ordinary reachability).
(rule
  (=> (and
        (Reach wall elapsed K T q
               nnCur nnNext nnSerial nnQRef nnQExp
               rpcMsgRef rpcCur rpcQRef rpcQExp balCur
               balQRef balQExp hbMsgRef hbCur hbQRef
               hbQExp dnCur dnQRef dnQExp nextRef
               ekRef ekId ekExp reqRef reqKey)
        (and (not (= reqRef 0)) (= reqKey q) (not (= dnQRef 0))))
      (Reach wall elapsed K T q
             nnCur nnNext nnSerial nnQRef nnQExp
             rpcMsgRef rpcCur rpcQRef rpcQExp balCur
             balQRef balQExp hbMsgRef hbCur hbQRef
             hbQExp dnCur dnQRef dnQExp nextRef
             ekRef ekId ekExp 0 reqKey)))

; Normal SASL receiver lookup consumes the request (after a witnessed RPC failure).
(rule
  (=> (and
        (AfterRpcFailure wall elapsed K T q
                         nnCur nnNext nnSerial nnQRef nnQExp
                         rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                         balQRef balQExp hbMsgRef hbCur hbQRef
                         hbQExp dnCur dnQRef dnQExp nextRef
                         ekRef ekId ekExp reqRef reqKey)
        (and (not (= reqRef 0)) (= reqKey q) (not (= dnQRef 0))))
      (AfterRpcFailure wall elapsed K T q
                       nnCur nnNext nnSerial nnQRef nnQExp
                       rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                       balQRef balQExp hbMsgRef hbCur hbQRef
                       hbQExp dnCur dnQRef dnQExp nextRef
                       ekRef ekId ekExp 0 reqKey)))

; Exact exceptional predicate:
;   requestRef != null && allKeys.get(request.keyId) == null.
; reqKey=q connects the real DEK keyId to the demand-selected nullable lookup.
(rule
  (=> (and
        (AfterRpcFailure wall elapsed K T q
                         nnCur nnNext nnSerial nnQRef nnQExp
                         rpcMsgRef rpcCur rpcQRef rpcQExp balCur
                         balQRef balQExp hbMsgRef hbCur hbQRef
                         hbQExp dnCur dnQRef dnQExp nextRef
                         ekRef ekId ekExp reqRef reqKey)
        (not (= reqRef 0))
        (= reqKey q)
        (= dnQRef 0))
      BadAfterRpcFailure))

(query BadAfterRpcFailure)

; HDFS-11741 with the real KeyManager expiry patch, successful RPC/delivery.
;
; Property-directed container projection: q is the request key, initially the
; NameNode current key.  roleHas/roleExpiry is exactly the observation
; allKeys.get(q) and its expiry.  For this observer, the VM container loops are:
; removeExpired => has && expiry>=now; export => copy; addKeys => remove local
; expired q, then overwrite it iff the exported fixed array contains q.
; No whole-container equality or closed-form map approximation is claimed.
;
; Inv closes arbitrary interleavings of seven real regions.  TICK encodes an
; environment invariant assumed from failure-free bounded scheduling: before
; q's retirement, Balancer refreshes soon enough that a stale current q cannot
; mint a DEK extending beyond NN retention.  reqWall=wall says the one-shot
; SASL transfer is delivered without an additional logical-clock tick.  Thus
; UNSAT below is conditional on successful bounded refresh/delivery; it is not
; a claim about unbounded delay or IOException executions.
; The workload fixes encryptDataTransfer=true.  cacheValid=false represents
; the real encryptionKey==null state.  The encryptDataTransfer=false branch
; returns null and cannot reach retrieveDataEncryptionKey, so this
; target-directed model slices that branch away.

(set-logic HORN)
(set-option :fp.engine spacer)

(define-fun liveQ ((has Bool) (expiry Int) (now Int)) Bool
  (and has (>= expiry now)))
(define-fun overlayHasQ ((oldHas Bool) (oldExpiry Int)
                         (incomingHas Bool) (now Int)) Bool
  (or incomingHas (liveQ oldHas oldExpiry now)))
(define-fun overlayExpiryQ ((oldExpiry Int) (incomingHas Bool)
                            (incomingExpiry Int)) Int
  (ite incomingHas incomingExpiry oldExpiry))

; wall, intervals; NN; RPC; Balancer; heartbeat; DataNode; cache; request;
; failure flag (always false in this success-only file).
(declare-rel Inv
  (Int Int Int Bool Bool Int Bool Bool Bool Int Bool Bool Int Bool
   Bool Bool Int Bool Bool Int Bool Bool Bool Int Bool Bool Int Bool))
(declare-rel Bad ())

(declare-var wall Int)
(declare-var keyInterval Int)
(declare-var lifetime Int)
(declare-var delta Int)
(declare-var rotated Bool)
(declare-var nnHas Bool)
(declare-var nnExpiry Int)
(declare-var nnCurrentQ Bool)
(declare-var rpcValid Bool)
(declare-var rpcHas Bool)
(declare-var rpcExpiry Int)
(declare-var rpcCurrentQ Bool)
(declare-var balancerHas Bool)
(declare-var balancerExpiry Int)
(declare-var balancerCurrentQ Bool)
(declare-var heartbeatValid Bool)
(declare-var heartbeatHas Bool)
(declare-var heartbeatExpiry Int)
(declare-var heartbeatCurrentQ Bool)
(declare-var datanodeHas Bool)
(declare-var datanodeExpiry Int)
(declare-var datanodeCurrentQ Bool)
(declare-var cacheValid Bool)
(declare-var cacheQ Bool)
(declare-var cacheExpiry Int)
(declare-var requestValid Bool)
(declare-var requestQ Bool)
(declare-var requestWall Int)
(declare-var seenFailure Bool)

(rule
  (=> (and (> keyInterval 0) (> lifetime 0))
      (Inv 0 keyInterval lifetime
           false true (+ (* 2 keyInterval) lifetime) true
           false false 0 false
           true (+ (* 2 keyInterval) lifetime) true
           false false 0 false
           true (+ (* 2 keyInterval) lifetime) true
           false false 0 false false 0 false)))

; Successful periodic-refresh timing invariant.
(rule
  (=> (and
        (Inv wall keyInterval lifetime rotated nnHas nnExpiry nnCurrentQ
             rpcValid rpcHas rpcExpiry rpcCurrentQ
             balancerHas balancerExpiry balancerCurrentQ
             heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
             datanodeHas datanodeExpiry datanodeCurrentQ
             cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
             seenFailure)
        (> delta 0)
        (or (not rotated) (not balancerCurrentQ)
            (<= (+ (+ wall delta) lifetime) nnExpiry)))
      (Inv (+ wall delta) keyInterval lifetime
           rotated nnHas nnExpiry nnCurrentQ
           rpcValid rpcHas rpcExpiry rpcCurrentQ
           balancerHas balancerExpiry balancerCurrentQ
           heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
           datanodeHas datanodeExpiry datanodeCurrentQ
           cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
           seenFailure)))

; REGION 1 / NN_UPDATE: first rotation retires q.
(rule
  (=> (and
        (Inv wall keyInterval lifetime rotated nnHas nnExpiry nnCurrentQ
             rpcValid rpcHas rpcExpiry rpcCurrentQ
             balancerHas balancerExpiry balancerCurrentQ
             heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
             datanodeHas datanodeExpiry datanodeCurrentQ
             cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
             seenFailure)
        (not rotated))
      (Inv wall keyInterval lifetime
           true true (+ wall keyInterval lifetime) false
           rpcValid rpcHas rpcExpiry rpcCurrentQ
           balancerHas balancerExpiry balancerCurrentQ
           heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
           datanodeHas datanodeExpiry datanodeCurrentQ
           cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
           seenFailure)))

; REGION 1 / later loop iterations: only removeExpiredKeys can affect q.
(rule
  (=> (and
        (Inv wall keyInterval lifetime rotated nnHas nnExpiry nnCurrentQ
             rpcValid rpcHas rpcExpiry rpcCurrentQ
             balancerHas balancerExpiry balancerCurrentQ
             heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
             datanodeHas datanodeExpiry datanodeCurrentQ
             cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
             seenFailure)
        rotated)
      (Inv wall keyInterval lifetime
           rotated (liveQ nnHas nnExpiry wall) nnExpiry false
           rpcValid rpcHas rpcExpiry rpcCurrentQ
           balancerHas balancerExpiry balancerCurrentQ
           heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
           datanodeHas datanodeExpiry datanodeCurrentQ
           cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
           seenFailure)))

; REGION 2 / NN_RPC_EXPORT.
(rule
  (=>
    (Inv wall keyInterval lifetime rotated nnHas nnExpiry nnCurrentQ
         rpcValid rpcHas rpcExpiry rpcCurrentQ
         balancerHas balancerExpiry balancerCurrentQ
         heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
         datanodeHas datanodeExpiry datanodeCurrentQ
         cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
         seenFailure)
    (Inv wall keyInterval lifetime rotated nnHas nnExpiry nnCurrentQ
         true nnHas nnExpiry nnCurrentQ
         balancerHas balancerExpiry balancerCurrentQ
         heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
         datanodeHas datanodeExpiry datanodeCurrentQ
         cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
         seenFailure)))

; REGION 3 / BALANCER_REFRESH: successful response, real addKeys observer.
(rule
  (=> (and
        (Inv wall keyInterval lifetime rotated nnHas nnExpiry nnCurrentQ
             rpcValid rpcHas rpcExpiry rpcCurrentQ
             balancerHas balancerExpiry balancerCurrentQ
             heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
             datanodeHas datanodeExpiry datanodeCurrentQ
             cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
             seenFailure)
        rpcValid)
      (Inv wall keyInterval lifetime rotated nnHas nnExpiry nnCurrentQ
           false rpcHas rpcExpiry rpcCurrentQ
           (overlayHasQ balancerHas balancerExpiry rpcHas wall)
           (overlayExpiryQ balancerExpiry rpcHas rpcExpiry) rpcCurrentQ
           heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
           datanodeHas datanodeExpiry datanodeCurrentQ
           cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
           false)))

; REGION 4 / NN_HEARTBEAT_EXPORT.
(rule
  (=>
    (Inv wall keyInterval lifetime rotated nnHas nnExpiry nnCurrentQ
         rpcValid rpcHas rpcExpiry rpcCurrentQ
         balancerHas balancerExpiry balancerCurrentQ
         heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
         datanodeHas datanodeExpiry datanodeCurrentQ
         cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
         seenFailure)
    (Inv wall keyInterval lifetime rotated nnHas nnExpiry nnCurrentQ
         rpcValid rpcHas rpcExpiry rpcCurrentQ
         balancerHas balancerExpiry balancerCurrentQ
         true nnHas nnExpiry nnCurrentQ
         datanodeHas datanodeExpiry datanodeCurrentQ
         cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
         seenFailure)))

; REGION 5 / DN_REFRESH: successful heartbeat delivery, real addKeys observer.
(rule
  (=> (and
        (Inv wall keyInterval lifetime rotated nnHas nnExpiry nnCurrentQ
             rpcValid rpcHas rpcExpiry rpcCurrentQ
             balancerHas balancerExpiry balancerCurrentQ
             heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
             datanodeHas datanodeExpiry datanodeCurrentQ
             cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
             seenFailure)
        heartbeatValid)
      (Inv wall keyInterval lifetime rotated nnHas nnExpiry nnCurrentQ
           rpcValid rpcHas rpcExpiry rpcCurrentQ
           balancerHas balancerExpiry balancerCurrentQ
           false heartbeatHas heartbeatExpiry heartbeatCurrentQ
           (overlayHasQ datanodeHas datanodeExpiry heartbeatHas wall)
           (overlayExpiryQ datanodeExpiry heartbeatHas heartbeatExpiry)
           heartbeatCurrentQ
           cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
           seenFailure)))

; REGION 6 / DISPATCHER_SENDER, patched source:
;   encryptionKey == null || encryptionKey.expiryDate < timer.now()
; regenerates from the synchronized Balancer currentKey; otherwise it reuses.
(rule
  (=> (and
        (Inv wall keyInterval lifetime rotated nnHas nnExpiry nnCurrentQ
             rpcValid rpcHas rpcExpiry rpcCurrentQ
             balancerHas balancerExpiry balancerCurrentQ
             heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
             datanodeHas datanodeExpiry datanodeCurrentQ
             cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
             seenFailure)
        (or (not cacheValid) (< cacheExpiry wall)))
      (Inv wall keyInterval lifetime rotated nnHas nnExpiry nnCurrentQ
           rpcValid rpcHas rpcExpiry rpcCurrentQ
           balancerHas balancerExpiry balancerCurrentQ
           heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
           datanodeHas datanodeExpiry datanodeCurrentQ
           true balancerCurrentQ (+ wall lifetime)
           true balancerCurrentQ wall seenFailure)))

(rule
  (=> (and
        (Inv wall keyInterval lifetime rotated nnHas nnExpiry nnCurrentQ
             rpcValid rpcHas rpcExpiry rpcCurrentQ
             balancerHas balancerExpiry balancerCurrentQ
             heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
             datanodeHas datanodeExpiry datanodeCurrentQ
             cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
             seenFailure)
        cacheValid (>= cacheExpiry wall))
      (Inv wall keyInterval lifetime rotated nnHas nnExpiry nnCurrentQ
           rpcValid rpcHas rpcExpiry rpcCurrentQ
           balancerHas balancerExpiry balancerCurrentQ
           heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
           datanodeHas datanodeExpiry datanodeCurrentQ
           cacheValid cacheQ cacheExpiry true cacheQ wall seenFailure)))

; REGION 7 / SASL_RECEIVER_TARGET, normal and exceptional lookup branches.
(rule
  (=> (and
        (Inv wall keyInterval lifetime rotated nnHas nnExpiry nnCurrentQ
             rpcValid rpcHas rpcExpiry rpcCurrentQ
             balancerHas balancerExpiry balancerCurrentQ
             heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
             datanodeHas datanodeExpiry datanodeCurrentQ
             cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
             seenFailure)
        requestValid (= requestWall wall)
        (or (not requestQ) datanodeHas))
      (Inv wall keyInterval lifetime rotated nnHas nnExpiry nnCurrentQ
           rpcValid rpcHas rpcExpiry rpcCurrentQ
           balancerHas balancerExpiry balancerCurrentQ
           heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
           datanodeHas datanodeExpiry datanodeCurrentQ
           cacheValid cacheQ cacheExpiry false requestQ requestWall
           seenFailure)))

(rule
  (=> (and
        (Inv wall keyInterval lifetime rotated nnHas nnExpiry nnCurrentQ
             rpcValid rpcHas rpcExpiry rpcCurrentQ
             balancerHas balancerExpiry balancerCurrentQ
             heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
             datanodeHas datanodeExpiry datanodeCurrentQ
             cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
             seenFailure)
        requestValid (= requestWall wall) requestQ (not datanodeHas))
      Bad))

(query Bad)

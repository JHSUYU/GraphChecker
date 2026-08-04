; HDFS-11741 with the expiry patch and symbolic Balancer response failure.
;
; q-observer projection (honest scope): roleHas/roleExpiry denotes exactly
; allKeys.get(q) and that entry's expiry for one distinguished request key q.
; removeExpiredKeys, exportKeys, and addKeys are projected pointwise exactly;
; no claim is made that the rest of a Map is equal or summarized.
;
; The seven region transformers are the same as patched.smt2.  REGION 3 has
; one extra VM-visible path from hdfs-11741-symbolic-rpc-hook.patch:
; injectIOException=true returns false before blockTokenSecretManager.addKeys,
; leaving Balancer state unchanged.  Java evaluates namenode.getBlockKeys()
; before entering that helper, so this is precisely response-delivery loss,
; not literally a pre-call transport failure.  getBlockKeys is a read-only
; snapshot here, hence both failures have the same local coordination effect.
;
; seenFailure releases the success-only refresh deadline in TICK.  This models
; the real consequence of a failed updater iteration: Balancer may retain q as
; current after NN/DN retire it.  The patched sender then creates a brand-new,
; unexpired DEK from that stale current q, so the target remains reachable.
; seenFailure abstracts one or more consecutive response drops, or an
; unbounded delay before the next successful refresh.  This model does not
; establish that one failed periodic attempt is sufficient.  It covers the
; Balancer response-delivery failure, not a DataNode heartbeat failure.
; The workload fixes encryptDataTransfer=true.  cacheValid=false represents
; the real encryptionKey==null state; the target-directed model slices away
; the false branch because it returns null and cannot reach the target.

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

; Clock/environment step.  Before a failure it obeys the same bounded,
; successful refresh invariant as patched.smt2.  A failed updater iteration
; removes that guarantee until a later successful Balancer refresh.
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
        (or (not rotated) seenFailure (not balancerCurrentQ)
            (<= (+ (+ wall delta) lifetime) nnExpiry)))
      (Inv (+ wall delta) keyInterval lifetime
           rotated nnHas nnExpiry nnCurrentQ
           rpcValid rpcHas rpcExpiry rpcCurrentQ
           balancerHas balancerExpiry balancerCurrentQ
           heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
           datanodeHas datanodeExpiry datanodeCurrentQ
           cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
           seenFailure)))

; REGION 1 / NN_UPDATE, first rotation.
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

; REGION 1 / later iterations: remove expired q.
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

; REGION 2 / NN_RPC_EXPORT, the read-only server snapshot.
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

; REGION 3 / BALANCER_REFRESH, successful delivery and real addKeys observer.
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

; REGION 3 / symbolic IOException path: consume/drop this response but perform
; no removeExpiredKeys, currentKey write, or map PUT on the Balancer.
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
           balancerHas balancerExpiry balancerCurrentQ
           heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
           datanodeHas datanodeExpiry datanodeCurrentQ
           cacheValid cacheQ cacheExpiry requestValid requestQ requestWall
           true)))

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

; REGION 5 / DN_REFRESH, successful heartbeat delivery.
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

; REGION 6 / patched DISPATCHER_SENDER.
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

; REGION 7 / SASL_RECEIVER_TARGET.
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

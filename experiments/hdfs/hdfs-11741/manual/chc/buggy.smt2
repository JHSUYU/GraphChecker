; HDFS-11741, buggy KeyManager, success-only coordination.
;
; This is a property-directed observer abstraction of the seven VM regions.
; Fix one distinguished key q: the key used by the failing request.  For each
; allKeys container, hasQ says whether allKeys.get(q) is non-null and expQ is
; that entry's expiry.  This is not a whole-map equality.  It is the exact
; pointwise semantics of the source operations relevant to the target:
;
;   removeExpiredKeys: hasQ' = hasQ && expQ >= now
;   exportKeys:        copy hasQ and expQ
;   addKeys:           removeExpiredKeys, then overwrite q iff the exported
;                      fixed array contains q
;
; Key IDs are unique and these regions do not rename a key, so this projection
; is closed for allKeys.get(requestKey)==null.  q is initialized as the first
; NameNode current key, which is precisely the stale-key HDFS-11741 scenario.
;
; Inv is the outer while-loop invariant.  Its rules allow arbitrary ordering
; of the seven atomic region steps.  The TICK guard states the success-only
; timing contract: a successful periodic Balancer refresh occurs before a
; stale current key can mint a DEK whose lifetime exceeds q's NN retention.
; A request is delivered without crossing the modeled logical clock
; (reqWall=wall); unbounded transfer delay is outside this success-only model.
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

; State order:
; wall, keyUpdateInterval, tokenLifetime,
; rotated, nn(has,expiry,currentIsQ),
; rpc(valid,has,expiry,currentIsQ),
; balancer(has,expiry,currentIsQ),
; heartbeat(valid,has,expiry,currentIsQ),
; datanode(has,expiry,currentIsQ),
; cachedDEK(valid,isQ,expiry), request(valid,isQ,sentWall),
; seenBalancerDeliveryFailure.
(declare-rel Inv
  (Int Int Int
   Bool Bool Int Bool
   Bool Bool Int Bool
   Bool Int Bool
   Bool Bool Int Bool
   Bool Int Bool
   Bool Bool Int
   Bool Bool Int
   Bool))
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

; Real initialization projected to q.  The initial current BlockKey expires at
; 2*keyInterval+lifetime at all three roles; no DEK/request exists yet.
(rule
  (=> (and (> keyInterval 0) (> lifetime 0))
      (Inv 0 keyInterval lifetime
           false true (+ (* 2 keyInterval) lifetime) true
           false false 0 false
           true (+ (* 2 keyInterval) lifetime) true
           false false 0 false
           true (+ (* 2 keyInterval) lifetime) true
           false false 0
           false false 0
           false)))

; Environment clock.  The guard is the explicit successful-refresh invariant
; discussed above; region transitions themselves may freely interleave at one
; wall-clock instant.
(rule
  (=> (and
        (Inv wall keyInterval lifetime
             rotated nnHas nnExpiry nnCurrentQ
             rpcValid rpcHas rpcExpiry rpcCurrentQ
             balancerHas balancerExpiry balancerCurrentQ
             heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
             datanodeHas datanodeExpiry datanodeCurrentQ
             cacheValid cacheQ cacheExpiry
             requestValid requestQ requestWall seenFailure)
        (> delta 0)
        (or (not rotated)
            (not balancerCurrentQ)
            (<= (+ (+ wall delta) lifetime) nnExpiry)))
      (Inv (+ wall delta) keyInterval lifetime
           rotated nnHas nnExpiry nnCurrentQ
           rpcValid rpcHas rpcExpiry rpcCurrentQ
           balancerHas balancerExpiry balancerCurrentQ
           heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
           datanodeHas datanodeExpiry datanodeCurrentQ
           cacheValid cacheQ cacheExpiry
           requestValid requestQ requestWall seenFailure)))

; REGION 1: NN_UPDATE, first rotation.  updateKeys() retires q with
; now+keyInterval+lifetime and advances currentKey to a distinct key.
(rule
  (=> (and
        (Inv wall keyInterval lifetime
             rotated nnHas nnExpiry nnCurrentQ
             rpcValid rpcHas rpcExpiry rpcCurrentQ
             balancerHas balancerExpiry balancerCurrentQ
             heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
             datanodeHas datanodeExpiry datanodeCurrentQ
             cacheValid cacheQ cacheExpiry
             requestValid requestQ requestWall seenFailure)
        (not rotated))
      (Inv wall keyInterval lifetime
           true true (+ wall keyInterval lifetime) false
           rpcValid rpcHas rpcExpiry rpcCurrentQ
           balancerHas balancerExpiry balancerCurrentQ
           heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
           datanodeHas datanodeExpiry datanodeCurrentQ
           cacheValid cacheQ cacheExpiry
           requestValid requestQ requestWall seenFailure)))

; REGION 1: later NN_UPDATE iterations.  q is no longer current/next, hence
; the only q effect is removeExpiredKeys' strict expiry comparison.
(rule
  (=> (and
        (Inv wall keyInterval lifetime
             rotated nnHas nnExpiry nnCurrentQ
             rpcValid rpcHas rpcExpiry rpcCurrentQ
             balancerHas balancerExpiry balancerCurrentQ
             heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
             datanodeHas datanodeExpiry datanodeCurrentQ
             cacheValid cacheQ cacheExpiry
             requestValid requestQ requestWall seenFailure)
        rotated)
      (Inv wall keyInterval lifetime
           rotated (liveQ nnHas nnExpiry wall) nnExpiry false
           rpcValid rpcHas rpcExpiry rpcCurrentQ
           balancerHas balancerExpiry balancerCurrentQ
           heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
           datanodeHas datanodeExpiry datanodeCurrentQ
           cacheValid cacheQ cacheExpiry
           requestValid requestQ requestWall seenFailure)))

; REGION 2: NN_RPC_EXPORT.  exportKeys() snapshots currentKey and allKeys.
(rule
  (=>
    (Inv wall keyInterval lifetime
         rotated nnHas nnExpiry nnCurrentQ
         rpcValid rpcHas rpcExpiry rpcCurrentQ
         balancerHas balancerExpiry balancerCurrentQ
         heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
         datanodeHas datanodeExpiry datanodeCurrentQ
         cacheValid cacheQ cacheExpiry
         requestValid requestQ requestWall seenFailure)
    (Inv wall keyInterval lifetime
         rotated nnHas nnExpiry nnCurrentQ
         true nnHas nnExpiry nnCurrentQ
         balancerHas balancerExpiry balancerCurrentQ
         heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
         datanodeHas datanodeExpiry datanodeCurrentQ
         cacheValid cacheQ cacheExpiry
         requestValid requestQ requestWall seenFailure)))

; REGION 3: BALANCER_REFRESH.  Real addKeys removes expired local entries,
; writes exported currentKey, then overlays every non-null exported array slot.
(rule
  (=> (and
        (Inv wall keyInterval lifetime
             rotated nnHas nnExpiry nnCurrentQ
             rpcValid rpcHas rpcExpiry rpcCurrentQ
             balancerHas balancerExpiry balancerCurrentQ
             heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
             datanodeHas datanodeExpiry datanodeCurrentQ
             cacheValid cacheQ cacheExpiry
             requestValid requestQ requestWall seenFailure)
        rpcValid)
      (Inv wall keyInterval lifetime
           rotated nnHas nnExpiry nnCurrentQ
           false rpcHas rpcExpiry rpcCurrentQ
           (overlayHasQ balancerHas balancerExpiry rpcHas wall)
           (overlayExpiryQ balancerExpiry rpcHas rpcExpiry)
           rpcCurrentQ
           heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
           datanodeHas datanodeExpiry datanodeCurrentQ
           cacheValid cacheQ cacheExpiry
           requestValid requestQ requestWall false)))

; REGION 4: NN_HEARTBEAT_EXPORT.  Same exportKeys transformer, distinct
; asynchronous channel state.
(rule
  (=>
    (Inv wall keyInterval lifetime
         rotated nnHas nnExpiry nnCurrentQ
         rpcValid rpcHas rpcExpiry rpcCurrentQ
         balancerHas balancerExpiry balancerCurrentQ
         heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
         datanodeHas datanodeExpiry datanodeCurrentQ
         cacheValid cacheQ cacheExpiry
         requestValid requestQ requestWall seenFailure)
    (Inv wall keyInterval lifetime
         rotated nnHas nnExpiry nnCurrentQ
         rpcValid rpcHas rpcExpiry rpcCurrentQ
         balancerHas balancerExpiry balancerCurrentQ
         true nnHas nnExpiry nnCurrentQ
         datanodeHas datanodeExpiry datanodeCurrentQ
         cacheValid cacheQ cacheExpiry
         requestValid requestQ requestWall seenFailure)))

; REGION 5: DN_REFRESH, the pointwise transformer of the real worker addKeys.
(rule
  (=> (and
        (Inv wall keyInterval lifetime
             rotated nnHas nnExpiry nnCurrentQ
             rpcValid rpcHas rpcExpiry rpcCurrentQ
             balancerHas balancerExpiry balancerCurrentQ
             heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
             datanodeHas datanodeExpiry datanodeCurrentQ
             cacheValid cacheQ cacheExpiry
             requestValid requestQ requestWall seenFailure)
        heartbeatValid)
      (Inv wall keyInterval lifetime
           rotated nnHas nnExpiry nnCurrentQ
           rpcValid rpcHas rpcExpiry rpcCurrentQ
           balancerHas balancerExpiry balancerCurrentQ
           false heartbeatHas heartbeatExpiry heartbeatCurrentQ
           (overlayHasQ datanodeHas datanodeExpiry heartbeatHas wall)
           (overlayExpiryQ datanodeExpiry heartbeatHas heartbeatExpiry)
           heartbeatCurrentQ
           cacheValid cacheQ cacheExpiry
           requestValid requestQ requestWall seenFailure)))

; REGION 6: DISPATCHER_SENDER, buggy source.  A null cache generates from the
; Balancer currentKey.  Every later call reuses the immutable cached DEK even
; when cacheExpiry < wall.
(rule
  (=> (and
        (Inv wall keyInterval lifetime
             rotated nnHas nnExpiry nnCurrentQ
             rpcValid rpcHas rpcExpiry rpcCurrentQ
             balancerHas balancerExpiry balancerCurrentQ
             heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
             datanodeHas datanodeExpiry datanodeCurrentQ
             cacheValid cacheQ cacheExpiry
             requestValid requestQ requestWall seenFailure)
        (not cacheValid))
      (Inv wall keyInterval lifetime
           rotated nnHas nnExpiry nnCurrentQ
           rpcValid rpcHas rpcExpiry rpcCurrentQ
           balancerHas balancerExpiry balancerCurrentQ
           heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
           datanodeHas datanodeExpiry datanodeCurrentQ
           true balancerCurrentQ (+ wall lifetime)
           true balancerCurrentQ wall seenFailure)))

(rule
  (=> (and
        (Inv wall keyInterval lifetime
             rotated nnHas nnExpiry nnCurrentQ
             rpcValid rpcHas rpcExpiry rpcCurrentQ
             balancerHas balancerExpiry balancerCurrentQ
             heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
             datanodeHas datanodeExpiry datanodeCurrentQ
             cacheValid cacheQ cacheExpiry
             requestValid requestQ requestWall seenFailure)
        cacheValid)
      (Inv wall keyInterval lifetime
           rotated nnHas nnExpiry nnCurrentQ
           rpcValid rpcHas rpcExpiry rpcCurrentQ
           balancerHas balancerExpiry balancerCurrentQ
           heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
           datanodeHas datanodeExpiry datanodeCurrentQ
           cacheValid cacheQ cacheExpiry
           true cacheQ wall seenFailure)))

; REGION 7: SASL_RECEIVER_TARGET.  The normal branch consumes a same-clock
; request; the exceptional branch is exactly allKeys.get(requestKey)==null.
(rule
  (=> (and
        (Inv wall keyInterval lifetime
             rotated nnHas nnExpiry nnCurrentQ
             rpcValid rpcHas rpcExpiry rpcCurrentQ
             balancerHas balancerExpiry balancerCurrentQ
             heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
             datanodeHas datanodeExpiry datanodeCurrentQ
             cacheValid cacheQ cacheExpiry
             requestValid requestQ requestWall seenFailure)
        requestValid (= requestWall wall)
        (or (not requestQ) datanodeHas))
      (Inv wall keyInterval lifetime
           rotated nnHas nnExpiry nnCurrentQ
           rpcValid rpcHas rpcExpiry rpcCurrentQ
           balancerHas balancerExpiry balancerCurrentQ
           heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
           datanodeHas datanodeExpiry datanodeCurrentQ
           cacheValid cacheQ cacheExpiry
           false requestQ requestWall seenFailure)))

(rule
  (=> (and
        (Inv wall keyInterval lifetime
             rotated nnHas nnExpiry nnCurrentQ
             rpcValid rpcHas rpcExpiry rpcCurrentQ
             balancerHas balancerExpiry balancerCurrentQ
             heartbeatValid heartbeatHas heartbeatExpiry heartbeatCurrentQ
             datanodeHas datanodeExpiry datanodeCurrentQ
             cacheValid cacheQ cacheExpiry
             requestValid requestQ requestWall seenFailure)
        requestValid (= requestWall wall) requestQ (not datanodeHas))
      Bad))

(query Bad)

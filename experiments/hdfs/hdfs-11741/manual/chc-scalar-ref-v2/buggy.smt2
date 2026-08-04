; HDFS-11741 before the KeyManager expiry fix.
;
; q is the distinguished key used by the target request.  Every qRef below is
; a real nullable reference denoting allKeys.get(q) or its serialized copy;
; 0 is Java null.  A qExpiry scalar is meaningful exactly when its qRef is
; non-null.  KeyManager.encryptionKey is carried as a real nullable reference
; with its immutable fields; requestRef is the pending serialized request token.
;
; Inv is recursively closed under every region, so NN/Balancer/DN loop
; activations are unbounded.  The clock has no property-directed guard.

(set-logic HORN)
(set-option :fp.engine spacer)

(define-sort Ref () Int)
(define-fun nullRef () Ref 0)

; Inv parameter order:
; wall, elapsed, K, T, q;
; NN current/next/serial/qRef/qExpiry;
; RPC message/current/qRef/qExpiry; Balancer current/qRef/qExpiry;
; heartbeat message/current/qRef/qExpiry; DN current/qRef/qExpiry;
; nextObjectRef; encryptionKey ref/id/expiry; request ref/keyId.
(declare-rel Inv
  (Int Int Int Int Int
   Int Int Int Ref Int
   Ref Int Ref Int Int Ref Int
   Ref Int Ref Int Int Ref Int
   Ref Ref Int Int Ref Int))
(declare-rel Bad ())

(declare-var wall Int)
(declare-var elapsed Int)
(declare-var keyInterval Int)
(declare-var lifetime Int)
(declare-var q Int)
(declare-var nnCurrent Int)
(declare-var nnNext Int)
(declare-var nnSerial Int)
(declare-var nnQRef Ref)
(declare-var nnQExpiry Int)
(declare-var rpcMsgRef Ref)
(declare-var rpcCurrent Int)
(declare-var rpcQRef Ref)
(declare-var rpcQExpiry Int)
(declare-var balancerCurrent Int)
(declare-var balQRef Ref)
(declare-var balQExpiry Int)
(declare-var hbMsgRef Ref)
(declare-var hbCurrent Int)
(declare-var hbQRef Ref)
(declare-var hbQExpiry Int)
(declare-var dnCurrent Int)
(declare-var dnQRef Ref)
(declare-var dnQExpiry Int)
(declare-var nextObjectRef Ref)
(declare-var encryptionKeyRef Ref)
(declare-var encryptionKeyId Int)
(declare-var encryptionKeyExpiry Int)
(declare-var requestRef Ref)
(declare-var requestKey Int)
(declare-var delta Int)

; Initial current key q=17 is present at NN, Balancer and DN.  Their nullable
; lookup references are distinct JVM objects with equal keyId/expiry fields.
(rule
  (=> (and (> keyInterval 0) (> lifetime 0))
      (Inv 0 0 keyInterval lifetime 17
           17 18 18 1 (+ (* 2 keyInterval) lifetime)
           nullRef 0 nullRef 0
           17 2 (+ (* 2 keyInterval) lifetime)
           nullRef 0 nullRef 0 17 3
           (+ (* 2 keyInterval) lifetime)
           4
           nullRef 0 0
           nullRef 0)))

; Ordinary environment time.  elapsed is the monotonic duration passed to
; updateKeys(long); wall is the Timer.now()/Time.now() domain.
(rule
  (=> (and
        (Inv wall elapsed keyInterval lifetime q
             nnCurrent nnNext nnSerial nnQRef nnQExpiry
             rpcMsgRef rpcCurrent rpcQRef rpcQExpiry
             balancerCurrent balQRef balQExpiry
             hbMsgRef hbCurrent hbQRef hbQExpiry
             dnCurrent dnQRef dnQExpiry
             nextObjectRef
             encryptionKeyRef encryptionKeyId encryptionKeyExpiry
             requestRef requestKey)
        (> delta 0))
      (Inv (+ wall delta) (+ elapsed delta) keyInterval lifetime q
           nnCurrent nnNext nnSerial nnQRef nnQExpiry
           rpcMsgRef rpcCurrent rpcQRef rpcQExpiry
           balancerCurrent balQRef balQExpiry
           hbMsgRef hbCurrent hbQRef hbQExpiry
           dnCurrent dnQRef dnQExpiry
           nextObjectRef
           encryptionKeyRef encryptionKeyId encryptionKeyExpiry
           requestRef requestKey)))

; NN_UPDATE true branch.  The <= branch is an identity activation.
;
; Exact VM/source order for the q coordinate:
;   removeExpiredKeys;
;   allKeys.put(old current, retiring BlockKey);
;   allKeys.put(old next, promoted BlockKey);
;   allKeys.put(new serial, new next BlockKey).
; The nested ITE preserves last-write-wins even across an int-key collision.
(rule
  (=> (and
        (Inv wall elapsed keyInterval lifetime q
             nnCurrent nnNext nnSerial nnQRef nnQExpiry
             rpcMsgRef rpcCurrent rpcQRef rpcQExpiry
             balancerCurrent balQRef balQExpiry
             hbMsgRef hbCurrent hbQRef hbQExpiry
             dnCurrent dnQRef dnQExpiry
             nextObjectRef
             encryptionKeyRef encryptionKeyId encryptionKeyExpiry
             requestRef requestKey)
        (> elapsed keyInterval))
      (let ((serial1 (+ nnSerial 1))
            (retiringRef nextObjectRef)
            (promotedRef (+ nextObjectRef 1))
            (newNextRef (+ nextObjectRef 2))
            (cleanedQ
              (ite (and (not (= nnQRef nullRef))
                        (< nnQExpiry wall))
                   nullRef nnQRef)))
        (Inv wall 0 keyInterval lifetime q
             nnNext serial1 serial1
             (ite (= q serial1) newNextRef
               (ite (= q nnNext) promotedRef
                 (ite (= q nnCurrent) retiringRef cleanedQ)))
             (ite (= q serial1) (+ wall (* 3 keyInterval) lifetime)
               (ite (= q nnNext) (+ wall (* 2 keyInterval) lifetime)
                 (ite (= q nnCurrent) (+ wall keyInterval lifetime)
                      nnQExpiry)))
             rpcMsgRef rpcCurrent rpcQRef rpcQExpiry
             balancerCurrent balQRef balQExpiry
             hbMsgRef hbCurrent hbQRef hbQExpiry
             dnCurrent dnQRef dnQExpiry
             (+ nextObjectRef 3)
             encryptionKeyRef encryptionKeyId encryptionKeyExpiry
             requestRef requestKey))))

; NN_RPC_EXPORT: a read-only, independently serialized snapshot.  rpcMsgRef
; distinguishes no message from a valid message whose q lookup is null.
(rule
  (=> (and
    (Inv wall elapsed keyInterval lifetime q
         nnCurrent nnNext nnSerial nnQRef nnQExpiry
         rpcMsgRef rpcCurrent rpcQRef rpcQExpiry
         balancerCurrent balQRef balQExpiry
         hbMsgRef hbCurrent hbQRef hbQExpiry
         dnCurrent dnQRef dnQExpiry
         nextObjectRef
         encryptionKeyRef encryptionKeyId encryptionKeyExpiry
         requestRef requestKey)
    (= rpcMsgRef nullRef))
    (Inv wall elapsed keyInterval lifetime q
         nnCurrent nnNext nnSerial nnQRef nnQExpiry
         nextObjectRef nnCurrent
         (ite (= nnQRef nullRef) nullRef (+ nextObjectRef 1))
         nnQExpiry
         balancerCurrent balQRef balQExpiry
         hbMsgRef hbCurrent hbQRef hbQExpiry
         dnCurrent dnQRef dnQExpiry
         (ite (= nnQRef nullRef)
              (+ nextObjectRef 1) (+ nextObjectRef 2))
         encryptionKeyRef encryptionKeyId encryptionKeyExpiry
         requestRef requestKey)))

; BALANCER_REFRESH success.  Exact pointwise addKeys order is local cleanup,
; currentKey write, then incoming-array PUTs.
(rule
  (=> (and
        (Inv wall elapsed keyInterval lifetime q
             nnCurrent nnNext nnSerial nnQRef nnQExpiry
             rpcMsgRef rpcCurrent rpcQRef rpcQExpiry
             balancerCurrent balQRef balQExpiry
             hbMsgRef hbCurrent hbQRef hbQExpiry
             dnCurrent dnQRef dnQExpiry
             nextObjectRef
             encryptionKeyRef encryptionKeyId encryptionKeyExpiry
             requestRef requestKey)
        (not (= rpcMsgRef nullRef)))
      (Inv wall elapsed keyInterval lifetime q
           nnCurrent nnNext nnSerial nnQRef nnQExpiry
           nullRef rpcCurrent rpcQRef rpcQExpiry
           rpcCurrent
           (ite (= rpcQRef nullRef)
                (ite (and (not (= balQRef nullRef))
                          (< balQExpiry wall))
                     nullRef balQRef)
                rpcQRef)
           (ite (= rpcQRef nullRef) balQExpiry rpcQExpiry)
           hbMsgRef hbCurrent hbQRef hbQExpiry
           dnCurrent dnQRef dnQExpiry
           nextObjectRef
           encryptionKeyRef encryptionKeyId encryptionKeyExpiry
           requestRef requestKey)))

; NN_HEARTBEAT_EXPORT is a second independent snapshot channel.  Its enabling
; flag is outside this property slice; repeated exports remain unbounded.
(rule
  (=> (and
        (Inv wall elapsed keyInterval lifetime q
             nnCurrent nnNext nnSerial nnQRef nnQExpiry
             rpcMsgRef rpcCurrent rpcQRef rpcQExpiry
             balancerCurrent balQRef balQExpiry
             hbMsgRef hbCurrent hbQRef hbQExpiry
             dnCurrent dnQRef dnQExpiry
             nextObjectRef
             encryptionKeyRef encryptionKeyId encryptionKeyExpiry
             requestRef requestKey)
        (= hbMsgRef nullRef))
      (Inv wall elapsed keyInterval lifetime q
           nnCurrent nnNext nnSerial nnQRef nnQExpiry
           rpcMsgRef rpcCurrent rpcQRef rpcQExpiry
           balancerCurrent balQRef balQExpiry
           nextObjectRef nnCurrent
           (ite (= nnQRef nullRef) nullRef (+ nextObjectRef 1))
           nnQExpiry
           dnCurrent dnQRef dnQExpiry
           (ite (= nnQRef nullRef)
                (+ nextObjectRef 1) (+ nextObjectRef 2))
           encryptionKeyRef encryptionKeyId encryptionKeyExpiry
           requestRef requestKey)))

; DN_REFRESH exact pointwise addKeys transformer.  It first removes a local q
; iff expiry < wall, then every incoming-array PUT runs.  Thus an incoming q
; reference overwrites the cleaned result even if its own expiry is old.
(rule
  (=> (and
        (Inv wall elapsed keyInterval lifetime q
             nnCurrent nnNext nnSerial nnQRef nnQExpiry
             rpcMsgRef rpcCurrent rpcQRef rpcQExpiry
             balancerCurrent balQRef balQExpiry
             hbMsgRef hbCurrent hbQRef hbQExpiry
             dnCurrent dnQRef dnQExpiry
             nextObjectRef
             encryptionKeyRef encryptionKeyId encryptionKeyExpiry
             requestRef requestKey)
        (not (= hbMsgRef nullRef)))
      (Inv wall elapsed keyInterval lifetime q
           nnCurrent nnNext nnSerial nnQRef nnQExpiry
           rpcMsgRef rpcCurrent rpcQRef rpcQExpiry
           balancerCurrent balQRef balQExpiry
           nullRef hbCurrent hbQRef hbQExpiry
           hbCurrent
           (ite (= hbQRef nullRef)
                (ite (and (not (= dnQRef nullRef))
                          (< dnQExpiry wall))
                     nullRef dnQRef)
                hbQRef)
           (ite (= hbQRef nullRef) dnQExpiry hbQExpiry)
           nextObjectRef
           encryptionKeyRef encryptionKeyId encryptionKeyExpiry
           requestRef requestKey)))

; DISPATCHER_SENDER, encrypted workload, null reference path.  The fresh DEK
; captures the synchronized Balancer currentKey read and wall+tokenLifetime.
(rule
  (=> (and
        (Inv wall elapsed keyInterval lifetime q
             nnCurrent nnNext nnSerial nnQRef nnQExpiry
             rpcMsgRef rpcCurrent rpcQRef rpcQExpiry
             balancerCurrent balQRef balQExpiry
             hbMsgRef hbCurrent hbQRef hbQExpiry
             dnCurrent dnQRef dnQExpiry
             nextObjectRef
             encryptionKeyRef encryptionKeyId encryptionKeyExpiry
             requestRef requestKey)
        (= encryptionKeyRef nullRef))
      (Inv wall elapsed keyInterval lifetime q
           nnCurrent nnNext nnSerial nnQRef nnQExpiry
           rpcMsgRef rpcCurrent rpcQRef rpcQExpiry
           balancerCurrent balQRef balQExpiry
           hbMsgRef hbCurrent hbQRef hbQExpiry
           dnCurrent dnQRef dnQExpiry
           (+ nextObjectRef 2)
           nextObjectRef balancerCurrent (+ wall lifetime)
           (+ nextObjectRef 1) balancerCurrent)))

; Buggy non-null path: no expiry field is read.  The immutable DEK reference is
; returned indefinitely, regardless of encryptionKeyExpiry < wall.
(rule
  (=> (and
        (Inv wall elapsed keyInterval lifetime q
             nnCurrent nnNext nnSerial nnQRef nnQExpiry
             rpcMsgRef rpcCurrent rpcQRef rpcQExpiry
             balancerCurrent balQRef balQExpiry
             hbMsgRef hbCurrent hbQRef hbQExpiry
             dnCurrent dnQRef dnQExpiry
             nextObjectRef
             encryptionKeyRef encryptionKeyId encryptionKeyExpiry
             requestRef requestKey)
        (not (= encryptionKeyRef nullRef)))
      (Inv wall elapsed keyInterval lifetime q
           nnCurrent nnNext nnSerial nnQRef nnQExpiry
           rpcMsgRef rpcCurrent rpcQRef rpcQExpiry
           balancerCurrent balQRef balQExpiry
           hbMsgRef hbCurrent hbQRef hbQExpiry
           dnCurrent dnQRef dnQExpiry
           (+ nextObjectRef 1)
           encryptionKeyRef encryptionKeyId encryptionKeyExpiry
           nextObjectRef encryptionKeyId)))

; Normal SASL lookup consumes the request.  Non-q requests are outside this
; one-coordinate slice; q succeeds exactly when dnQRef is non-null.
(rule
  (=> (and
        (Inv wall elapsed keyInterval lifetime q
             nnCurrent nnNext nnSerial nnQRef nnQExpiry
             rpcMsgRef rpcCurrent rpcQRef rpcQExpiry
             balancerCurrent balQRef balQExpiry
             hbMsgRef hbCurrent hbQRef hbQExpiry
             dnCurrent dnQRef dnQExpiry
             nextObjectRef
             encryptionKeyRef encryptionKeyId encryptionKeyExpiry
             requestRef requestKey)
        (not (= requestRef nullRef))
        (or (not (= requestKey q))
            (not (= dnQRef nullRef))))
      (Inv wall elapsed keyInterval lifetime q
           nnCurrent nnNext nnSerial nnQRef nnQExpiry
           rpcMsgRef rpcCurrent rpcQRef rpcQExpiry
           balancerCurrent balQRef balQExpiry
           hbMsgRef hbCurrent hbQRef hbQExpiry
           dnCurrent dnQRef dnQExpiry
           nextObjectRef
           encryptionKeyRef encryptionKeyId encryptionKeyExpiry
           nullRef requestKey)))

; Annotated target: allKeys.get(requestKey) == null.
(rule
  (=> (and
        (Inv wall elapsed keyInterval lifetime q
             nnCurrent nnNext nnSerial nnQRef nnQExpiry
             rpcMsgRef rpcCurrent rpcQRef rpcQExpiry
             balancerCurrent balQRef balQExpiry
             hbMsgRef hbCurrent hbQRef hbQExpiry
             dnCurrent dnQRef dnQExpiry
             nextObjectRef
             encryptionKeyRef encryptionKeyId encryptionKeyExpiry
             requestRef requestKey)
        (not (= requestRef nullRef))
        (= requestKey q)
        (= dnQRef nullRef))
      Bad))

(query Bad)

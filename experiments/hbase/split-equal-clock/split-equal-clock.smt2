; Manual GraphChecker-style composition for the split equal-clock exception.
; Inputs: parent RegionInfo in master RegionStates, and master's currentTime.
; HBase 4.x SplitTableRegionProcedure.java:138-146,264-273;
; ModifyRegionUtils.java:94-110.
(set-logic ALL)

(declare-const parentRid Int)
(declare-const now Int)
(declare-const parentTable Int)
(declare-const parentStartKey Int)
(declare-const daughterRid Int)
(declare-const daughterTable Int)
(declare-const daughterStartKey Int)

; Path arms: exactly one branch of getDaughterRegionIdTimestamp.
(declare-const clockBehind Bool)
(declare-const clockEqual Bool)
(declare-const clockAhead Bool)
(assert (or clockBehind clockEqual clockAhead))
(assert (not (and clockBehind clockEqual)))
(assert (not (and clockBehind clockAhead)))
(assert (not (and clockEqual clockAhead)))
(assert (= clockBehind (< now parentRid)))
(assert (= clockEqual (= now parentRid)))
(assert (= clockAhead (> now parentRid)))
(assert (= daughterRid (ite clockBehind (+ parentRid 1) now)))
(assert (<= 0 parentRid))
(assert (<= 0 now))

; WIRE/constructor join: the first daughter copies parent table and start key.
(assert (= daughterTable parentTable))
(assert (= daughterStartKey parentStartKey))

; Region-name identity is (table,startKey,regionId). The production encoded
; name is an MD5 digest of this name. For the control, assume no MD5 collision
; between these two distinct names; equality always implies equal digest.
(declare-datatypes () ((RegionIdentity
  (mkRegion (regionTable Int) (regionStartKey Int) (regionId Int)))))
(define-fun parentIdentity () RegionIdentity
  (mkRegion parentTable parentStartKey parentRid))
(define-fun daughterIdentity () RegionIdentity
  (mkRegion daughterTable daughterStartKey daughterRid))
(declare-fun encodedName (RegionIdentity) Int)
(define-fun parentEncoded () Int (encodedName parentIdentity))
(define-fun daughterEncoded () Int (encodedName daughterIdentity))
(assert (=> (distinct parentIdentity daughterIdentity)
            (distinct parentEncoded daughterEncoded)))

; STATE join: the split parent still has a RegionStateNode. The second
; daughter is distinct because its start key is the split point.
(declare-const parentInRegionStates Bool)
(declare-const splitPoint Int)
(assert parentInRegionStates)
(assert (distinct splitPoint parentStartKey))
(define-fun duplicateCandidate () Bool false)
(define-fun existingEncodedName () Bool
  (and parentInRegionStates (= daughterEncoded parentEncoded)))
(define-fun collisionGuard () Bool
  (or duplicateCandidate existingEncodedName))

; Targeted exception path: equal clock lets daughter reuse the parent's name.
(push 1)
(assert clockEqual)
(assert collisionGuard)
(check-sat)
(get-value (parentRid now daughterRid parentIdentity daughterIdentity collisionGuard))
(pop 1)

; Timely clock control: with a later ID, this specific parent-name collision
; cannot trigger. It says nothing about a separate accidental MD5 collision.
(push 1)
(assert clockAhead)
(assert collisionGuard)
(check-sat)
(pop 1)

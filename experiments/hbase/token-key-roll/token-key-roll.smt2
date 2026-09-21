; HBase authentication-token key-roll coordination, in the style of
; GraphChecker's path/arm/state/wire composition.  This is a hand-built,
; bounded model of TestAuthenticationTokenKeyRollCoordination, not output
; from GraphChecker's Java 8 recorder.
;
; Run: z3 -smt2 token-key-roll.smt2
; Expected: sat, a value list, unsat.  The first answer is the delayed
; notification path.  The second is the timely notification control.
(set-logic QF_LIA)
(set-option :produce-models true)

; The clock values are relative to a successful leader roll.  The test
; uses the same 100 ms issue delay and 1000 ms token lifetime.
(declare-const roll_time Int)
(declare-const issue_time Int)
(declare-const verify_time Int)
(declare-const lifetime Int)
(assert (>= roll_time 0))
(assert (= lifetime 1000))
(assert (= issue_time (+ roll_time 100)))
(assert (= verify_time (+ roll_time lifetime 1)))
(define-fun old_key_expiry () Int (+ roll_time lifetime))
(define-fun token_expiry () Int (+ issue_time lifetime))
(assert (< roll_time issue_time))
(assert (< issue_time verify_time))

; K0 is already present at both managers.  The leader rolls K1.  K0's
; expiry is based on the roll, while a token's expiry is based on issue.
(declare-const old_key_id Int)
(declare-const new_key_id Int)
(assert (= old_key_id 11))
(assert (= new_key_id (+ old_key_id 1)))

; The STATE family of the issuer's currentKey has two attested arms.  A
; delayed ZK notification selects K0 at issue; an early one selects K1.
; Delivery eventually happens in both scenarios, as in the test.
(declare-const notification_before_issue Bool)
(declare-const notification_before_verify Bool)
(declare-const arm_old Bool)
(declare-const arm_new Bool)
(declare-const issuer_current_key_at_issue Int)
(assert notification_before_verify)
(assert (=> notification_before_issue notification_before_verify))
(assert (or arm_old arm_new))
(assert (not (and arm_old arm_new)))
(assert (=> arm_old
  (and (not notification_before_issue)
       (= issuer_current_key_at_issue old_key_id))))
(assert (=> arm_new
  (and notification_before_issue
       (= issuer_current_key_at_issue new_key_id))))

; The token captures the issuer's key id.  The request carries that id
; to the verifier; the two equalities are a WIRE handoff, not an assumed
; equality between the servers' currentKey fields.
(declare-const token_key_at_issuer Int)
(declare-const token_key_at_verifier Int)
(assert (= token_key_at_issuer issuer_current_key_at_issue))
(assert (= token_key_at_verifier token_key_at_issuer))

; The leader's cleanup is a STATE transition over allKeys, followed by
; a successful ZK deletion.  A refresh after the lookup miss can recover
; only a key still present in ZK.  K1 remains in the leader's map.
(declare-const cleanup_ran Bool)
(declare-const zk_delete_succeeded Bool)
(declare-const old_in_leader_after_cleanup Bool)
(declare-const old_in_zk_after_cleanup Bool)
(declare-const new_in_leader_after_cleanup Bool)
(declare-const found_after_refresh Bool)
(assert cleanup_ran)
(assert zk_delete_succeeded)
(assert (= old_in_leader_after_cleanup
  (not (and cleanup_ran (< old_key_expiry verify_time)))))
(assert (= old_in_zk_after_cleanup
  (not (and cleanup_ran zk_delete_succeeded
            (< old_key_expiry verify_time)))))
(assert new_in_leader_after_cleanup)
(assert (= found_after_refresh
  (or (and (= token_key_at_verifier old_key_id)
           (or old_in_leader_after_cleanup old_in_zk_after_cleanup))
      (and (= token_key_at_verifier new_key_id)
           new_in_leader_after_cleanup))))

; retrievePassword first takes the non-expired arm, then refreshes on
; a miss and throws InvalidToken("Unknown master key...") if still null.
(declare-const zk_aborted Bool)
(declare-const fatal_unknown_master_key Bool)
(assert (not zk_aborted))
(assert (= fatal_unknown_master_key
  (and (<= verify_time token_expiry)
       (not zk_aborted)
       (not found_after_refresh))))
(assert fatal_unknown_master_key)

; Counterfactual 1: issuer has not seen K1 at issue, but sees it later.
; K0 expires at roll+1000, whereas the token expires at roll+1100.
; Verification at roll+1001 lies in the 99 ms failure window.
(push 1)
(assert (not notification_before_issue))
(check-sat)
(get-value (roll_time issue_time verify_time old_key_expiry token_expiry
            arm_old arm_new token_key_at_verifier
            old_in_leader_after_cleanup old_in_zk_after_cleanup
            found_after_refresh fatal_unknown_master_key))
(pop 1)

; Counterfactual 2: the notification arrives before issue.  The issuer
; signs with K1, which the leader retains, so the same fatal guard is UNSAT.
(push 1)
(assert notification_before_issue)
(check-sat)
(pop 1)

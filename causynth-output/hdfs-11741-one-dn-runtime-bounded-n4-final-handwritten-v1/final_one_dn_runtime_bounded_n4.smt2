; HANDWRITTEN_FINAL_ONE_DN_RUNTIME_BOUNDED_N4
;
; Scope:
;   NN keyId -> Balancer cached DEK -> SASL username token 0 -> target DN keyId
;   NN heartbeat -> target DN removeExpiredKeys() -> four addKeys() puts
;   target DN allKeys.get(keyId) == null
;
; The map cardinality N=4 and P0..P3 are runtime witnesses from
; ACT.PATH.d26d55b957be30a5 / REGION.15.  The expiry decisions and the four
; heartbeat keyIds remain symbolic.  This is a bounded relation, not a proof
; for arbitrary Java Map cardinality.

(set-logic ALL)

(define-fun isJavaInt ((x Int)) Bool
  (and (<= (- 2147483648) x) (<= x 2147483647)))

(define-fun isJavaLong ((x Int)) Bool
  (and (<= (- 9223372036854775808) x)
       (<= x 9223372036854775807)))

; ---------------------------------------------------------------------------
; NN -> Balancer -> DN key relation.
; ---------------------------------------------------------------------------

(declare-const K_NN Int)
(declare-const K_BALANCER Int)
(declare-const K_CACHED_DEK Int)
(declare-const K_PARSED Int)
(declare-const K_DN Int)

(assert (and (isJavaInt K_NN)
             (isJavaInt K_BALANCER)
             (isJavaInt K_CACHED_DEK)
             (isJavaInt K_PARSED)
             (isJavaInt K_DN)))

(assert (! (= K_BALANCER K_NN)
  :named nn_to_balancer_key))
(assert (! (= K_CACHED_DEK K_BALANCER)
  :named balancer_cached_dek_key))

; Certified Java-library round trip:
;
;   Integer.parseInt(
;     (Integer.toString(K_CACHED_DEK) ++ " " ++ POOL ++ " " ++ NONCE)
;       .split(" ")[0])
;   = K_CACHED_DEK
;
; Therefore no handwritten javaParseInt/string approximation is needed in
; the SMT.  The captured concat/split/parseInt AST is summarized directly by
; this equality.
(assert (! (= K_PARSED K_CACHED_DEK)
  :named java_int_string_split_parse_roundtrip))
(assert (! (= K_DN K_PARSED)
  :named sasl_parsed_key_to_dn_lookup_key))

; ---------------------------------------------------------------------------
; Exact runtime-bounded N=4 pre-map snapshot.
; ---------------------------------------------------------------------------

(define-fun P0 () Int 1)
(define-fun P1 () Int 2)
(define-fun P2 () Int (- 1801356227))
(define-fun P3 () Int (- 1801356226))
(assert (distinct P0 P1 P2 P3))

(declare-const E0 Int)
(declare-const E1 Int)
(declare-const E2 Int)
(declare-const E3 Int)
(declare-const NOW Int)
(assert (and (isJavaLong E0)
             (isJavaLong E1)
             (isJavaLong E2)
             (isJavaLong E3)
             (isJavaLong NOW)))

(define-fun EMPTY_KEY_MAP () (Array Int Bool)
  ((as const (Array Int Bool)) false))

(define-fun PRE_MAP () (Array Int Bool)
  (store (store (store (store EMPTY_KEY_MAP P0 true)
                              P1 true)
                       P2 true)
                P3 true))

; removeExpiredKeys(): each entry is removed exactly when expiry < NOW.
(define-fun AFTER_EXPIRY_0 () (Array Int Bool)
  (ite (< E0 NOW) (store PRE_MAP P0 false) PRE_MAP))
(define-fun AFTER_EXPIRY_1 () (Array Int Bool)
  (ite (< E1 NOW)
       (store AFTER_EXPIRY_0 P1 false)
       AFTER_EXPIRY_0))
(define-fun AFTER_EXPIRY_2 () (Array Int Bool)
  (ite (< E2 NOW)
       (store AFTER_EXPIRY_1 P2 false)
       AFTER_EXPIRY_1))
(define-fun AFTER_EXPIRY_3 () (Array Int Bool)
  (ite (< E3 NOW)
       (store AFTER_EXPIRY_2 P3 false)
       AFTER_EXPIRY_2))

; The same NN heartbeat then contributes four symbolic addKeys() keyIds.
(declare-const B0 Int)
(declare-const B1 Int)
(declare-const B2 Int)
(declare-const B3 Int)
(assert (and (isJavaInt B0)
             (isJavaInt B1)
             (isJavaInt B2)
             (isJavaInt B3)))

(define-fun AFTER_PUT_0 () (Array Int Bool)
  (store AFTER_EXPIRY_3 B0 true))
(define-fun AFTER_PUT_1 () (Array Int Bool)
  (store AFTER_PUT_0 B1 true))
(define-fun AFTER_PUT_2 () (Array Int Bool)
  (store AFTER_PUT_1 B2 true))
(define-fun AFTER_PUT_3 () (Array Int Bool)
  (store AFTER_PUT_2 B3 true))

; Exact one-DN state edge: REGION.15.out.122 -> REGION.0.in.117.
(declare-const REGION15_OUT122 (Array Int Bool))
(declare-const REGION0_IN117 (Array Int Bool))
(assert (! (= REGION15_OUT122 AFTER_PUT_3)
  :named region15_output_exact_n4_transformer))
(assert (! (= REGION0_IN117 REGION15_OUT122)
  :named region_edge_883_same_dn_instance))

; Fatal target branch: allKeys.get(K_DN) == null.
(define-fun FATAL () Bool
  (not (select REGION0_IN117 K_DN)))

; Quantifier-free closed form of the complete N=4 transformer.
;
; Every pre-map entry equal to K_DN must expire, and none of the four puts may
; reintroduce K_DN.
(define-fun CLOSED_FORM_FATAL () Bool
  (and (or (not (= P0 K_DN)) (< E0 NOW))
       (or (not (= P1 K_DN)) (< E1 NOW))
       (or (not (= P2 K_DN)) (< E2 NOW))
       (or (not (= P3 K_DN)) (< E3 NOW))
       (not (= B0 K_DN))
       (not (= B1 K_DN))
       (not (= B2 K_DN))
       (not (= B3 K_DN))))

; 1. At least one bug-reaching valuation exists.
(echo "CHECK_1_FATAL_EXPECT_SAT")
(push)
(assert FATAL)
(check-sat)
(pop)
; 2. Array/store semantics and the symbolic closed form are equivalent for
;    every assignment under this N=4 bound.
(echo "CHECK_2_CLOSED_FORM_EQUIVALENCE_EXPECT_UNSAT")
(push)
(assert (not (= FATAL CLOSED_FORM_FATAL)))
(check-sat)
(pop)

; 3. The exact fresh replay branch family (first three survive, P3 expires)
;    contains the expiry-move solution K_DN=P3.
(echo "CHECK_3_FRESH_REPLAY_EXPIRY_MOVE_EXPECT_SAT")
(push)
(assert (>= E0 NOW))
(assert (>= E1 NOW))
(assert (>= E2 NOW))
(assert (< E3 NOW))
(assert (= K_DN P3))
(assert (not (= B0 K_DN)))
(assert (not (= B1 K_DN)))
(assert (not (= B2 K_DN)))
(assert (not (= B3 K_DN)))
(assert FATAL)
(check-sat)
(pop)

; 4. A heartbeat put of K_DN makes the fatal lookup impossible.
(echo "CHECK_4_ANY_REINTRODUCTION_EXPECT_UNSAT")
(push)
(assert FATAL)
(assert (or (= B0 K_DN)
            (= B1 K_DN)
            (= B2 K_DN)
            (= B3 K_DN)))
(check-sat)
(pop)

; 5. A non-expired pre-entry equal to K_DN makes the fatal lookup impossible.
(echo "CHECK_5_ANY_SURVIVING_TARGET_ENTRY_EXPECT_UNSAT")
(push)
(assert FATAL)
(assert (or (and (= P0 K_DN) (>= E0 NOW))
            (and (= P1 K_DN) (>= E1 NOW))
            (and (= P2 K_DN) (>= E2 NOW))
            (and (= P3 K_DN) (>= E3 NOW))))
(check-sat)
(pop)

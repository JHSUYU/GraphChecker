; HDFS-17899 bug 1, in the branch-relation style of HDFS-11741:
; refresh failure -> Balancer retains S0 -> DN lookup is null -> target.
(set-logic QF_LIA)

(declare-const rpcFails Bool)
(declare-const S0 Int)
(declare-const S2 Int)
(declare-const T_capture Int)
(declare-const T_rotate Int)
(declare-const T_refresh Int)
(declare-const T_transfer Int)
(declare-const T_recv Int)
(declare-const T_target Int)

(assert (distinct S0 S2))
(assert (>= T_capture 0))
(assert (< T_capture T_rotate))
(assert (< T_rotate T_refresh))
(assert (< T_refresh T_transfer))
(assert (< T_transfer T_recv))
(assert (< T_recv T_target))

(define-fun branch_refresh_failure () Bool rpcFails)
(define-fun balancerState () Int (ite branch_refresh_failure S0 S2))
(define-fun dnState () Int S2)
(define-fun branch_dn_lookup_is_null () Bool
  (not (= balancerState dnState)))
(define-fun branch_final_target () Bool branch_dn_lookup_is_null)

(assert branch_refresh_failure)
(assert branch_final_target)
(check-sat)
(get-value (rpcFails branch_refresh_failure balancerState dnState
            branch_dn_lookup_is_null branch_final_target
            T_capture T_rotate T_refresh T_transfer T_recv T_target))

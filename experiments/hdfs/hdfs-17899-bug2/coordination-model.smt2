; HDFS-17899 bug 2, in the branch-relation style of HDFS-11741:
; refresh failure -> SPS retains S0 -> DN lookup is null -> target.
(set-logic QF_LIA)

(declare-const rpcFails Bool)
(declare-const S0 Int)
(declare-const S2 Int)
(declare-const T_capture Int)
(declare-const T_rotate Int)
(declare-const T_install_s2 Int)
(declare-const T_refresh Int)
(declare-const T_policy Int)
(declare-const T_move Int)
(declare-const T_recv Int)
(declare-const T_target Int)

(assert (distinct S0 S2))
(assert (>= T_capture 0))
(assert (< T_capture T_rotate))
(assert (< T_rotate T_install_s2))
(assert (< T_install_s2 T_refresh))
(assert (< T_refresh T_policy))
(assert (< T_policy T_move))
(assert (< T_move T_recv))
(assert (< T_recv T_target))

(define-fun branch_refresh_failure () Bool rpcFails)
(define-fun spsState () Int (ite branch_refresh_failure S0 S2))
(define-fun datanodeState () Int S2)
(define-fun branch_dn_lookup_is_null () Bool
  (not (= spsState datanodeState)))
(define-fun branch_final_target () Bool branch_dn_lookup_is_null)

(assert branch_refresh_failure)
(assert branch_final_target)
(check-sat)
(get-value (rpcFails branch_refresh_failure spsState datanodeState
            branch_dn_lookup_is_null branch_final_target
            T_capture T_rotate T_install_s2 T_refresh
            T_policy T_move T_recv T_target))

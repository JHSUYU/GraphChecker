; HDFS-17899 bug 3, in the branch-relation style of HDFS-11741:
; update failure -> source retains S0 -> target lookup is null -> target.
(set-logic QF_LIA)

(declare-const rpcFails Bool)
(declare-const S0 Int)
(declare-const S2 Int)
(declare-const T_capture Int)
(declare-const T_rotate Int)
(declare-const T_target_install_s2 Int)
(declare-const T_update_start Int)
(declare-const T_update_complete Int)
(declare-const T_transfer Int)
(declare-const T_recv Int)
(declare-const T_target Int)

(assert (distinct S0 S2))
(assert (>= T_capture 0))
(assert (< T_capture T_rotate))
(assert (< T_rotate T_target_install_s2))
(assert (< T_target_install_s2 T_update_start))
(assert (< T_update_start T_update_complete))
(assert (< T_update_complete T_transfer))
(assert (< T_transfer T_recv))
(assert (< T_recv T_target))

(define-fun branch_update_failure () Bool rpcFails)
(define-fun sourceState () Int (ite branch_update_failure S0 S2))
(define-fun targetState () Int S2)
(define-fun branch_target_lookup_is_null () Bool
  (not (= sourceState targetState)))
(define-fun branch_final_target () Bool branch_target_lookup_is_null)

(assert branch_update_failure)
(assert branch_final_target)
(check-sat)
(get-value (rpcFails branch_update_failure sourceState targetState
            branch_target_lookup_is_null branch_final_target
            T_capture T_rotate T_target_install_s2
            T_update_start T_update_complete T_transfer T_recv T_target))

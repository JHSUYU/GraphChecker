; HDFS-17897, in the branch-relation style of HDFS-11741:
; one producer branch -> three failed attempts -> final target branch.
(set-logic QF_LIA)

(declare-const rpcFails Bool)
(declare-const T_dn0 Int)
(declare-const T_dn1 Int)
(declare-const T_dn2 Int)
(declare-const T_target Int)

(assert (>= T_dn0 0))
(assert (< T_dn0 T_dn1))
(assert (< T_dn1 T_dn2))
(assert (< T_dn2 T_target))

(define-fun branch_dn0_rpc_failure () Bool rpcFails)
(define-fun branch_dn1_attempted () Bool branch_dn0_rpc_failure)
(define-fun branch_dn1_rpc_failure () Bool
  (and branch_dn1_attempted rpcFails))
(define-fun branch_dn2_attempted () Bool branch_dn1_rpc_failure)
(define-fun branch_dn2_rpc_failure () Bool
  (and branch_dn2_attempted rpcFails))
(define-fun branch_checksum_group_false () Bool branch_dn2_rpc_failure)
(define-fun branch_final_target () Bool branch_checksum_group_false)

(assert rpcFails)
(assert branch_final_target)
(check-sat)
(get-value (rpcFails branch_dn0_rpc_failure branch_dn1_rpc_failure
            branch_dn2_rpc_failure branch_checksum_group_false
            branch_final_target
            T_dn0 T_dn1 T_dn2 T_target))

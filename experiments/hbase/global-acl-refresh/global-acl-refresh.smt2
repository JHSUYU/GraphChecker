; AuthManager.updateGlobalCache clears the live map before inserting the same
; ZooKeeper permission. AccessChecker can read in that interval.
(set-logic QF_LIA)
(declare-const clear-order Int)
(declare-const rpc-order Int)
(declare-const repopulate-order Int)
(declare-const old-acl-allows Bool)
(declare-const zk-acl-allows Bool)
(declare-const local-cache-allows Bool)
(declare-const access-denied Bool)
(assert old-acl-allows)
(assert zk-acl-allows)
(assert (< clear-order repopulate-order))
(assert (= local-cache-allows
  (ite (< rpc-order clear-order) old-acl-allows
    (ite (< rpc-order repopulate-order) false zk-acl-allows))))
(assert (= access-denied (not local-cache-allows)))

; A concurrent RPC arrives after clear and before repopulation: false denial.
(push)
(assert (< clear-order rpc-order))
(assert (< rpc-order repopulate-order))
(assert access-denied)
(check-sat)
(get-value (clear-order rpc-order repopulate-order old-acl-allows zk-acl-allows
  local-cache-allows access-denied))
(pop)

; After the ZooKeeper ACL has been fully installed, the same denial is impossible.
(push)
(assert (<= repopulate-order rpc-order))
(assert access-denied)
(check-sat)
(pop)

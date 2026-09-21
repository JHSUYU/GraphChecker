; Hand-composed GraphChecker-style target slice for an ACL watcher startup
; failure. Each query selects one watcher outcome arm. The persisted ZK grant
; is the WIRE-like input; the local AuthManager map is the STATE read.
(set-logic QF_UF)
(declare-const zk-global-admin-grant Bool)
(declare-const watcher-failure-arm Bool)
(declare-const watcher-success-arm Bool)
(declare-const local-global-admin-cache Bool)
(declare-const rpc-started Bool)
(declare-const ordinary-user Bool)
(declare-const admin-request-after-start Bool)
(declare-const access-denied-exception Bool)

; Authoritative ACL in ZooKeeper remains granted in both arms. The watcher
; succeeds only in the success arm. HBaseRpcServicesBase catches the
; KeeperException in the failure arm and starts the RPC server in either arm.
(assert zk-global-admin-grant)
(assert (xor watcher-failure-arm watcher-success-arm))
(assert (= local-global-admin-cache
  (and watcher-success-arm zk-global-admin-grant)))
(assert rpc-started)
(assert ordinary-user)
(assert admin-request-after-start)

; AccessChecker.requirePermission -> requireGlobalPermission ->
; AuthManager.authorizeUserGlobal reads the local cache. For an ordinary user
; without a group/superuser bypass, the failed check takes the throw arm.
(assert (= access-denied-exception
  (and rpc-started admin-request-after-start ordinary-user
       (not local-global-admin-cache))))

; KeeperException during initial watch: RPC serves despite missing grant.
(push)
(assert watcher-failure-arm)
(assert access-denied-exception)
(check-sat)
(get-value (zk-global-admin-grant watcher-failure-arm watcher-success-arm
  local-global-admin-cache rpc-started access-denied-exception))
(pop)

; Same request after a successful initial watch cannot take the throw arm.
(push)
(assert watcher-success-arm)
(assert access-denied-exception)
(check-sat)
(pop)

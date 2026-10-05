<!-- Moved into the repo at the 2026-10-05 handover from /bigtemp/vnr3ne/analysis/study-2026-10-04/hbase.md (investigator tables of 2026-10-04, read against our trees). Ids never move. Live status per check: docs/checks/README.md and docs/handover/STATE.md. -->
# HBase: study.txt items and bug_study bugs against OUR tree (2026-10-04)

Tree read: `/bigtemp/vnr3ne/wt/hbase-unified` (`gc/hbase-unified` `8b83a08afc`, HBase master 1790942bb2 + Java 8
backport + adapter). The study used HBase 2.6.6; its line numbers are statement-end lines (e.g. 2.6.6
`NamespaceStateManager:172` is the `throw new` at :168), so every site below was re-located in our tree.
bug_study's base commit `63d06533` is not in our tree; every added bug was re-read in our tree's code.

## Facts that apply to many rows

- **HBase 3 removed the 2.x client** (`ConnectionImplementation`, `HBaseAdmin`): study items 01-07 are ABSENT.
  Their checks now sit in `RawAsyncHBaseAdmin`/`AsyncRpcRetryingCaller` as `future.completeExceptionally(new X)`
  inside listener lambdas: no `throw new`, so they cannot be marked without changing behaviour. Two have a
  server-side equivalent with a real `throw new`, listed as optional re-sites (04r, 07r).
- **No HBASE_RPC fault door exists yet.** The library catalog (`hbase-startup` and `main`) has DOOR rows for
  Hadoop IPC, HDFS DataTransfer, Solr HTTP and `org.apache.zookeeper.ZooKeeper` writes (create/setData/delete/
  multi), but none for HBase IPC. `CausynthRpc` carries the trace and symbolic context but plants no FAULT. Any
  HBase FAULT case needs DOOR rows for the HBase RPC client (request at `AbstractRpcClient#callMethod`, response
  at call completion). Fault kinds the HBase retry code tells apart: IOException, CallTimeoutException,
  ConnectionClosedException, CallQueueTooBigException.
- **HBase's client retries undo most single faults**: `AsyncRpcRetryingCaller`, `RSProcedureDispatcher` and
  `RecoverableZooKeeper` retry. A single fault decides something only where the retry is not idempotent
  (bug 2 below) or where the caller gives up on the first attempt (`RSProcedureDispatcher#unableToConnectToServer`).
- **ZooKeeper data is LOST in HBase.** HBase has no store/read door (Solr has `SolrZkClient` hooks). Values read
  from znodes (master address, token keys, ZK-procedure payloads) reach the reader as concrete values.
- **Adapter coverage**: `CausynthHBaseCluster` hooks `HBaseTestingUtil`/`SingleProcessHBaseCluster` only. Tests
  that build `new LocalHBaseCluster(...)` directly (`TestRSStatusPage`, `SecureTestCluster` ->
  `TestGenerateDelegationToken`) get no node registration and no window. They need a small adapter hook.
- **Tests that throw on purpose**: several named tests reach the study throw by design (an expected-exception
  step). Such a case must declare a selector for a non-throwing occurrence (IDENTITY §9: the k-th match), not
  `first`, or use the alternative test given.
- All kept sites are already `throw new` (no `checkState`). The assert (17) is not kept. 31 throws
  `new ServiceException(new DoNotRetryIOException(..))`: mark the outer `ServiceException`. 35 sits in an
  anonymous visitor class (`HBaseFsck$N`), which the resolver handles.

## A. study.txt items (38)

| id | our file:line | kind | guard | coordination? | counterfactual that could flip it | IO ok? | test in our tree | fit |
|---|---|---|---|---|---|---|---|---|
| 01 | ABSENT (`ConnectionImplementation` removed; `AsyncNonMetaRegionLocator` has no dead-server check) | throw | `isDeadServer(sn)` -> RegionServerStoppedException | Y client cache vs master | - | - | `TestConnectionImplementation` ABSENT | DROP: site absent |
| 02 | ABSENT (nearest: `AsyncRpcRetryingCaller.java:205` completeExceptionally, in a lambda) | throw | `isTableDisabled` on relocate | Y | - | - | ABSENT | DROP: site absent |
| 03 | ABSENT | throw | getTableState null | - | - | - | NO_PATH | DROP |
| 04 | ABSENT client (`RawAsyncHBaseAdmin.java:1093` legacyFlush fallback, completeExceptionally). Server equivalent `AbstractStateMachineTableProcedure.java:163` `throw new TableNotEnabledException` (FlushTableProcedure preflight) | throw | `!ts.isEnabledOrEnabling()` | Y request vs TableStateManager | STATE: table state re-paired to a DISABLED/DISABLING writer; none concurrent in this test | ok | `TestMobStoreScanner#testMobStoreScanner` (admin.flush -> FlushTableProcedure) | client site DROP; optional re-site 04r, C |
| 05 | ABSENT | throw | - | - | - | - | NO_PATH | DROP |
| 06 | ABSENT | throw | - | - | - | - | NO_PATH | DROP |
| 07 | ABSENT client (`RawAsyncHBaseAdmin.java:2220` completeExceptionally). Server equivalent `SnapshotManager.java:1046` `throw new UnsupportedOperationException("...must be disabled...")` | throw | table state ENABLED at restore | Y request vs TableStateManager | STATE: state read re-paired to ENABLED (the disable is HB-before restore) | ok | `TestRestoreFlushSnapshotFromClient#testRestoreSnapshot` (3 RS) | client site DROP; optional re-site 07r, C |
| 08 | `master/ClusterSchemaServiceImpl.java:111` | throw NamespaceNotFoundException | `TableNamespaceManager.cache.get(ns)==null` | weak: the master's own cache vs its namespace procedures | STATE: cache read re-paired to INITIAL vs CreateNamespaceProcedure's put; HB-ordered by the client's wait, so CONFIRM should refute | ok | `namespace/TestNamespaceAuditor#testTableOperations` (2 masters, quota on) | C |
| 09 | `master/HMasterCommandLine.java:229` | throw | standalone ZK port | - | - | - | NO_PATH | DROP |
| 10 | `master/assignment/AssignmentManager.java:765` | throw HBaseIOException | `regionNode.getProcedure()!=null` | Y-weak: assign RPC vs TRSP attachment | STATE: getProcedure re-paired to the unassign TRSP's setProcedure (before its unset in confirmClosed); under regionNode lock and the client's wait | ok | `regionserver/TestRegionMove#testDisableAndMove` (2 RS) | C/B- |
| 11 | `AssignmentManager.java:769` | throw DoNotRetryRegionException | `!regionNode.isInState(expected)` | request vs master region state | the test REACHES it by design (move after unassign); target = the `admin.assign` occurrence (selector); STATE re-pair to CLOSING is HB-ordered | ok | same | C |
| 12 | `AssignmentManager.java:772` | throw DoNotRetryIOException | `isTableDisabled(table)` | request vs TableStateManager | REACHED by design (move after disable); at the assign occurrence the only other writer (disable) is HB-after, so it is ineligible | ok | same | C |
| 13 | `master/assignment/MergeTableRegionsProcedure.java:499` | throw MergeRegionException | `regionStateStore.hasMergeRegions(ri)` (meta Get) | CatalogJanitor GC vs new merge | STATE on the meta row (RS memstore); no other writer in the test | ok | `master/assignment/TestMergeTableRegionsProcedure#testMergeTwoRegions` (1 RS, procedure submitted in-JVM) | C |
| 14 | `MergeTableRegionsProcedure.java:503` | throw UnknownRegionException | `regionStates.getRegionState(enc)==null` | master map vs region creation | STATE INITIAL vs node creation: HB-ordered | ok | same | C |
| 15 | `MergeTableRegionsProcedure.java:507` | throw MergeRegionException | `!state.isOpened()` | Y: master's region view (driven by the RS's OPENED report) vs merge request | STATE: RegionStateNode.state re-paired to OPENING (TRSP write before the report); the test waits for assignment, CONFIRM decides | ok | same | B |
| 16 | `master/assignment/TransitRegionStateProcedure.java:427` | throw HBaseIOException "Failed to close region" | region still CLOSING at confirmClosed | Y master state vs RS close | FAULT at `RSProcedureDispatcher` executeProcedures, kind CallQueueTooBigException (first attempt -> remoteCallFailed); needs the HBASE_RPC door | ok | `TestTransitRegionStateProcedure` exists, but normal runs return at CLOSED before the guard | UNCERTAIN: not kept (no test evaluates the guard); could be promoted with a fault |
| 17 | `TransitRegionStateProcedure.java:435` | assert ABNORMALLY_CLOSED | after the CLOSED/CLOSING arms | Y | abnormal close only | ok | none evaluates it | UNCERTAIN: not kept |
| 18 | `TransitRegionStateProcedure.java:368` | throw | retries > assignRetryImmediatelyMaxAttempts | Y | needs several failed opens (several flips) | ok | none | UNCERTAIN: not kept |
| 19 | `master/procedure/ModifyTableProcedure.java:134` | throw HBaseIOException | unmodified CF count != modified (reopenRegions=false) | N: request vs stored descriptor | STATE on the FSTableDescriptors cache re-paired to an older descriptor; procedures run one after another | ok | `master/procedure/TestModifyTableProcedure#testModifyWillNotReopenRegions` (1 RS). REACHED by design (3rd modify), so selector = the 1st modify | C |
| 20 | `ModifyTableProcedure.java:138` | throw HBaseIOException | `isCoprocModified()` | N | same | ok | `testModifyWillNotReopenRegions` / `testModifyTableWithCoprocessorAndColumnFamilyPropertyChange` | C |
| 21 | `namespace/NamespaceStateManager.java:130` | throw QuotaExceededException | regions - tableRegions + incr > maxRegions | Y-weak: namespace count cache vs restore/split | STATE on NamespaceTableAndRegionInfo; no concurrent writer. maxRegions is a namespace-descriptor String, not a Configuration getter | ok | named `testRestoreSnapshotQuotaExceed` REACHES it by design; use `TestNamespaceAuditor#testRestoreSnapshot` | C |
| 22 | `NamespaceStateManager.java:168` | throw QuotaExceededException | regionCount + numRegions > maxRegions | Y-weak: its message says "transient ... ongoing split" (split vs create) | STATE: count re-paired to a version with a concurrent split's increment; needs a concurrent split | ok | named `testTableOperations` REACHES :168 and :160 by design; use `TestNamespaceAuditor#testDeleteTable` | C/B- |
| 23 | `procedure/ZKProcedureCoordinator.java:131` | throw | PB magic of a reached znode | - | timing + ZK data | - | none | UNCERTAIN: not kept |
| 24 | `procedure/ZKProcedureMemberRpcs.java:210` (caught at :217) | throw IllegalArgumentException | `!isPBMagicPrefix(znode data)` | N: format check | none in memory: the data crosses the ZK socket (no door) | ZK-lost | `master/procedure/TestFlushTableProcedureWithDoNotSupportFlushTableMaster#testFlushFallback` (3 RS) | C |
| 25 | `procedure2/store/wal/WALProcedureStore.java:727` | throw | store not running | - | - | - | NO_PATH (master uses RegionProcedureStore) | DROP |
| 26 | `WALProcedureStore.java:729` | throw | sync aborted | - | - | - | NO_PATH | DROP |
| 27 | `regionserver/HRegionServer.java:789` | throw | stopped while the ZK tracker is null | - | timing | - | none | UNCERTAIN: not kept |
| 28 | `HBaseServerBase.java:353` (putUpWebUI moved here) | throw IOException | `!isLocalAddress(bindAddress)` | N: config string | String config is not supported | startup (needs `recording_window=startup`) | `TestInfoServers#testInfoServersRedirect` | C |
| 29 | `regionserver/RSRpcServices.java:2139` (`replay`, @Deprecated) | throw NotServingRegionException | entries from several regions | N: request validation | - | - | `TestRegionReplicaReplicationEndpoint` ABSENT. In master `replay` is only the fallback (`AsyncRegionReplicationRetryingCaller` useReplay); `TestFallbackToUseReplay` uses mocks only | DROP: unreachable from a cluster test (the same validation is `replicateToReplica` :2228) |
| 30 | `RSRpcServices.java:2173` | throw IOException | `result[i]!=SUCCESS` | - | - | - | same | DROP: same reason |
| 31 | `RSRpcServices.java:1880` | throw ServiceException(DoNotRetryIOException) | RS startcode != request's serverStartCode | Y: master's ServerName view vs RS incarnation | CLOCK on the RS's startcode read moves both sides (the master's copy is the same symbol via regionServerStartup), so no flip. The real trigger is an RS restart on the same host:port | ok | `TestRegionMove#testDisableAndMove` | C |
| 32 | `regionserver/handler/RegionReplicaFlushHandler.java:189` | throw | catch path after the flush RPC | - | - | - | none | UNCERTAIN: not kept |
| 33 | `security/token/AuthenticationTokenSecretManager.java:141` | throw InvalidToken | ZKWatcher aborted | - | - | - | none | UNCERTAIN: not kept |
| 34 | `AuthenticationTokenSecretManager.java:160` | throw InvalidToken | `allKeys.get(keyId)==null` after refreshKeys | Y: token keyId (master leader) vs the RS key map (via ZK) | STATE INITIAL on allKeys needs two re-pairings, and the second read follows the same thread's refreshKeys write, so it is infeasible. keyId crosses SASL (no door); keys cross ZK (lost). The adjacent :135 expiry-vs-RS-clock check is CLOCK-flippable (skew >= 7 d max lifetime) but is not a study item | ok | `security/token/TestGenerateDelegationToken#testOnlyToken` (SecureTestCluster: MiniKdc + Kerberos + direct LocalHBaseCluster: adapter hook needed) | C |
| 35 | `util/HBaseFsck.java:2742` (anonymous visitor) | throw IOException | two meta entries with the same encoded name | N: local invariant of a scan | none | ok | `util/TestHBaseFsckReplication#test` (1 RS) | C |
| 36 | `hbase-zookeeper .../MasterAddressTracker.java:236` | throw | backup master znode null | - | - | - | NO_PATH | DROP |
| 37 | `MasterAddressTracker.java:206` | throw IOException | master znode data == null | Y: the published ZK address vs its reader | ZK data lost. A ZK WRITE-door fault on the master znode create stops activation instead | ZK-lost | `regionserver/http/TestRSStatusPage#testStatusPage` (direct LocalHBaseCluster: adapter hook) | C |
| 38 | `MasterAddressTracker.java:177` | throw | master address null | - | - | - | NO_PATH | DROP |

Count: 23 TESTED. 6 are dropped for a hard reason: 01, 02, 04 and 07 are ABSENT (04 and 07 have optional re-sites);
29 and 30 are unreachable from a cluster test in master. 17 TESTED items are kept. The 15 NO_PATH or UNCERTAIN items
are not kept because no cluster test evaluates their guard; 16 is promotable once the HBASE_RPC door exists.

## B. bug_study bugs not covered by README §0.3

The first batch (`HBase.txt` #01-#15) keeps its §0.3 verdicts: #14 is our case, the rest are rejected or second
tier. Master does not change any of them. HBase #13 (refreshMeta) exists in master but stays dropped (second tier;
its chain runs through HDFS scans).

| bug | in our tree (fatal) | coordination? | single counterfactual | chain in memory? | cluster test | fit | study site? |
|---|---|---|---|---|---|---|---|
| H2-01 CreateNamespace vs removeRSGroup | YES: `rsgroup/RSGroupInfoManagerImpl.java:385-391` scans persisted namespaces only; fatal `master/procedure/MasterProcedureUtil.java:231` (via CreateTableProcedure:310-319) | Y: namespace procedure's one-shot group check vs the group manager's removal check | STATE: removeRSGroup's namespace-cache scan re-paired to INITIAL (N not yet inserted) while the procedure is in flight | Y (TableNamespaceManager cache, RSGroup holder map, all on the master) | self-written (no test interleaves an in-flight create with a removal) | **ADD, B** | no |
| H2-02 rename skips namespaces | yes | Y | none: deterministic | - | - | C | no |
| H2-03 rename partial failure | yes | Y | coprocessor failure; no door | - | - | C | no |
| H2-04 moveServers ignores inherited group | yes | Y | none: deterministic | - | - | C | no |
| H2-05 ModifyTable vs removeRSGroup | yes, same fatal :231 | Y | STATE on the FSTableDescriptors cache | cache, or an HDFS rescan | self-written | variant of H2-01, not added | no |
| H2-06 snapshot postCompleted failure | yes | Y | coprocessor failure; completed dir on HDFS | IO | - | C | no |
| H2-07 snapshot cleaner init | yes | Y | negative period + archived HFile deletion | IO | - | C | no |
| H2-08 space-quota refresher half-published | yes: `SpaceViolationPolicyEnforcementFactory` IAE | Y | STATE (fits) | Y | quota tests | C: recovers by itself when the chore finishes (not hard to recover) | no |
| H2-09 throttle switch crash | yes | Y | process crash at a cut point | - | - | C | no |
| H2-10 quota delete then enable fails | yes; fatal = `AbstractStateMachineTableProcedure:163` (04r) | Y | the enable is a master->master admin RPC that is retried; the client sees an exception | - | - | C | 04r (re-site) |
| H2-11 truncate(false) keeps ns count | yes; fatal = study HBASE-22 site `:168` | Y | none: deterministic omission; master failover fixes it | - | - | C | HBASE-22 |
| H2-12 zero quota factor | yes | Y | deterministic; recovers at the next refresh | - | - | C | no |
| H2-13/14/15 descriptor / listing read errors | yes | Y | HDFS read faults | IO | - | C | no |
| H2-16 backup lock reply lost | YES: `hbase-backup/.../BackupSystemTable.java:495-505` (checkAndMutate builder with NO_NONCE, `RawAsyncTableImpl.java:350-360`); fatal `:504` ExclusiveOperationException, then `BackupManager.java:329` timeout; repair (`BackupCommands.java:1135-1165`) never frees a lock with no RUNNING session | Y: client session state vs the persisted lock row (RS) | FAULT on the HBASE_RPC RESPONSE of the first CAS; the client's own retry re-runs the CAS and gets false | Y (RS memstore cell -> CAS result -> protobuf response -> client boolean) | existing `backup/TestBackupManager#testStartBackupExclusiveOperation` (1 RS) | **ADD, A-/B** (needs the door + hbase-backup harness) | no |
| H2-17 refreshMeta crash | yes | Y | crash cut | - | - | C | no |
| H2-18 restore truncate failure | yes | Y | coprocessor failure; admin RPC retried; MR | - | - | C | no |
| H2-19 shared locate future | yes | Y | timer; completeExceptionally; transient | - | - | C | no |
| H2-20 meta replica count | yes | Y | mock registry; transient | - | - | C | no |
| H2-21 getAll overwrites invalidation | yes: `util/FSTableDescriptors.java:241,301,719`; fatal `SnapshotManager.java:855` | Y | STATE on `fsvisited` (fits) | Y | self-written | C: another refreshMeta or a master restart clears it (fails hard-to-recover). Nearest miss | no |
| H2-22 backup id before lock | yes | Y | both ids come from one client clock (a per-node skew moves both); manifests on HDFS | IO | - | C | no |
| H2-23 visibility ZK mirror | yes | Y | coprocessor failure; ZK mirror lost | ZK-lost | - | C | no |
| H2-24 backup delete rollback | yes | Y | manifest file | IO | - | C | no |
| H2-25 hotness counter leak | yes | N: local counter | row-lock timed wait | - | - | C | no |
| H2-26 TIMELINE first error | yes | Y | the throw echoes the injected primary failure | - | - | C | no |
| H2-27 buffered mutator close race | yes | N: client-local | generic FutureUtils timeout | - | - | C | no |
| H2-28 cluster id rewrite crash | yes | Y | HDFS files + crash | IO | - | C | no |
| H2-29 PITR mutual delete | yes | Y | deterministic CLI | - | - | C | no |
| H2-30 namespace migration | yes; fatal = study HBASE-08 site `:111` | Y | upgrade fixture + child failure + failover | IO | - | C | HBASE-08 |
| H3-01 cache clear orphans locate | yes | Y | client timer, completeExceptionally; transient | - | - | C | no |
| H3-02 delayed archive report | yes | Y | long chain through archive/manifests/chores; next full compute fixes it | partly IO | - | C | no |
| H3-03 RS verifier cache | yes | Y | manifest files | IO | - | C | no |
| H3-04 refreshMeta deletes hbase:quota | yes | Y | none: deterministic | IO | - | C | no |
| H3-05 refreshMeta keeps ns quota cache | yes; fatal at `NamespaceStateManager:160` | Y | needs a table dir moved on HDFS | IO | - | C | next to HBASE-22 |
| H3-06 FAILED history keeps incremental set | yes | Y | failure injection + MR | - | - | C | no |
| H3-07 remote verify ignores missing manifest | yes | Y | listStatus omission | IO | - | C | no |
| H3-08 Meta FILE tracker listing | yes | Y | listing fault | IO | - | C | no |
| H3-09 quota snapshot advance then enable fails | yes; fatal = `:163` (04r) | Y | the enable fails only via coprocessor; the self-RPC is retried | - | - | C | 04r |
| H3-10 split-WAL worker replay leak | yes | Y | master failover at an exact point + remote split failure; the fatal is a client completeExceptionally | - | - | C | no |

## C. Known cases mapped to study items

- `hbase-bugs-master-active-time` (bug_study HBase #14): `master/MasterRpcServices.java:2629` (marked), CLOCK,
  `TestSplitWALProcedure#testMasterRestart`. **No study item is this throw.** Its closest relative is HBASE-31
  (`RSRpcServices:1880`, the RS refusing a request whose master-side ServerName names another incarnation): the
  same identity-across-nodes idea, but a different throw, and not CLOCK-flippable (see A).
- bug_study fatals that land on study sites but are excluded: H2-11 -> HBASE-22 (`:168`), H2-30 -> HBASE-08
  (`:111`), H2-10 and H3-09 -> 04r (`AbstractStateMachineTableProcedure:163`).

## D. Pick list (owner ruling 2026-10-04: every TESTED study item kept unless there is a hard reason)

Shared prerequisites:
- **P1**: HBASE_RPC DOOR rows in the library catalog (bug 2; also promotes 16).
- **P2**: adapter hook for a directly built `LocalHBaseCluster` (34, 37).
- **P3**: `hbase-backup` in `experiments/hbase/system.sh` (module, surefire report, classes); its native JDK 8
  build is not done yet (`hbase-backup/target` is absent).
- **P4**: a selector target where the test throws by design (11, 12, 19).
- **P5**: `recording_window=startup` for 28 (owner opt-in).

No kept site needs a `checkState`/assert rewrite. Each needs only `throw new @CausynthExceptionTarget("<id>") E(..)`.

1. **hbase-adhoc-08**: `ClusterSchemaServiceImpl.java:111`, `TestNamespaceAuditor#testTableOperations`; scope
   ClusterSchemaServiceImpl, TableNamespaceManager, procedure/CreateNamespaceProcedure, HMaster(createTable),
   MasterRpcServices. STATE INITIAL on the namespace cache. Fit C: HB-ordered, expect a refutation.
2. **hbase-adhoc-10**: `AssignmentManager.java:765`, `TestRegionMove#testDisableAndMove`; scope AssignmentManager,
   RegionStateNode, RegionStates, TransitRegionStateProcedure. STATE on regionNode.procedure. C/B-.
3. **hbase-adhoc-11**: `AssignmentManager.java:769`, same test, selector = the `admin.assign` occurrence (the move
   throws by design); same scope. C.
4. **hbase-adhoc-12**: `AssignmentManager.java:772`, same test and selector rule; scope + TableStateManager. C.
5. **hbase-adhoc-13**: `MergeTableRegionsProcedure.java:499`, `TestMergeTableRegionsProcedure#testMergeTwoRegions`;
   scope MergeTableRegionsProcedure, RegionStateStore, CatalogFamilyFormat. C.
6. **hbase-adhoc-14**: `:503`, same test; scope + RegionStates. C.
7. **hbase-adhoc-15**: `:507`, same test; scope + RegionStateNode, AssignmentManager#reportRegionStateTransition,
   TransitRegionStateProcedure. STATE: the region state re-paired to OPENING (master view vs the RS's report). B:
   the best of the study items.
8. **hbase-adhoc-19**: `ModifyTableProcedure.java:134`, `TestModifyTableProcedure#testModifyWillNotReopenRegions`,
   selector = the 1st ModifyTableProcedure; scope ModifyTableProcedure, util/FSTableDescriptors. C.
9. **hbase-adhoc-20**: `ModifyTableProcedure.java:138`, same test (or
   `#testModifyTableWithCoprocessorAndColumnFamilyPropertyChange`); same scope. C.
10. **hbase-adhoc-21**: `NamespaceStateManager.java:130`, `TestNamespaceAuditor#testRestoreSnapshot` (the named
    QuotaExceed test throws by design); scope NamespaceStateManager, NamespaceTableAndRegionInfo, NamespaceAuditor,
    quotas/MasterQuotaManager, procedure/RestoreSnapshotProcedure. C.
11. **hbase-adhoc-22**: `NamespaceStateManager.java:168`, `TestNamespaceAuditor#testDeleteTable`; scope as 21 +
    CreateTableProcedure. Split-vs-create count. C/B-.
12. **hbase-adhoc-24**: `ZKProcedureMemberRpcs.java:210`,
    `TestFlushTableProcedureWithDoNotSupportFlushTableMaster#testFlushFallback`; scope ZKProcedureMemberRpcs,
    ZKProcedureCoordinator, ZKProcedureUtil. C: ZK data lost, format check.
13. **hbase-adhoc-28**: `HBaseServerBase.java:353`, `TestInfoServers#testInfoServersRedirect`, needs P5; scope
    HBaseServerBase, common util/Addressing. C: config string.
14. **hbase-adhoc-31**: `RSRpcServices.java:1880` (thrown type ServiceException), `TestRegionMove#testDisableAndMove`;
    scope RSRpcServices, HRegionServer, procedure/RSProcedureDispatcher, ServerManager, MasterRpcServices. C: CLOCK
    moves both sides.
15. **hbase-adhoc-34**: `AuthenticationTokenSecretManager.java:160`, `TestGenerateDelegationToken#testOnlyToken`,
    needs P2 + MiniKdc on the VM; scope AuthenticationTokenSecretManager, ZKSecretWatcher, ipc/ServerRpcConnection.
    C (the adjacent :135 expiry is the CLOCK-checkable sibling, not a study item).
16. **hbase-adhoc-35**: `HBaseFsck.java:2742`, `TestHBaseFsckReplication#test`; scope HBaseFsck (+ its visitor class),
    HbckRegionInfo. C.
17. **hbase-adhoc-37**: `MasterAddressTracker.java:206`, `TestRSStatusPage#testStatusPage`, needs P2; scope
    zookeeper MasterAddressTracker, master/ActiveMasterManager, HMaster. C: ZK data lost.
18. (optional re-site) **hbase-adhoc-04**: `AbstractStateMachineTableProcedure.java:163`,
    `TestMobStoreScanner#testMobStoreScanner`; scope AbstractStateMachineTableProcedure, FlushTableProcedure,
    TableStateManager. C. It is also the fatal of H2-10 and H3-09.
19. (optional re-site) **hbase-adhoc-07**: `SnapshotManager.java:1046`,
    `TestRestoreFlushSnapshotFromClient#testRestoreSnapshot`; scope SnapshotManager, TableStateManager. C.
20. **hbase-bugs-backup-lock-reply-lost** (H2-16): target `BackupSystemTable.java:504` with selector = the first
    acquirer's first `startBackupExclusiveOperation` (the other thread throws there by contention in the passing
    run). Alternative target `BackupManager.java:329` (never reached in the passing run) = FAULT + a nested CLOCK on
    the wait loop's `currentTime`. Workload: existing `TestBackupManager#testStartBackupExclusiveOperation`.
    Needs P1 + P3. Counterfactual: FAULT on the RESPONSE of the `ifNotExists` checkAndMutate. Chain: the RS commits
    YES; the reply is lost; `AsyncRpcRetryingCaller` resends the CAS (no nonce); the CAS reads its own YES ->
    false -> the `ifEquals(NO)` CAS -> false -> throw. The lock stays YES forever, and `backup repair` skips it.
    Scope: backup BackupSystemTable, BackupManager; client RawAsyncTableImpl,
    AsyncSingleRequestRpcRetryingCaller/AsyncRpcRetryingCaller; server RSRpcServices#mutate, HRegion#checkAndMutate.
    Fit A-/B.
21. **hbase-bugs-ns-rsgroup-removal** (H2-01): target `MasterProcedureUtil.java:231`, selector = the
    CreateTableProcedure occurrence. Self-written test justified (no existing test interleaves an in-flight
    namespace creation with a group removal; `TestRSGroupsAdmin1#testNamespaceConstraint` does them one after
    another, so its removal is refused and a re-pairing would be HB-refuted). The test: enable rsgroup, 2 RS,
    `addRSGroup(G)` + move 1 server in; `createNamespaceAsync(N, hbase.rsgroup.name=G)` without waiting; move the
    server out; `removeRSGroup(G)` (refused in the recording, caught); join; `createTable(N:T)` (caught).
    Counterfactual: STATE INITIAL on `removeRSGroup`'s namespace scan (`TableNamespaceManager.cache` values, read
    at `RSGroupInfoManagerImpl:385`). Chain: the removal passes -> holder drops G -> CreateTableProcedure inherits
    G from N -> `getRSGroup(G)==null` -> throw. Persistent: N->G is in meta and G is gone from hbase:rsgroup; a
    restart does not fix it. Scope: rsgroup/RSGroupInfoManagerImpl, procedure/CreateNamespaceProcedure,
    AbstractStateMachineNamespaceProcedure, CreateTableProcedure, MasterProcedureUtil, TableNamespaceManager,
    ClusterSchemaServiceImpl. Fit B: the risk is re-pairing a container iteration (`cache.values().stream()`).

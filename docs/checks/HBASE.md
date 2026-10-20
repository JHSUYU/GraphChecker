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
| 11 | `AssignmentManager.java:769` | throw DoNotRetryRegionException | `!regionNode.isInState(expected)` | request vs master region state | the test REACHES it by design (both moves: after the unassign, and after the disable, whose region is CLOSED); its first occurrence, the `admin.unassign`'s, does not throw and is the case's target; STATE re-pair to an earlier state is HB-ordered | ok | same | C |
| 12 | `AssignmentManager.java:772` | throw DoNotRetryIOException | `isTableDisabled(table)` | request vs TableStateManager | not reached by the move after the disable (its region is CLOSED, so :769 throws first); evaluated at the `admin.unassign` and the `admin.assign`, neither throwing; the target is the first, and the only other writer (the disable) is HB-after both | ok | same | C |
| 13 | `master/assignment/MergeTableRegionsProcedure.java:499` | throw MergeRegionException | `regionStateStore.hasMergeRegions(ri)` (meta Get) | CatalogJanitor GC vs new merge | STATE on the meta row (RS memstore); no other writer in the test | ok | `master/assignment/TestMergeTableRegionsProcedure#testMergeTwoRegions` (1 RS, procedure submitted in-JVM) | C |
| 14 | `MergeTableRegionsProcedure.java:503` | throw UnknownRegionException | `regionStates.getRegionState(enc)==null` | master map vs region creation | STATE INITIAL vs node creation: HB-ordered | ok | same | C |
| 15 | `MergeTableRegionsProcedure.java:507` | throw MergeRegionException | `!state.isOpened()` | Y: master's region view (driven by the RS's OPENED report) vs merge request | STATE: RegionStateNode.state re-paired to OPENING (TRSP write before the report); the test waits for assignment, CONFIRM decides | ok | same | B |
| 16 | `master/assignment/TransitRegionStateProcedure.java:427` | throw HBaseIOException "Failed to close region" | region still CLOSING at confirmClosed | Y master state vs RS close | FAULT at `RSProcedureDispatcher` executeProcedures, kind CallQueueTooBigException (first attempt -> remoteCallFailed); needs the HBASE_RPC door | ok | `TestTransitRegionStateProcedure` exists, but normal runs return at CLOSED before the guard | UNCERTAIN: not kept (no test evaluates the guard); could be promoted with a fault |
| 17 | `TransitRegionStateProcedure.java:435` | assert ABNORMALLY_CLOSED | after the CLOSED/CLOSING arms | Y | abnormal close only | ok | none evaluates it | UNCERTAIN: not kept |
| 18 | `TransitRegionStateProcedure.java:368` | throw | retries > assignRetryImmediatelyMaxAttempts | Y | needs several failed opens (several flips) | ok | none | UNCERTAIN: not kept |
| 19 | `master/procedure/ModifyTableProcedure.java:134` | throw HBaseIOException | unmodified CF count != modified (reopenRegions=false) | N: request vs stored descriptor | STATE on the FSTableDescriptors cache re-paired to an older descriptor; procedures run one after another | ok | `master/procedure/TestModifyTableProcedure#testModifyWillNotReopenRegions` (1 RS). REACHED by design (Test 3's modify); the guard runs in the procedure's constructor (`preflightChecks`, on the test thread), and its first occurrence, Test 1's modify, does not throw | C |
| 20 | `ModifyTableProcedure.java:138` | throw HBaseIOException | `isCoprocModified()` | N | same | ok | `testModifyWillNotReopenRegions` / `testModifyTableWithCoprocessorAndColumnFamilyPropertyChange` | C |
| 21 | `namespace/NamespaceStateManager.java:130` | throw QuotaExceededException | regions - tableRegions + incr > maxRegions | Y-weak: namespace count cache vs restore/split | STATE on NamespaceTableAndRegionInfo; no concurrent writer. maxRegions is a namespace-descriptor String, not a Configuration getter | ok | named `testRestoreSnapshotQuotaExceed` REACHES it by design; use `TestNamespaceAuditor#testRestoreSnapshot` | C |
| 22 | `NamespaceStateManager.java:168` | throw QuotaExceededException | regionCount + numRegions > maxRegions | Y-weak: its message says "transient ... ongoing split" (split vs create) | STATE: count re-paired to a version with a concurrent split's increment; needs a concurrent split | ok | named `testTableOperations` REACHES :168 and :160 by design; the case runs our `TestCausynthTruncatedTableQuota#createWhileATruncatedTableIsDeleted`, which holds HBASE-30483 (§E) | B- |
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
| 34 | `AuthenticationTokenSecretManager.java:160` | throw InvalidToken | `allKeys.get(keyId)==null` after refreshKeys | Y: token keyId (master leader) vs the RS key map (via ZK) | One counterfactual since the workload makes the first `allKeys.get` miss natively (it removes the key first: the key's watch event not yet processed), so `refreshKeys` runs, and the second read stays null only if `refreshKeys` adds no key: its ZooKeeper read fails (a READ door fault: `KeeperException` -> `watcher.abort`; NZ3-34's `SessionExpired`), misses the key's znode (a stale read: no single-server workload), or `addKey` ignores the key while this server's elector believes it leads (`isMaster`). The case stays at world depth 1 (`hbase-adhoc/case.sh`, a superset). keyId crosses SASL (no door); keys cross ZK (lost). The adjacent :135 expiry-vs-RS-clock check is CLOCK-flippable (skew >= 7 d max lifetime) but is not a study item | ok | `security/token/TestGenerateDelegationToken#testOnlyToken` (SecureTestCluster: MiniKdc + Kerberos + direct LocalHBaseCluster: adapter hook needed) | C |
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
  the tree's `TestCausynthMasterActiveTime#reportOpenedToTheNextMaster` (a master failover while a region opens).
  **No study item is this throw.** Its closest relative is HBASE-31
  (`RSRpcServices:1880`, the RS refusing a request whose master-side ServerName names another incarnation): the
  same identity-across-nodes idea, but a different throw, and not CLOCK-flippable (see A).
- bug_study fatals that land on study sites but are excluded: H2-11 -> HBASE-22 (`:168`), H2-30 -> HBASE-08
  (`:111`), H2-10 and H3-09 -> 04r (`AbstractStateMachineTableProcedure:163`).

## D. Pick list (owner ruling 2026-10-04: every TESTED study item kept unless there is a hard reason)

Shared prerequisites:
- **P1**: HBASE_RPC DOOR rows in the library catalog (bug 2; also promotes 16): agent H3's.
- **P2**: adapter hook for a directly built `LocalHBaseCluster` (34, 37): done on the tree (gc/hb-checks
  `bded085587`): `LocalHBaseCluster.Observer`, installed by every `HBaseTestingUtil` in automatic mode, has
  `CausynthHBaseCluster` configure such a cluster, register its nodes and open the window once it is up, and close
  the window before it shuts down; `startMiniDFSCluster` starts no HDFS in automatic mode, so these tests' own
  HDFS is the local filesystem too.
- **P3**: `hbase-backup`: builds on JDK 8 (`-pl hbase-server,hbase-backup -am install`), and
  `TestBackupManager#testStartBackupExclusiveOperation` passes on the local filesystem as written (the test needs no
  HDFS or MapReduce); `experiments/hbase/system.sh` names its sources and its test module (`hbase_test_module`),
  and `build.sh` builds a workload's own module with hbase-server and runs it there.
- **P4**: a target occurrence where the test throws by design (11, 12, 19, 20): each one's first occurrence does
  not throw, so their rows say `first`. 22 and ns-rsgroup-removal take a selector (§E: the region of the target on
  master0 and the occurrence's index in it, read off a seed recording); backup-lock-reply-lost's `first` is
  checked at its first seed.
- **P5**: `recording_window=startup` for 28 (owner opt-in): its row's window is `startup`, which
  `hbase-adhoc/case.sh` declares as `recording_window=startup`; the adapter opens the window before the HBase
  cluster starts when `MessageDoors#startupWindow` says so (as hbase-bugs-master-active-time's).

No kept site needs a `checkState`/assert rewrite. Each needs only `throw new @CausynthExceptionTarget("<id>") E(..)`.
The scopes below are the study's lists; each case's row (§E) cuts them to the classes whose code the target's guard
reads and whose code writes what it reads (owner 2026-10-19: "范围弄小点").

1. **hbase-adhoc-08**: `ClusterSchemaServiceImpl.java:111`, `TestNamespaceAuditor#testTableOperations`; scope
   ClusterSchemaServiceImpl, TableNamespaceManager, procedure/CreateNamespaceProcedure, HMaster(createTable),
   MasterRpcServices. STATE INITIAL on the namespace cache. Fit C: HB-ordered, expect a refutation.
2. **hbase-adhoc-10**: `AssignmentManager.java:765`, `TestRegionMove#testDisableAndMove`; scope AssignmentManager,
   RegionStateNode, RegionStates, TransitRegionStateProcedure. STATE on regionNode.procedure. C/B-.
3. **hbase-adhoc-11**: `AssignmentManager.java:769`, same test, the first occurrence (`admin.unassign`'s; both
   moves throw by design); same scope. C.
4. **hbase-adhoc-12**: `AssignmentManager.java:772`, same test, the first occurrence (`admin.unassign`'s); scope +
   TableStateManager. C.
5. **hbase-adhoc-13**: `MergeTableRegionsProcedure.java:499`, `TestMergeTableRegionsProcedure#testMergeTwoRegions`;
   scope MergeTableRegionsProcedure, RegionStateStore, CatalogFamilyFormat. C.
6. **hbase-adhoc-14**: `:503`, same test; scope + RegionStates. C.
7. **hbase-adhoc-15**: `:507`, same test; scope + RegionStateNode, AssignmentManager#reportRegionStateTransition,
   TransitRegionStateProcedure. STATE: the region state re-paired to OPENING (master view vs the RS's report). B:
   the best of the study items.
8. **hbase-adhoc-19**: `ModifyTableProcedure.java:134`, `TestModifyTableProcedure#testModifyWillNotReopenRegions`,
   the first occurrence (Test 1's ModifyTableProcedure); scope ModifyTableProcedure, util/FSTableDescriptors. C.
9. **hbase-adhoc-20**: `ModifyTableProcedure.java:138`, same test (or
   `#testModifyTableWithCoprocessorAndColumnFamilyPropertyChange`); same scope. C.
10. **hbase-adhoc-21**: `NamespaceStateManager.java:130`, `TestNamespaceAuditor#testRestoreSnapshot` (the named
    QuotaExceed test throws by design); scope NamespaceStateManager, NamespaceTableAndRegionInfo, NamespaceAuditor,
    quotas/MasterQuotaManager, procedure/RestoreSnapshotProcedure. C.
11. **hbase-adhoc-22**: `NamespaceStateManager.java:168`, our `TestCausynthTruncatedTableQuota#createWhileATruncatedTableIsDeleted`
    (HBASE-30483's truncate in a passing recording, §E); scope as 21. Deletion-vs-create count. B-.
12. **hbase-adhoc-24**: `ZKProcedureMemberRpcs.java:210`,
    `TestFlushTableProcedureWithDoNotSupportFlushTableMaster#testFlushFallback`; scope ZKProcedureMemberRpcs,
    ZKProcedureCoordinator, ZKProcedureUtil. C: ZK data lost, format check.
13. **hbase-adhoc-28**: `HBaseServerBase.java:353`, `TestInfoServers#testInfoServersRedirect`, needs P5; scope
    HBaseServerBase, common util/Addressing. C: config string.
14. **hbase-adhoc-31**: `RSRpcServices.java:1880` (thrown type ServiceException),
    `TestRetainAssignmentOnRestart#testForceRetainAssignment` (2026-10-19, was TestRegionMove: the guard compares the
    region server's own start code with the master's copy, both run constants there, so no world flips it): a region
    server stops and starts again on the same port with a new start code, and the master retains its regions on it.
    The target is the restarted server's first check (auto0/rs3, REGION.4a0683a9 = throwOnWrongStartCode(ExecuteProceduresRequest), #1); the flip needs the master's open request to carry
    the old incarnation's start code, a STATE re-pairing of `RegionStateNode.regionLocation` read for the open to its
    write by the first assignment. Scope RSRpcServices, procedure/RSProcedureDispatcher, assignment/RegionStateNode,
    assignment/RegionRemoteProcedureBase.
15. **hbase-adhoc-34**: `AuthenticationTokenSecretManager.java:160`, `TestGenerateDelegationToken#testOnlyToken`,
    needs P2 + MiniKdc on the VM; scope AuthenticationTokenSecretManager, ZKSecretWatcher, ipc/ServerRpcConnection.
    C (the adjacent :135 expiry is the CLOCK-checkable sibling, not a study item).
16. **hbase-adhoc-35**: `HBaseFsck.java:2742`, `TestHBaseFsckReplication#test`; scope HBaseFsck (+ its visitor class),
    HbckRegionInfo. C.
17. **hbase-adhoc-37**: `MasterAddressTracker.java:206`, `TestRSStatusPage#testStatusPage`, needs P2; scope
    zookeeper MasterAddressTracker, master/ActiveMasterManager, HMaster. C: ZK data lost.
18. (re-site, wanted) **hbase-adhoc-04**: `AbstractStateMachineTableProcedure.java:163`,
    `TestMobStoreScanner#testMobStoreScanner`; scope AbstractStateMachineTableProcedure, FlushTableProcedure,
    TableStateManager. C. It is also the fatal of H2-10 and H3-09 (HBASE-30484), which no single counterfactual
    reaches from a passing recording (§E), so the workload stays.
19. (re-site, wanted) **hbase-adhoc-07**: `SnapshotManager.java:1046`,
    `TestRestoreFlushSnapshotFromClient#testRestoreSnapshot`; scope SnapshotManager, TableStateManager. C.
20. **hbase-bugs-backup-lock-reply-lost** (H2-16): target `BackupSystemTable.java:504` with selector = the first
    acquirer's first `startBackupExclusiveOperation` (the other thread throws there by contention in the passing
    run). Alternative target `BackupManager.java:329` (never reached in the passing run) = FAULT + a nested CLOCK on
    the wait loop's `currentTime`. Workload: ours, `TestCausynthBackupLockReplyLost` (one acquirer; §E).
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
    `addRSGroup(G)` + move the server not holding meta in; `createNamespaceAsync(N, hbase.rsgroup.name=G)`, then a
    1 s sleep (not a wait on the procedure: the RPC returns before the procedure's prepare, and only time orders the
    namespace's insertion before the removal); move the server out; `removeRSGroup(G)` (refused in the recording,
    caught); join; `createTable(N:T)` (refused for the empty group at `MasterProcedureUtil:216`, caught):
    `TestCausynthNamespaceGroupRemoval#removeTheGroupOfANamespaceBeingCreated` in the fork.
    Counterfactual: STATE INITIAL on `removeRSGroup`'s namespace scan (`TableNamespaceManager.cache` values, read
    at `RSGroupInfoManagerImpl:385`). Chain: the removal passes -> holder drops G -> CreateTableProcedure inherits
    G from N -> `getRSGroup(G)==null` -> throw. Persistent: N->G is in meta and G is gone from hbase:rsgroup; a
    restart does not fix it. Scope: rsgroup/RSGroupInfoManagerImpl, procedure/CreateNamespaceProcedure,
    AbstractStateMachineNamespaceProcedure, CreateTableProcedure, MasterProcedureUtil, TableNamespaceManager,
    ClusterSchemaServiceImpl. Fit B: the risk is re-pairing a container iteration (`cache.values().stream()`).

## E. State per check (2026-10-19, at the owner's stop 23:10)

Tree: the fork's `graphchecker/hbase-checks` = local `gc/hbase-checks` `985a0dfe91` (sites first re-located on
`c72b1d7e80`; every site of §D was re-located there: none moved). Engine: `system/hbase` (STATE §H). Summary at the
stop: 1 PASS (backup-lock-reply-lost), 1 SAT confirmed in the VM awaiting REPRODUCE (04 = HBASE-30484, PASS since 2026-10-20: NR3-04), 5 UNSAT all
vacuous (08, 13, 31-old, 34, 37), the rest stopped mid-run or not run; the next runs are TODO HBase 1. Each target is marked `throw new @CausynthExceptionTarget("<case>") E(..)`. Native: each workload alone,
JDK 8, the automatic cluster on the local filesystem (no DataNode or NameNode), the test's own time from its surefire
report (`/bigtemp/vnr3ne/analysis/hbase-2026-10-19/checks/native.tsv`). The row's scope is the case's classes
(`root=:class`, the class and its nested classes): the target's class, the class whose field its guard reads, and
the class whose code writes that field.

| case | target | workload | window | occurrence | row scope | native | state |
|---|---|---|---|---|---|---|---|
| hbase-adhoc-04 | AbstractStateMachineTableProcedure:163 | TestCausynthQuotaEnableAfterAdvance#enableAfterTheSnapshotAdvanced (ours, HBASE-30484, below) | up | `auto0/master0#epoch0/region/REGION.98cba534-e757-3508-990f-4855688e1e1e#2`: the test's flush (#1 is its own disable) | AbstractStateMachineTableProcedure, TableStateManager | 2.3 s | **DONE, PASS** (owner bug HBASE-30484): SAT MARKER_FLIPPED, confirmed in the VM, reproduced natively 7/10 with control 0/10, report.py PASS, 889 s (NR3-04, `gc-out/hbase-rpc/accept-NR3-04`; snapshot hb2-rpc-1 53a4ecfdf, tree set hb-int-trees-1 985a0dfe91, depth 0); the moved root is an `HBASE_RPC` REQUEST fault on the observer connection's `ClientMetaService.GetActiveMaster`, the master lookup of its enable (HC21-04 moved the `EnableTable` request itself: the same lost enable one hop later), so the first observer run fails after it persisted and advanced the snapshot, the second finds nothing to change, the table stays disabled and the flush is refused at :163. The 3 native runs that did not reproduce took the fatal at the anchor with the root planted, but a procedure step ran under another hand-off nesting (TODO HBase 11); REPRODUCE needed the checked orders and the turn-counted plant rule (TODO HBase 3, PIPELINE §10/§10b) |
| hbase-adhoc-07 | SnapshotManager:1046 | TestRestoreFlushSnapshotFromClient#testRestoreSnapshot | up | first (the 1st restore, table disabled) | SnapshotManager, TableStateManager | 16 s | not run (budget 21600 s) |
| hbase-adhoc-08 | ClusterSchemaServiceImpl:111 | TestNamespaceAuditor#testTableOperations | up | first | ClusterSchemaServiceImpl, TableNamespaceManager | 13 s | HC12-08 UNSAT_CLOSED at FIXED_POINT, 774 s, **vacuous** (vacuity.py: fatal arm literal false; `nsd == null` over `TableNamespaceManager.cache.get` has no writer family). Likely class C: the client waits on the namespace insert before the read. Rerun on tree set hb-checks-trees-20; if still vacuous, record class C |
| hbase-adhoc-10 | AssignmentManager:765 | TestRegionMove#testDisableAndMove | up | first (`admin.unassign`) | AssignmentManager, RegionStateNode | 12 s | no result. R7-10 ended at its 4 h budget (RUN_DEFECT, identity drift since fixed); R17-10 stopped at EXPLORE round 35: 401 verdicts (36 ADMITTED, 281 NOT_ADMITTED -- 241 of them worker-side query refusals of seconds each --, 84 UNSAT); 210 of its 233 SAT flips were `HBASE_RPC` REQUEST faults (70 client calls x 3 kinds, ~10 min replays). Rerun on system/hbase >= 8da6eb24d (CallQueueTooBigException cut, fault replays queued last: 140 such replays) |
| hbase-adhoc-11 | AssignmentManager:769 | same | up | first (`admin.unassign`) | AssignmentManager, RegionStateNode | same run | no result. R9-11 MISSING (async continuation identity, fixed 7384c1e61); R14-11's seed matched both MoveRegion producers; R20-11 stopped at round 0. Rerun as 10 |
| hbase-adhoc-12 | AssignmentManager:772 | same | up | first (`admin.unassign`) | AssignmentManager, TableStateManager | same run | never run on the fixed tree. Run as 10 |
| hbase-adhoc-13 | MergeTableRegionsProcedure:499 | TestMergeTableRegionsProcedure#testMergeTwoRegions | up | first | MergeTableRegionsProcedure, RegionStateStore, client CatalogFamilyFormat | 14 s | HP9-13 UNSAT_CLOSED, 2957 s, **vacuous** (14/14 paths' fatal arm literal false): `hasMergeRegions` scans the hbase:meta row's cells, which reach the master through a region's store and a Get reply (no tracked cell; `Result`'s map is sorted: `ordered_map_unmodeled`); its race partner, CatalogJanitor's GC, is a chore that never comes due in automatic mode. Needs a store-data model and a workload that drives the janitor (TODO HBase 9) |
| hbase-adhoc-14 | MergeTableRegionsProcedure:503 | same | up | first | MergeTableRegionsProcedure, RegionStates | same run | HP10-14 MISSING at PREFLIGHT (317 s: the head on lift03 could not reach lift15 over batch ssh). Run with workers the head reaches; expect a bound by `ordered_map_unmodeled` (RegionStates' maps are ConcurrentSkipListMaps) |
| hbase-adhoc-15 | MergeTableRegionsProcedure:507 | same | up | first | MergeTableRegionsProcedure, RegionStates, RegionStateNode, AssignmentManager | same run | no result. HP7-15: 2 STATE_PAIRING_FLIPPED claims refused ORDER_UNHELD (the merge step was a QUEUED_TASK; tree 1dda23ecc5 makes steps HANDOFF_TASKs); HP8-15: FORMULA_SAT on the seed path from a free `unsupported__` leaf (`"OPEN".equals(state)` over an enum read stated at REF; fixed on hbase-reask, PIPELINE §8: offline on HP8-15's corpus the seed's phi is `false` and the claim is STATE_PAIRING_FLIPPED on path 62, RegionStateNode.state re-paired to OPENING plus one FAULT marker); HP9-15 stopped in EXPLORE (251 verdicts). Rerun on system/hbase + tree set 9 |
| hbase-adhoc-19 | ModifyTableProcedure:134 | TestModifyTableProcedure#testModifyWillNotReopenRegions | up | first (Test 1's modify) | ModifyTableProcedure, util/FSTableDescriptors | 11 s | not run (its guard is over `TreeMap.size`: expect `ordered_map_unmodeled`); a SEED-only run first |
| hbase-adhoc-20 | ModifyTableProcedure:138 | same | up | first (Test 1's modify) | ModifyTableProcedure, util/FSTableDescriptors | same run | not run (guard over a HashSet and an ArrayList); a SEED-only run first |
| hbase-adhoc-21 | NamespaceStateManager:130 | TestNamespaceAuditor#testRestoreSnapshot | up | first (the restore) | NamespaceStateManager, NamespaceTableAndRegionInfo | 15 s | HC11-21 MISSING: the restore is sent inside a `getProcedureResult` poll's reply callback, so its anchor is minted from the poll count (TODO HBase 8). Workaround 23ff06c9ba (`restoreSnapshot(name, false)`) is in trees >= 18; not rerun |
| hbase-adhoc-22 | NamespaceStateManager:168 | TestCausynthTruncatedTableQuota#createWhileATruncatedTableIsDeleted (ours) | up | `auto0/master0#epoch0/region/REGION.ebc27075-13a0-35bd-8787-ae2532aac65d#2`: the created table's check (the 1st is the truncated table's own creation; seed HC1SEED-22 observed exactly these 2) | NamespaceStateManager, NamespaceTableAndRegionInfo | 12-14 s, 3/3 | no result on the fixed CONFIRM. HC13-22 SAT_UNCONFIRMED, 3093 s: the right claim (the creation's read of `NamespaceTableAndRegionInfo.regionCount` 32#24 at v157 re-paired to the truncated table's `addTable` v93: 2 + 1 > 2 at :168) refused 4x by CONFIRM's moves-nothing shortcut (fixed a9aead2fa) and 5x "run published no target row at anchor 90c306fc" (unexplained: read `accept-HC13-22/.../final/refuted/000*`); HC20-22 stopped in COMPOSE (>10 min). Rerun with the full budget |
| hbase-adhoc-24 | ZKProcedureMemberRpcs:210 | TestFlushTableProcedureWithDoNotSupportFlushTableMaster#testFlushFallback | up | first | ZKProcedureMemberRpcs, ZKProcedureCoordinator | 37 s | no result. HZ17-24's seed replay stuck 40 min (the balancer chore moved regions 8 min in; fixed by tree f9340f2aab); HZ18-24 stopped in its seed replay. Rerun on tree >= f9340f2aab |
| hbase-adhoc-28 | HBaseServerBase:353 | TestInfoServers#testInfoServersRedirect | startup | first | HBaseServerBase, common util/Addressing | 9 s | **done: UNSAT, vacuous by construction (class C: a configuration constant decided in the JDK), no workaround** (NP4-28, `gc-out/hbase-platform/accept-NP4-28`, UNSAT_CLOSED at FIXED_POINT, 575 s; vacuity.py: 2 paths, fatal arm literal false, guard terms 0/2). `!Addressing.isLocalAddress(InetAddress.getByName(addr))` is decided inside the JDK (InetAddress, NetworkInterface natives) over `hbase.master.info.bindAddress`, which the workload never sets ("0.0.0.0"); the formula's only symbol is the CONFIG root `hbase.master.info.port` (`port >= 0`). A replay forced to the fatal arm threw (FORCED_TARGET), but only a non-local bind address takes it: a misconfiguration, not coordination |
| hbase-adhoc-31 | RSRpcServices:1880 (ServiceException) | TestRetainAssignmentOnRestart#testForceRetainAssignment | up | the restarted server's first (auto0/rs3) | RSRpcServices, master/procedure/RSProcedureDispatcher, master/assignment/RegionStateNode, RegionRemoteProcedureBase | 19 s | R10-31 (old workload TestRegionMove) UNSAT_CLOSED, vacuous by its workload: the start codes it compares are run constants. New workload above (5da09e03b), selector `auto0/rs3#epoch0/region/REGION.4a0683a9-728f-350d-b755-1212d91a2dc1#1` (the declared `throwOnWrongStartCode(long)` region folds into it); R21-31 passed SEED and PLAN, stopped at EXPLORE round 0. Rerun |
| hbase-adhoc-34 | AuthenticationTokenSecretManager:160 | TestCausynthTokenKeys#anotherServerValidatesTheKeyMastersToken (ours, owner 2026-10-19: no MiniKdc, no Kerberos; every server's token secret manager runs on a simple-authentication cluster, `RpcServer#CAUSYNTH_TOKEN_SECRETS`; the key master's token validated by the other server's manager, the identifier decoded from its bytes) | startup (the keys are made and distributed through ZooKeeper while the cluster starts: the key master's write and the other server's read of `/hbase/tokenauth/keys`) | first | AuthenticationTokenSecretManager, ZKSecretWatcher | 7.5 s | **PASS** (NZ3-34, `gc-out/hbase-zk/accept-NZ3-34`, snapshot hb2-zk-2 cf142b588, tree set hb-int-trees-2, depth 1, 1684 s): SAT MARKER_FLIPPED by the ZooKeeper READ door's `SessionExpired` on refreshKeys' getData of `/hbase/tokenauth/keys/1`, confirmed in the VM, reproduced natively 10/10, control 0/10. The workload removes the token's key from the other server's manager before `retrievePassword` (tree 5e7f0688a5: the key's watch event not yet processed), so `refreshKeys` runs in the target occurrence; NZ1-34 (that workload alone) and NZ2-34 (+ f6e07b3c9, the fetch of a declared read's receiver) stayed vacuous: no read door asked, then the asked door's fault roots in client0's root context never flipped (`client_fault_transports`), fixed by cf142b588. Earlier HZ14/15/18-34 vacuous (the key held from startup) |
| hbase-adhoc-35 | HBaseFsck:2742 (anonymous visitor) | TestHBaseFsckReplication#test | up | first | util/HBaseFsck, util/HbckRegionInfo | 9 s | **done: UNSAT, vacuous by construction (class C: corrupt meta), no workaround** (NP2-35, UNSAT_CLOSED at FIXED_POINT, `gc-out/hbase-platform/accept-NP2-35`, 1354 s; vacuity.py: 10 paths, guard terms 10/10, roots 0, reads offered 0/1). The guard `previous.getMetaEntry() == null` reads the `HbckRegionInfo` the scanning thread itself made; its meta entry's only other writer is the visitor on the same thread, so no world re-pairs it, and the 10 door faults the engine planted (connect's registry call, the meta location call, the hbck znode) kept the healthy arm. The throw needs two hbase:meta rows of one region in one scan (a corrupt meta; a re-sent Scan resumes after its last row) |
| hbase-adhoc-37 | MasterAddressTracker:206 | TestRSStatusPage#testStatusPage (expects `text/html`: the Java 8 tree serves the page without a charset) | up | first (the test's `getActiveMasterInfoPort`) | zookeeper MasterAddressTracker, master/ActiveMasterManager | 13 s | **UNSAT_CLOSED, vacuous** (HZ2-37, `gc-out/hbase-zk/accept-HZ2-37`, 502 s, 2 paths, no root; FSHLog tree; `tools/analysis/vacuity.py`: the fatal arm is literal false on both paths, the guard decided with no term). Reading: the guard's read is in the chain only as a store read -- the target occurrence's STORE_READ of `/hbase/master` v0 through `RecoverableZooKeeper#getData`, in the zk chain's path and keys, its writer (the active master's create) before the `up` window --, but `data == null` is decided over a concrete local: no symbol names whether the read found a node, so no world could flip it. A flip needs a read in an absent window (no master znode), which this workload never has and the store model cannot state. Not rerun: vacuous until a znode's absence is state (TODO HBase 10) |
| hbase-bugs-backup-lock-reply-lost | BackupSystemTable:504 | TestCausynthBackupLockReplyLost#takeAndReleaseTheBackupLock (ours: one client takes and releases the lock, exclusive-operation timeout 5 s; TestBackupManager's two workers reach :504 by contention in passing runs, and R4-bak's witness was a REQUEST fault that only delayed the first acquirer: confirmed, reproduced 3/10, control 5/10) | up | first (the only acquirer's first call) | BackupSystemTable, BackupManager (the chain is the HBASE_RPC reply door's fault and the client's retry, which the doors' families carry; HRegion and RawAsyncTableImpl dropped, owner 2026-10-19) | 2 s | **SAT MARKER_FLIPPED, confirmed, reproduced 10/10 (control 0/10), PASS, 551 s** (R5-bak, `gc-out/hbase-rpc/accept-R5-bak`): the `HBASE_RPC` RESPONSE door of the lock CAS's reply (`RpcConnection#finishCall`, on the client's event loop); expected mechanism a `RpcConnection` reply-door fault (experiments/accept/report.py) |
| hbase-bugs-ns-rsgroup-removal | MasterProcedureUtil:227 | TestCausynthNamespaceGroupRemoval#removeTheGroupOfANamespaceBeingCreated (ours) | up | `auto0/master0#epoch0/region/REGION.874dbcb2-c79c-38ee-bb4f-4dfdf62bd234#3`: CreateTableProcedure's second `checkGroupExists`, the group the table inherits from its namespace (seeds observed 3: the namespace's prepare, then the table's own group and the inherited one in one context; the region is the one of `checkGroupExists(RSGroupInfoManager, ..)` since the tree's workaround cabb055aad) | MasterProcedureUtil, rsgroup/RSGroupInfoManagerImpl, TableNamespaceManager, ClusterSchemaServiceImpl | 9 s (tree 985a0dfe91) | HC9 UNSAT_CLOSED (the holder's writers unplanned); HC14/HC15 SAT claims refuted by CONFIRM on ORDER and STATE edges of other chains (a CreateTable retry fault, the startup worker's flush): the removal's namespace check compared Strings in a TreeMap, which the engine cannot state. Tree 985a0dfe91 (STATUS Per-system surface): the check refuses on a per-group namespace count the insertion writes; the namespace's meta put makes one attempt and a failed insertion's retry waits for the workload's removal. A probe failing the first namespace put once removed the group and the table was refused at :227; natively the removal is refused (1 namespace) and the table for the group's emptiness. Next run on tree set hb-checks-trees-20 |
| hbase-bugs-master-active-time | MasterRpcServices:2629 | TestCausynthMasterActiveTime#reportOpenedToTheNextMaster (the tree's own: a master failover while a region opens; the region server reports OPENED with the old master's active time to the new master) | startup | `auto0/master1#epoch0/region/REGION.f3a7cc84-...#1` (the new master's first `reportRegionStateTransition`; `first` named the old master's first report) | MasterRpcServices, HMaster, OpenRegionProcedure, RegionRemoteProcedureBase, RSProcedureDispatcher, RemoteProcedureDispatcher, RSRpcServices, HRegionServer, AssignRegionHandler, RegionServerServices (widened 2026-10-19, HZ7: its nested PostOpenDeployContext and RegionStateTransitionContext carry the old master's active time from the region server's open handler to its OPENED report; outside the scope, their accessor reads were untracked, so the report's time lowered to its recorded constant though its read still named the handoff symbol), EnvironmentEdgeManager | 10 s | no result. HZ17-mat (5637 s): every claim FORMULA_SAT with no moved root, refuted: master0's activation clock T0 was unplaced (read only in re-runs, on another node than their other clock cells). Fixed by 208ac1899 (offline: 112 of 114 paths compose; claim 0 CLOCK_SKEW, T0 = T1 + 60001 ms). HZ18-mat stopped at EXPLORE round 25. Rerun; CONFIRM must plant T0 on master0's clock at its activation reading and deliver it on the OpenRegionRequest |

**HBASE-30483 in hbase-adhoc-22 (yes).** A table truncated without its splits keeps its old region count in the
master's namespace quota (`TruncateTableProcedure` never updates it; the fork's fix/truncate-namespace-region-quota
13f4fa2 sets it). For :168 the bug is a refusal by exactly the stale surplus, so the workload holds a creation that
fits only once something has released quota: a namespace of 2 regions, a 2-region table truncated to 1 (the quota
still counts 2), the table deleted asynchronously, then (after 2 s, not a wait on the deletion) a 1-region table
created; the deletion's release (`DeleteTableProcedure#postDelete` -> `NamespaceStateManager#removeTable`) lands
first and the creation fits (0 + 1 <= 2). The counterfactual is the creation's region-count read re-paired to before
that release, which no synchronization orders: 2 + 1 > 2 throws at :168, while under the fix the same order counts
1 + 1 <= 2. Natively, the same creation run before the deletion is refused with "not allowed to have 1 regions ...
current region count is 2" (cached 2 for 1 real region). A split cannot play the release's part: its own quota
check (`incr > 0 && regionCount >= max`) is stricter than :168's, so a recording in which both pass has no order in
which only :168 throws. Risk for the replay: the deletion's last step and the creation must run on different
procedure workers (16 by default).

**HBASE-30484 in hbase-adhoc-04 (yes; the owner's report, PR 8788).** The quota observer moves a table that a
DISABLE violation disabled out of violation by writing the new snapshot to hbase:quota, advancing its in-memory
snapshot, and only then enabling the table (`QuotaObserverChore#updateTableQuota`). The workload drives the real
observer twice, as two chore runs would (the master's own runs are pushed past the test), with a client that makes one
attempt per call (`hbase.client.retries.number` 0: the chore's retry is its next run): the first run moves the disabled
table out of violation and enables it, the second finds nothing to change, then the test flushes the table. One lost
EnableTable request (an `HBASE_RPC` fault, world depth 0) is the bug: the second run skips the enable, the table stays
disabled and the flush is refused at :163 (a probe client that fails the first enable observed exactly that). The
fork's fix/quota-enable-retry-after-snapshot-advance (07a45a0) advances the snapshot only after the enable, so its
next run enables the table.

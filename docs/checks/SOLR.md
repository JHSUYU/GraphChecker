<!-- Moved into the repo at the 2026-10-05 handover from /bigtemp/vnr3ne/analysis/study-2026-10-04/solr.md (investigator tables of 2026-10-04, read against our trees). Ids never move. Live status per check: docs/checks/README.md and docs/handover/STATE.md. -->
# Solr: study.txt items, bug_study bugs, picks (investigator, 2026-10-04)

Tree read: `/bigtemp/vnr3ne/wt/lucene-solr-bugs` (`gc/solr-bugs` f65aaf7, version 8.11.5-SNAPSHOT; same line as
`lucene-solr-storing`). Line numbers below are OUR tree's. Files the adapter touched are shifted against 8.11.4
(IndexDeletionPolicyWrapper +2, DistributedZkUpdateProcessor +2..+6, ZkStateReader +22, ReplicationHandler +2);
the other study files match 8.11.4 line for line.

Facts about our Solr reach that decide many rows:
- FAULT doors: `SOLR_HTTP`/`SOLR_HTTP2` REQUEST and RESPONSE (HttpSolrClient#executeMethod, Http2SolrClient#request)
  and `ZOOKEEPER` WRITE (ZooKeeper#create/setData/delete/multi; Solr HOOK rows in SolrZkClient#create/setData/multi).
  A ZooKeeper write fault is "the write committed, the caller sees the failure". There is NO door on ZooKeeper reads
  (getData/exists/getChildren): every bug_study bug triggered by a watcher READ fault is out of reach.
- Every node keeps cached views in ZkStateReader fields (clusterState / watchedCollectionStates, `AliasesManager.aliases`,
  `clusterProperties`, liveNodes): a STATE re-pairing of such a read (INITIAL or an older watcher write) is our
  stale-view counterfactual. A collection with no local core is a `LazyCollectionRef` whose cache is a CLOCK guard
  (`ZkStateReader.java:823`, `System.nanoTime() - lastUpdateTime > LAZY_CACHE_TIME`, 2 s): a CLOCK skew there is the
  other stale-view counterfactual (Overseer-side and request-side reads of collections the node does not host).
- `experiments/solr/system.sh` builds workloads from `solr/core` tests only (module, report, test_classes are
  solr-core's). Items whose named test lives in `solr/solrj/src/test` need that file to also accept the solrj test
  module (small, general) or a core-module equivalent (given).
- Throws that are not `throw new` at the line: asserts (rewrite to `if (!(c)) throw new @CausynthExceptionTarget("id")
  AssertionError(..)`), `throw ex` (SOLR-29), and `throw RoutedAlias.newAliasMustExistException(..)` (SOLR-39/40: the
  factory itself throws at `RoutedAlias.java:72`, shared by three callers incl. `TimeRoutedAlias.java:326`, so each
  site needs its own inline `throw new @CausynthExceptionTarget(..) SolrException(SERVICE_UNAVAILABLE, ..)`).

## A. study.txt items (all 40)

C = core `solr/core/src/java/org/apache/solr/`, J = solrj `solr/solrj/src/java/org/apache/solr/`.

| id | our file:line | kind | guard (one line) | coordination? | counterfactual that could flip it | IO ok? | test in our tree | fit |
|---|---|---|---|---|---|---|---|---|
| 01 | J client/solrj/impl/BaseHttpClusterStateProvider.java:267 | throw | every live node's LISTALIASES fetch failed after cache expiry | N: client retry exhaustion | CLOCK (5 s cache) + FAULT on every node's fetch; the throw is the faults' echo | ok | none (NO_PATH) | C, dropped: no test |
| 02 | same:180 | throw | `liveNodes == null` | N | none: every writer stores a new HashSet (:66,:144,:191); `init` runs in the constructor and throws otherwise; INITIAL is a constructor write | ok | CloudHttp2SolrClientTest#testParallelUpdateQTime (solrj) | DROPPED: failure branch unreachable |
| 03 | same:198 | throw | after expiry, every node's live_nodes fetch failed | N | CLOCK + FAULT x n (echo) | ok | none | C, dropped: no test |
| 04 | same:75 | throw | live nodes null/empty after trying each given URL | N (echo of the fetch failure) | FAULT at the one CLUSTERSTATUS fetch (test gives one URL) | ok | HttpClusterStateSSLTest#testHttpClusterStateWithSSL (solrj) | C |
| 05 | C cloud/ZkController.java:1274 | throw | replica gone from the node's state right after `waitForState` saw it | Y: node's watched state vs Overseer DELETEREPLICA | none in the test: the re-read follows the predicate that saw the replica (an older-version re-pairing deadlocks the wait, CONFIRM refutes); real trigger is a concurrent DELETEREPLICA (DeleteReplicaTest#raceConditionOnDeleteAndRegisterReplica takes it on purpose via a hook) | ok | AddReplicaTest#testAddMultipleReplicas | C |
| 06 | same:1315 | assert | not (leaderUrl == ourUrl and PULL) | weak: leader znode vs local type | none: no writer publishes a PULL replica as leader | ok | same | C |
| 07 | same:1326 | throw | `cc.getCore(name) == null` during register | Y: core map vs concurrent UNLOAD | none in the test (putCore precedes register in the same thread) | ok | same | C |
| 08 | same:1859 | throw | 320 x 1 s without a shard id | N (count loop) | none | ok | none | dropped: no test |
| 09 | C cloud/api/collections/DeleteReplicaCmd.java:278 | throw | `!callable.call()`: `waitForCoreNodeGone` false twice | Y: Overseer waits for the node's unregister / its own DELETECORE in its view | one FAULT on UNLOAD still returns TRUE after `deleteCoreNode`; a fault on the DELETECORE offer lands at :281; :278 needs two 30 s latch timeouts (timed wait, no clock read) | ok | DeleteReplicaTest#deleteReplicaAndVerifyDirectoryCleanup | C |
| 10 | C cloud/api/collections/MaintainRoutedAliasCmd.java:117 | throw | `RoutedAlias.fromProps(props) == null` with non-empty props | Y: Overseer alias view vs data node | none: no aliases.json version has props without router.*; a stale/INITIAL view lands at :112 (BAD_REQUEST) | ok | TimeRoutedAliasUpdateProcessorTest#test | C |
| 11 | same:160 | throw | switch default over the Action enum | N | none (all values handled) | ok | none | dropped: unreachable default |
| 12 | C cloud/api/collections/OverseerCollectionMessageHandler.java:570 | throw | 320 x 1 s without coreNodeName | N | none | ok | none | dropped: no test |
| 13 | C cloud/api/collections/RoutedAlias.java:350 | throw | after MAINTAINROUTEDALIAS + `aliasesManager.update()` the alias list lacks the new collection | Y: data node's alias view vs Overseer's alias write | Overseer-side FAULTs make `remoteInvoke` throw first (MaintainRoutedAliasCmd:68, rethrown RoutedAlias:406); a stale read after `sync()`+getData is infeasible (`setIfNewer` synchronized, monotone); needs a concurrent MAINTAIN | ok | TimeRoutedAliasUpdateProcessorTest#testPreemptiveCreation | C |
| 14 | C cloud/api/collections/SplitShardCmd.java:167 | throw | `exists(live_nodes/<leader node>) == null` | Y: Overseer's leader view vs the live-node session | none: needs the leader node's session gone; `exists` has no door; a CLOCK-stale lazy view yields an older leader that is still live | ok | SplitShardTest#doTest | C |
| 15 | same:538 | throw | second probe: leader live node gone | Y | session loss only | ok | none named; SplitShardTest#doTest evaluates the enclosing predicate (:521) | optional, C |
| 16 | same:543 | throw | second probe: ephemeralOwner changed | Y | session change only | ok | same | optional, C |
| 17 | C cloud/api/collections/TimeRoutedAlias.java:579 | assert | debug-only ordering assert in `calcDeletes` | N | none | ok | none | dropped: no test |
| 18 | J common/cloud/ZkStateReader.java:2369 | assert | same ZK version implies same alias JSON | Y: local alias cache vs ZK | none: `setIfNewer` is synchronized and both copies come from one znode version | ok | AliasIntegrationTest#testModifyPropertiesV2 | C |
| 19 | C core/CoreContainer.java:1330 | throw | node says non-legacy (`legacyCloud` != "true") and the CREATE carries no coreNodeName (Overseer said legacy) | **Y: Overseer's clusterprops view vs the core node's view** | STATE re-pairing: the core node's `ZkStateReader.clusterProperties` read (J ZkStateReader.java:1126) to its INITIAL/older map, i.e. its watcher has not yet applied `legacyCloud=true` | ok | AddReplicaTest#testAddMultipleReplicas never sets legacyCloud (no writer to re-pair); use DeleteReplicaTest#deleteReplicaFromClusterStateLegacy (4 nodes, CLUSTERPROP legacyCloud=true then CREATE 1x3) | B (A- with that workload) |
| 20 | C core/CoreContainer.java:1559 | throw | corrupt-index fallthrough | N | index corruption (disk) | IO no | none | dropped |
| 21 | same:1765 | assert | this core's replica present in docCollection on reload | Y: node state vs replica delete | none in the test (register already waited for the replica; a concurrent delete is needed) | ok | CollectionReloadTest#testReloadedLeaderStateAfterZkSessionLoss | C |
| 22 | C core/IndexDeletionPolicyWrapper.java:179 | throw | requested generation deleted / older than latest | Y: follower's filelist generation vs leader's commits and reservation clock | CLOCK = **solr-18406** | ok | TestPullReplica#testAddDocs (study); our case TestCausynthPullReplicaReservation#pullReplicaFetchesAcrossALeaderCommit | A (PASS) |
| 23 | same:488 | assert | `latestCommit == last of list` | N: local invariant under `synchronized` | none | ok | CloudHttp2SolrClientTest#testAliasHandling (solrj); core: TestPullReplica#testAddDocs | C |
| 24 | C core/ZkContainer.java:128 | throw | zkHost chroot exists | N: startup config | none (string config) | ok | HttpClusterStateSSLTest#testHttpClusterStateWithSSL (solrj); runs at node start, before the window | C |
| 25 | same:157 | throw | bootstrap_confdir with chroot | N | none | ok | none (single CoreContainer test) | dropped |
| 26 | C handler/ReplicationHandler.java:681 | assert | `null != commit` | N | none: both null cases return just above | ok | TestPullReplica#testAddDocs | DROPPED: unreachable |
| 27 | C handler/admin/CollectionsHandler.java:1134 | throw | BACKUP location exists in the repository | N: operator input | none | IO no | TestLocalFSCloudBackupRestore#test | C |
| 28 | same:1183 | throw | RESTORE location exists | N | none | IO no | same | C |
| 29 | same:681 | `throw ex` | CREATEALIAS routed-alias params failed to parse | N: request validation | none | ok | TimeRoutedAliasUpdateProcessorTest#test | C |
| 30 | same:685 | assert | `routedAlias != null` | N: invalid input (no collections, no router params) | none | ok | same | C |
| 31 | same:1477 | throw | FORCELEADER refused: slice leader ACTIVE in this node's view | Y: receiving node's state view vs the dead leader | CLOCK on the receiving node's lazy cache (stale DocCollection with the killed leader ACTIVE) or STATE re-pairing of its watched DocCollection | ok | ForceLeaderTest#testReplicasInLowerTerms (@Nightly; base AbstractFullDistribZkTestBase, not MiniSolrCloudCluster: adapter hooks need extending) | B- |
| 32 | C handler/admin/ConfigSetsHandler.java:486 | throw | unauthenticated create from a trusted base | N: auth | none | ok | TestConfigSetsAPI#testCreateWithTrust (throw already taken in the run) | C |
| 33 | C servlet/CoordinatorHttpSolrCall.java:140 | throw | rethrow of the create exception | N: echo | FAULT echo | ok | none | dropped |
| 34 | same:142 | throw | synthetic collection absent after a successful createColl | Y: coordinator view vs Overseer create | none: the local CREATE waits for active on the same reader; needs a concurrent delete | ok | TestCoordinatorRole#testSimple evaluates it (re-audit) | optional, C |
| 35 | C update/processor/DistributedZkUpdateProcessor.java:633 | assert | `TestInjection.injectFailReplicaRequests()` | N: test hook | none (static String injection) | ok | TimeRoutedAliasUpdateProcessorTest#test | C |
| 36 | same:995 | throw | sub-shard leader gets FROMLEADER + DISTRIB_FROM_PARENT while its slice is ACTIVE | Y: parent leader's view of sub-shard state vs sub-shard leader's | STATE re-pairing of the parent leader's DocCollection read to the version with the sub-shard still RECOVERY | ok | none named; SplitShardTest#testLiveSplit (unbounded indexing threads; a bounded variant is better) | optional, B |
| 37 | same:1003 | throw | sub-shard range not inside parent range | weak | none (ranges fixed at split) | ok | same | optional, C |
| 38 | same:1031 | throw | cluster state says we lead, `cloudDesc.isLeader()` still false after 5 x 500 ms | **Y: Overseer-published leader (the LEADER message carries ACTIVE, ShardLeaderElectionContextBase.java:178) vs the local election flag (set after it, ShardLeaderElectionContext.java:264)** | STATE re-pairing / ORDER: the `isLeader` reads paired with the field's initial false, `setLeader(true)` held until the update's occurrence closes | ok | CloudHttp2SolrClientTest#testAliasHandling (solrj); core: TestPullReplica#testAddDocs (1 NRT leader; with 2+ NRT the follower's PREPRECOVERY orders `setLeader` first) | B |
| 39 | C update/processor/RoutedAliasUpdateProcessor.java:247 (thrown at RoutedAlias.java:72) | throw | node's alias view lacks the alias on a commit | **Y: collection's routedAliasName vs the node's alias cache** | STATE re-pairing of `AliasesManager.aliases` (node not the Overseer's) to INITIAL/older | ok | TimeRoutedAliasUpdateProcessorTest#test | B |
| 40 | same:133 (thrown at RoutedAlias.java:72, rewrapped :123) | throw | same at processor creation | **Y** (same parties; bug_study #21 and #38 hit this exact guard) | same; in `test()` col23rd carries routedAliasName before the alias exists, so the INITIAL arm is realistic | ok | same | B+ |

## B. bug_study bugs not covered by README §0.3 (Solr #16-#60)

bug_study is Solr 11 main; "present" = the faulty logic and the fatal throw exist in our 8.11 tree.

| bug | present in our tree (fatal) | coord.? | single counterfactual | chain in memory? | cluster test | fit | study site? |
|---|---|---|---|---|---|---|---|
| 16 snapshot all-DOWN false success | yes: CreateSnapshotCmd.java:104 skip, :181 Successful; fatal BackupCmd.java:207 | Y: Overseer's replica-state view vs cores | CLOCK on the Overseer's lazy cache or STATE re-pairing of its DocCollection read (replicas still DOWN/RECOVERING) | yes; crosses snapshot-metadata JSON in ZK | TestSolrCloudSnapshots#testSnapshots reaches it but asserts the replica count between snapshot and backup: self-written needed | **B, added** | no |
| 17 MIGRATE buffer leak | yes: MigrateCmd.java:187 buffers, no compensation; fatal CoreAdminOperation.java:186 | Y: Overseer command flow vs target core's UpdateLog state | FAULT at any door after the buffer step (ADDROUTINGRULE offer ZK write :197, SPLIT/CREATE/REQUESTAPPLYUPDATES HTTP :292-369) | yes: `UpdateLog.state` field | no test migrates twice into one target: self-written (extend TestCausynthMigrateRuleTarget) | **A-, added** | no |
| 18 split parent-session read fault | yes (ReplicaMutator) | Y | ZK READ fault | - | - | C: no read door | no |
| 19 backup during split final switch | yes | Y | two-command interleaving | no: backup files | - | C: IO | no |
| 20 TRA start overwrites a newer alias | yes: TimeRoutedAlias.java:386-387 (closure ignores `a`) | Y: captured alias snapshot vs concurrent CREATEALIAS, CAS on current version | STATE re-pairing of the ADD thread's snapshot read (`zkStateReader.getAliases()`, :377) to the version before B | yes but crosses aliases.json key presence to the client | testDateMathInStart is @AwaitsFix: self-written | **B-, added** | no |
| 21 DELETEALIAS keeps routedAliasName | yes: same guard as SOLR-40 | Y | deterministic sequence (no flip) | yes | - | C: deterministic; strengthens SOLR-40 | **SOLR-40** |
| 22 CREATE alias publish fails | yes | Y | needs an uncommitted ZK write; our write fault commits | - | - | C | no |
| 23 REINDEX worker dies with Error | yes | Y | needs an Error; a door fault takes `catch (Exception)` -> cleanup (#04's path) | - | - | C | no |
| 24 REINDEX stopped daemon | yes | Y | operator `/stream?action=stop` | - | - | C | no |
| 25 snapshot delete loses failed core | partly | Y | two faults; core snapshot metadata on disk | no | - | C | no |
| 26 RESTORE retry leaves CONSTRUCTION | yes: only the new-collection path marks ACTIVE (RestoreCmd.java:285); fatal J HashBasedRouter.java:67 | Y (aborted command's leftover vs the retry's assumption, like #04) | FAULT at the RESTORECORE / apply-buffer HTTP door (RestoreCmd.java:282-284) | yes (backup files read identically in both worlds) | self-written (backup, restore, restore again, add) | **B-, added** | no |
| 27-31 filestore (ack/delete/lock/put retry/short overwrite) | filestore exists in 8.11 | Y | disk state, read faults, operator stop | no | - | C: IO rule | no |
| 32 CREATESHARD EMPTY | n/a | N | deterministic | - | - | C | no |
| 33 package watch lost | yes | Y | 11 ZK read faults | - | - | C | no |
| 34 configset partial create + concurrent CREATE | partly | Y | fault + concurrent command | - | - | C: two events | no |
| 35 concurrent package ADD | partly | Y | three-party schedule; package infra (signed jar) | - | - | C | no |
| 36 security late NodeDeleted event | yes | Y | watcher callback delayed across delete+recreate | - | - | C | no |
| 37 UNLOAD term-write fault ghost | yes | Y | ZK write fault commits (term removed); fatal is a 404 with no `throw new` | - | - | C | no |
| 38 collectionprops version reset | yes | Y | callback delayed across delete+recreate+prop | - | - | C; same guard as SOLR-40 | **SOLR-40** |
| 39 ADDREPLICA term-write failure | yes | Y | ZK write fault; the retry guard also fires in a fault-free retry; no clean production fatal | - | - | C | no |
| 40 configset zip partial upload | partly | Y | ZK write fault; chain is a missing znode (not symbolic); overwrite=true repairs | no | - | C | no |
| 41 PRS ActiveReplicaWatcher | partly | Y | latch timeout only | - | - | C | no |
| 42 package version load failure | yes | Y | local file read IOException | no | - | C | no |
| 43 watched collection recreate | yes | Y | callback delayed across delete+recreate | - | - | C | no |
| 44 RESTORE second replica create fail | yes | Y | fault, then 30 s timeout + NPE path, backup IO | no | - | C | no |
| 45, 49 distributed collection API | absent (Solr 9) | - | - | - | - | C: absent | no |
| 46 core.properties write failure | yes | Y | disk write fault | no | - | C | no |
| 47, 51, 54, 60 watcher read loss | yes | Y | ZK READ fault | - | - | C: no read door | no |
| 48 PRS disable | n/a | N | deterministic | - | - | C | no |
| 50 Overseer running-map fault leaks lock | yes: OverseerTaskProcessor.java:313-325 unlocks only on NodeExists/Interrupted; outer catch :335 keeps the LockTree lock and `runningTasks` | Y: Overseer in-memory lock/running set vs ZK running map | ZK WRITE fault at `runningMap.put` (:492, DistributedMap.put -> makePath create) of an async task | yes | self-written (readOnly=true, async readOnly=false, add) | **B, added** | no |
| 52 async snapshot key-path mismatch | partly | weak | HTTP fault; the throw is the count-bounded poll after it (echo-like) | yes | - | C | no |
| 53 DELETESTATUS clear fault | yes | Y | needs an uncommitted ZK delete | - | - | C | no |
| 55 DELETENODE co-located replicas | likely | N | deterministic placement | - | - | C | no |
| 56 PULL reload bad interval | yes | N | invalid config upload | - | - | C | no |
| 57 CREATE EMPTY skips alias | yes | N | deterministic | - | - | C | no |
| 58 overlay child written, parent touch fails | yes | Y | our write fault commits the touch, so no divergence | - | - | C | no |
| 59 conf watcher drops event under lock | yes | Y | thread schedule on a ReentrantLock | - | - | C | no |

## C. Known cases mapped to study items

| case | throw (our tree) | study item |
|---|---|---|
| solr-18406 | IndexDeletionPolicyWrapper.java:179 (`getAndSaveCommitPoint`, 8.11.4 :177) | **SOLR-22**, the same throw (SOLR-26 is a different, dead assert in the same test path) |
| solr-18413 | DistributedZkUpdateProcessor.java:934 (route-rule target lookup) | none (the study lists :631/987/995/1025 of that file, not this one) |
| solr-bugs-reindex-cleanup | DeleteCollectionCmd.java:246 (`checkAliasReference`) | none |

## D. Pick list

### D.1 Every study item with a cluster test (owner ruling 2026-10-04)

Kept: the 24 TESTED items below. Dropped for a hard reason: SOLR-02 and SOLR-26 (failure branch unreachable in our
tree, see A). NO_PATH/UNCERTAIN with no test stay out (01, 03, 08, 11, 12, 17, 20, 25, 33). Fit is information only.
Marker: "inline" = put `@CausynthExceptionTarget("<id>")` on the existing `throw new` (fully qualified where the file
imports none, so no line moves). The 12 checked points (05 07 09 10 13 14 19 21 31 38 39 40) and the six bug checks of
D.2 are marked on `gc/solr-checks`; 22 is solr-18406's marker.

| case id | our site | tree change | workload (our tree) | counterfactual / chain | start scope | fit |
|---|---|---|---|---|---|---|
| solr-adhoc-04 | J BaseHttpClusterStateProvider.java:75 | inline | HttpClusterStateSSLTest#testHttpClusterStateWithSSL (solrj module) | FAULT at the CLUSTERSTATUS fetch -> liveNodes null -> throw (echo) | J impl/BaseHttpClusterStateProvider, impl/Http2SolrClient | C |
| solr-adhoc-05 | C ZkController.java:1274 | inline | AddReplicaTest#testAddMultipleReplicas | stale re-read of the watched state; expected refuted | C cloud/ZkController, core/ZkContainer; J common/cloud/ZkStateReader | C |
| solr-adhoc-06 | C ZkController.java:1315 | assert rewrite | same | none known | C cloud/ZkController, cloud/ShardLeaderElectionContext | C |
| solr-adhoc-07 | C ZkController.java:1326 | inline | same | core-map re-pairing; HB-ordered in the test | C cloud/ZkController, core/CoreContainer, core/SolrCores | C |
| solr-adhoc-09 | C DeleteReplicaCmd.java:278 | inline | DeleteReplicaTest#deleteReplicaAndVerifyDirectoryCleanup | UNLOAD fault -> 30 s wait -> deleteCoreNode; :278 needs a second timeout | C cloud/api/collections/DeleteReplicaCmd, OverseerCollectionMessageHandler; J ZkStateReader | C |
| solr-adhoc-10 | C MaintainRoutedAliasCmd.java:117 | inline | TimeRoutedAliasUpdateProcessorTest#test | none known (stale view hits :112) | C cloud/api/collections/MaintainRoutedAliasCmd, RoutedAlias; J common/cloud/Aliases | C |
| solr-adhoc-13 | C RoutedAlias.java:350 | inline | TimeRoutedAliasUpdateProcessorTest#testPreemptiveCreation | stale alias read after update(); expected refuted | C cloud/api/collections/RoutedAlias, MaintainRoutedAliasCmd; J ZkStateReader, Aliases | C |
| solr-adhoc-14 | C SplitShardCmd.java:167 | inline | SplitShardTest#doTest | none (needs session loss) | C cloud/api/collections/SplitShardCmd | C |
| solr-adhoc-18 | J ZkStateReader.java:2369 | assert rewrite | AliasIntegrationTest#testModifyPropertiesV2 | none (synchronized, same version) | J common/cloud/ZkStateReader, Aliases | C |
| **solr-adhoc-19** | C CoreContainer.java:1330 | inline | named AddReplicaTest#testAddMultipleReplicas; **use DeleteReplicaTest#deleteReplicaFromClusterStateLegacy** | STATE INITIAL re-pairing of the core node's `clusterProperties` read: Overseer sees legacyCloud=true and sends CREATE with no coreNodeName (CreateCollectionCmd.java:332, no :361); the core node's stale view says non-legacy -> `coreNodeName == null` -> throw | C core/CoreContainer, cloud/Overseer, cloud/api/collections/CreateCollectionCmd; J ZkStateReader | B (A-) |
| solr-adhoc-21 | C CoreContainer.java:1765 | assert rewrite | CollectionReloadTest#testReloadedLeaderStateAfterZkSessionLoss | stale view; HB-ordered by register | C core/CoreContainer; J ZkStateReader | C |
| solr-adhoc-22 | C IndexDeletionPolicyWrapper.java:179 | already marked `solr-18406` | = regression case solr-18406 (do not duplicate) | CLOCK, PASS | case's scope | A |
| solr-adhoc-23 | C IndexDeletionPolicyWrapper.java:488 | assert rewrite (multi-line 488-489) | CloudHttp2SolrClientTest#testAliasHandling (solrj); core: TestPullReplica#testAddDocs | none (local invariant) | C core/IndexDeletionPolicyWrapper | C |
| solr-adhoc-24 | C ZkContainer.java:128 | inline | HttpClusterStateSSLTest#testHttpClusterStateWithSSL (solrj); needs `recording_window=startup` | none (string config) | C core/ZkContainer, cloud/ZkController | C |
| solr-adhoc-27 | C CollectionsHandler.java:1134 | inline | TestLocalFSCloudBackupRestore#test | none (FS location) | C handler/admin/CollectionsHandler | C |
| solr-adhoc-28 | C CollectionsHandler.java:1183 | inline | same | none | same | C |
| solr-adhoc-29 | C CollectionsHandler.java:681 | `throw ex` -> `throw new @..("solr-adhoc-29") SolrException(ex.code(), ex.getMessage(), ex)` | TimeRoutedAliasUpdateProcessorTest#test | none (validation) | C handler/admin/CollectionsHandler, cloud/api/collections/RoutedAlias | C |
| solr-adhoc-30 | C CollectionsHandler.java:685 | assert rewrite | same | none (invalid input) | same | C |
| solr-adhoc-31 | C CollectionsHandler.java:1477 | inline | ForceLeaderTest#testReplicasInLowerTerms (not `@Nightly` in our tree; an AbstractFullDistribZkTestBase test: the base class registers its servers and opens the window, `CausynthSolrCluster#registerServers`) | CLOCK on the receiving node's LazyCollectionRef (ZkStateReader.java:823) or re-pairing of its DocCollection: stale view shows the killed leader ACTIVE -> refusal | C handler/admin/CollectionsHandler; J ZkStateReader, Slice, Replica | B- |
| solr-adhoc-32 | C ConfigSetsHandler.java:486 | inline | TestConfigSetsAPI#testCreateWithTrust (throw is taken in the run: target an untaken occurrence) | none (auth) | C handler/admin/ConfigSetsHandler | C |
| solr-adhoc-35 | C DistributedZkUpdateProcessor.java:633 | assert rewrite | TimeRoutedAliasUpdateProcessorTest#test | none (test hook) | C update/processor/DistributedZkUpdateProcessor | C |
| **solr-adhoc-38** | C DistributedZkUpdateProcessor.java:1031 | inline | named CloudHttp2SolrClientTest#testAliasHandling (solrj); **core: TestPullReplica#testAddDocs** | ORDER/re-pairing of `CloudDescriptor.isLeader` (volatile, initial false) on the leader's update thread: Overseer applied LEADER (state ACTIVE) before the election thread's `setLeader(true)`; held across the 5 x 500 ms loop -> throw | C update/processor/DistributedZkUpdateProcessor, cloud/CloudDescriptor, cloud/ShardLeaderElectionContext(Base) | B |
| **solr-adhoc-39** | C RoutedAliasUpdateProcessor.java:247 | inline `throw new @..("solr-adhoc-39") SolrException(SERVICE_UNAVAILABLE, ..)` in place of the factory call | TimeRoutedAliasUpdateProcessorTest#test | STATE re-pairing of the node's `AliasesManager.aliases` read to INITIAL/older on the commit path (`solrClient.commit(alias)`), core's routedAliasName recorded | C update/processor/RoutedAliasUpdateProcessor, cloud/api/collections/RoutedAlias; J ZkStateReader, Aliases | B |
| **solr-adhoc-40** | C RoutedAliasUpdateProcessor.java:133 | same inline rewrite (the factory throw at RoutedAlias.java:72 is shared) | TimeRoutedAliasUpdateProcessorTest#test | same re-pairing at processor creation: col23rd's routedAliasName says "alias", the node (4-node cluster, not the Overseer's) still holds INITIAL aliases -> empty props -> throw | same | B+ |

Optional, beyond the TESTED set (a test evaluating the guard was found on re-audit; add only if wanted):
solr-adhoc-36 (DZUP:995, SplitShardTest#testLiveSplit or a bounded live-split variant; parent-leader stale
DocCollection re-pairing; B), solr-adhoc-15/16 (SplitShardCmd:538/:543, SplitShardTest#doTest; session change only; C),
solr-adhoc-34 (CoordinatorHttpSolrCall:142, TestCoordinatorRole#testSimple; C), solr-adhoc-37 (DZUP:1003; C).

### D.2 bug_study additions (all criteria checked against our tree)

1. **solr-bugs-migrate-buffer-leak** (#17). Target `CoreAdminOperation.java:186` (REQUESTBUFFERUPDATES "Core .. not in
   active state", inline; the second MIGRATE's buffer request, a selector). Workload `TestCausynthMigrateBufferLeak#
   twoMigratesIntoOneTarget`: S on node0, T on node1, MIGRATE `a!` S->T, then MIGRATE `b!` S->T, both synchronous, each
   failure returned rather than thrown, no check between. Counterfactual: FAULT on the first MIGRATE after the buffer step
   (ADDROUTINGRULE offer ZK write, or SPLIT/temp CREATE/REQUESTAPPLYUPDATES HTTP request). Chain: T's `UpdateLog.state` =
   BUFFERING (bufferUpdates) never returned to ACTIVE (apply request never sent; MigrateCmd has no finally) -> second
   MIGRATE's buffer request reads BUFFERING -> throw. Hard to recover: T buffers forwarded updates (invisible) and refuses
   every later MIGRATE until a reload/restart. Scope: MigrateCmd, CoreAdminOperation, UpdateLog,
   OverseerCollectionMessageHandler. A-.
2. **solr-bugs-overseer-lock-leak** (#50). Target `DistributedZkUpdateProcessor.java:238` (8.11.4 :236; processAdd "is
   read-only", inline; the window's first add). Workload `TestCausynthOverseerLockLeak#addAfterAnAsyncReadOnlyOff`: CREATE
   C; MODIFYCOLLECTION readOnly=true; async MODIFYCOLLECTION readOnly="" (removal) under a fixed request id; at most 30
   REQUESTSTATUS polls 1 s apart, no assert; ADD. Counterfactual: ZK WRITE fault, a ConnectionLoss past
   `ZkCmdExecutor`'s retries (the write committed, the connection flapping, the session alive) at `runningMap.put`
   (OverseerTaskProcessor.java:492, `DistributedMap.put` -> `SolrZkClient#makePath` -> `create`, whose door stands where
   its retries return; `makepath-create-tree.patch`). Chain: KeeperException escapes
   `markTaskAsRunning` (only NodeExists/Interrupted unlock, :316-325) -> outer catch :335 keeps the LockTree lock and
   `runningTasks` -> the task is never dispatched again, its Runner never runs -> readOnly stays true -> add throws.
   The leak's only throw of its own, a later sync command's wait timeout (CollectionsHandler.java:383), never comes in an
   automatic cluster (`DEFAULT_COLLECTION_OP_TIMEOUT` = `CausynthBounds.NEVER_MS`): the target is the effect the task
   never applied, after a wait bounded by a count. Hard to recover: every later command on C blocks until the Overseer
   changes. Scope: OverseerTaskProcessor, LockTree, DistributedMap, OverseerCollectionMessageHandler,
   DistributedZkUpdateProcessor, SolrZkClient. B.
3. **solr-bugs-snapshot-no-active** (#16). Target `BackupCmd.java:207` ("Unable to find any live replica with a snapshot
   named", inline). The report's zero-request case (every replica of a shard skipped) never reaches it: BACKUP skips a
   shard the snapshot holds no replica of (:331-336, a warning; the backup silently lacks the shard, and the next failure
   is a RESTORE's read of the missing files, IO). :207 needs a shard the snapshot holds whose holders are all down or
   gone. Workload `TestCausynthSnapshotBackup#backupFromASnapshotAfterItsLeaderIsGone`: CREATE C 1 shard x 2 replicas,
   index, commit, CREATESNAPSHOT M, DELETEREPLICA the leader R1 (wait until it is gone and R2 leads), BACKUP commitName=M
   incremental=false (the path that reads M). Natively R2 was ACTIVE at CREATESNAPSHOT, so M holds both and the backup
   reads R2's. Counterfactual: the Overseer's view at CreateSnapshotCmd.java:102 shows R2 not ACTIVE yet (STATE
   re-pairing of its DocCollection read; CLOCK on a lazy reference where the Overseer hosts no replica) -> R2 skipped ->
   M = {R1}, recorded Successful (:176) -> R1 deleted -> :207. Risk: the list shape crosses snapshot-metadata JSON. Scope:
   CreateSnapshotCmd, BackupCmd, SolrSnapshotManager, CollectionSnapshotMetaData, ZkStateReader. B.
4. **solr-bugs-tra-start-overwrite** (#20). Target solrj `BaseCloudSolrClient.java:901` ("Collection not found: B" in
   `requestWithRetryOnStaleState`, inline; the same message at :1140 in `sendRequest` comes after it, `CloudSolrClient`
   has none; a selector: every client request passes it). Workload `TestCausynthTraStartAlias#
   requestViaAnAliasCreatedBeforeTheFirstDocument`: D on the Overseer's node; a TRA whose start `2019-09-14T03:00:00Z/DAY`
   is date math on a fixed day (the same collections every run), its collection on the other node; CREATEALIAS B->D; the
   TRA's first ADD (rewrites the start); at most 30 polls of the client's own alias view for the parsed start; a query via
   B. Counterfactual: STATE re-pairing of the routing node's `getAliases()` capture (TimeRoutedAlias.java:377) to the
   version before B: CreateAliasCmd only sleeps 100 ms for the nodes' watchers, so nothing orders B into the routing
   node's view before the capture; the async task (:386) writes the captured map over B's version -> B lost. The
   workload never reads the routing node's view (that read would order B first), and the TRA's collection is off the
   Overseer's node (the Overseer applies its own alias writes to its view as it makes them). Risk: alias-key presence
   through aliases.json. B-.
5. **solr-bugs-restore-construction** (#26). Target solrj `common/cloud/HashBasedRouter.java:67` ("No active slice servicing
   hash code", inline; a selector: every routed add passes it). Workload `TestCausynthRestoreRetry#restoreTwiceThenAdd`:
   BACKUP S; RESTORE to new T; RESTORE to T again; ADD T, each RESTORE's failure returned rather than thrown and nothing
   waiting for T's shards in between (such a wait never ends in the counterfactual). Counterfactual: FAULT at the first
   RESTORE's RESTORECORE or apply-buffer HTTP request (RestoreCmd.java:282-284) -> T left CONSTRUCTION; the retry takes
   RestoreOnExistingCollection (:600, never marks ACTIVE) and reports success -> ADD has no active slice. Hard to
   recover: only DELETE + RESTORE. B-.
6. **solr-bugs-reindex-cleanup** (#04, the owner's report 5). Target `DeleteCollectionCmd.java:246` (`checkAliasReference`,
   inline; the window's first DELETE, the cleanup's of T). Workload `TestCausynthReindexAbortAlias#
   abortAfterAnAliasOfTheTargetIsRemoved`: REINDEX S->T async, held at `TestInjection#reindexLatch` once S is read-only
   and T exists; CREATEALIAS A->T; DELETEALIAS A (a failure logged, as an operator would go on); ABORT; release the
   latch; at most 30 REQUESTSTATUS polls; an add to S. Counterfactual: a SOLR_HTTP REQUEST fault on DELETEALIAS (an
   IOException: an admin request is retried on another node only on a ConnectException) -> A->T survives -> the
   cleanup's DELETE of T throws -> S's read-only flag and reindexing state are never reset. The report's trigger was a
   concurrent CREATEALIAS; here the workload's own requests order the alias against the cleanup (DELETEALIAS completes,
   the client sends ABORT, the worker reads the abort from ZooKeeper, `checkAliasReference` re-reads aliases.json after
   `update()`), so a re-pairing with A's write is no world. Scope: DeleteCollectionCmd, ReindexCollectionCmd,
   DeleteAliasCmd, OverseerCollectionMessageHandler, Aliases, ZkStateReader.

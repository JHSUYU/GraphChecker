# The checks: every ad hoc coordination point and bug check, per system

The owner's goal is a set of ad hoc coordination checks per system, each run as one campaign whose exported `.smt` is
right (SAT confirmed, or UNSAT at the fixed point; RULES.md "Only SAT or UNSAT"). The points come from the owner's
static study (`study.txt`, branch `study`, 144 YES points with cluster tests), narrowed by the owner on 2026-10-04
(`SELECTION.md`: control plane first, a good cluster test, GraphChecker covers it). Real bug_study bugs that
GraphChecker can check are added (`VERIFIED-BUGS.md`). Ids never move: `<sys>-adhoc-NN` is study point NN.

| file | holds |
| --- | --- |
| [SELECTION.md](SELECTION.md) | the owner's narrowed selection per system: checked points, points without a check, dropped points with the reason |
| [HDFS.md](HDFS.md), [SOLR.md](SOLR.md), [HBASE.md](HBASE.md), [ZOOKEEPER.md](ZOOKEEPER.md) | per system every study point read against OUR tree: site (file:line), guard, coordination, the counterfactual that could flip it, IO rule, the cluster test, fit; then the bug_study bugs and the pick list |
| [VERIFIED-BUGS.md](VERIFIED-BUGS.md) | the lead's code reads of each admitted bug_study bug |

How a check is declared and run: a check's throw is marked in the system's tree with
`throw new @CausynthExceptionTarget("<check id>") E(...)`; its case directory names the tree, the test and the target
occurrence (README "Run one case"). HDFS's 36 study checks are rows of `experiments/hadoop/hdfs-adhoc/checks.tsv`
(id, test class, method, window, target occurrence, analysis scope); the named bugs have their own case directories
(`experiments/hadoop/hdfs-*`). The HDFS trees mark all 49 study points; the Solr, HBase and ZooKeeper trees mark only
their bug targets so far (their study markers are their turn's first TODO).

Counts: HDFS 38 points / 36 checked + 10 named bug checks = 46 cases; Solr 21 / 13 + 8 bug checks (solr-adhoc-22 is
solr-18406) = 20; HBase 30 / 17 + 3 = 20; ZooKeeper 13 / 10 + 3 = 13.

## HDFS (the current system): 36 study checks

State as of the 2026-10-05 handover. "HG7" = the round on the merged body `272afdef2` (stopped by the owner after
7 study verdicts); "HG5A" = the round on the previous body `e76f6b4a8`. Every UNSAT listed was checked: its
exploration reached FIXED_POINT and z3 re-solves the exported `candidate.smt2` to unsat
(`tools/rounds/round-verify.sh`). Final acceptance still owes each case an exclusive run and a hand check of its
`.smt` chain (TODO "The end of HDFS").

| check | site (our tree) | guard | workload | window | state (2026-10-05) |
| --- | --- | --- | --- | --- | --- |
| hdfs-adhoc-05 | H/qjournal/client/QuorumOutputStream.java:106 | `bufToSend.getLength()==numReadyBytes` (the double buffer's flush) | TestQuorumJournalManager#testSingleWriter | up | UNSAT at FIXED_POINT (HG8W); swapped in for 32 (owner 2026-10-05: 32's map removal runs in unnamed pre-window work) |
| hdfs-adhoc-06 | H/qjournal/client/QuorumOutputStream.java:112 | `data.length == bufToSend.getLength()` (the flushed buffer's backing array) | TestQuorumJournalManager#testSingleWriter | up | UNSAT at FIXED_POINT (SW1, 64 symbols, none unbound), but 51 task rounds read only 32 paths: owes the bound fix (TODO §5); swapped in for 01 (owner 2026-10-05) |
| hdfs-adhoc-07 | H/qjournal/server/Journal.java:926 | acceptRecovery would discard a committed txn | TestQuorumJournalManager#testRecoverAfterIncompleteRecovery | up | UNSAT at FIXED_POINT (HG8A, 3 h budget, compose-cost merged): 129 obligations, 61 branches pruned by (r,c), 93 symbols |
| hdfs-adhoc-08 | H/qjournal/server/Journal.java:487 | `reqInfo.epoch < lastPromisedEpoch` | TestQuorumJournalManager#testSingleWriter | up | UNSAT at FIXED_POINT (HG7D, 3 h budget): 417 obligations, 155 paths, 725 symbols |
| hdfs-adhoc-09 | H/qjournal/server/Journal.java:504 | `reqInfo.committedTxId >= committedTxnId` | TestQuorumJournalManager#testSingleWriter | up | UNSAT at FIXED_POINT (HG7D, 3 h budget): 477 obligations, 151 paths, 1068 symbols |
| hdfs-adhoc-10 | H/qjournal/server/Journal.java:518 | `reqInfo.epoch != lastWriterEpoch` | TestQuorumJournalManager#testSingleWriter | up | SAT confirmed, reproduced 10/10 (HG7, SL1): a LOCAL_IO SYNC fault keeps lastWriterEpoch at 0 -> journal() epoch check; QJM designed tolerance, no new bug |
| hdfs-adhoc-11 | H/security/token/block/BlockTokenSecretManager.java:582 (marked) | `allKeys.get(DEK keyId)==null` | TestEncryptedTransfer#testEncryptedReadDefaultAlgorithmCipherSuite[1] | up | UNSAT but NO-SYMBOL (HG7): allKeys.get(DEK keyId) pinned to an identity; the container writers (D1) and the one handoff rule (A3) owed |
| hdfs-adhoc-12 | same file :541 | retrievePassword: `allKeys.get(token keyId)==null` | TestCausynthDataTransferRpcFailure#testUnencryptedReplicationAfterModeledKeyRefreshRpcFailure | up | SAT confirmed, reproduced 10/10 (HG7, SL1): a heartbeat RESPONSE fault loses the KeyUpdateCommand -> retrievePassword misses the token key id (the 17899/17967 root cause) |
| hdfs-adhoc-14 | same file :441 | 6-argument: password from the DN's key != the token password from the NN's key | TestEncryptedTransfer#testEncryptedReadDefaultAlgorithmCipherSuite[1] | up | UNSAT at FIXED_POINT on the r4 tree (R4A): REGION.084d06ab on Anchor:<call> [doAs@0] |
| hdfs-adhoc-15 | H/server/blockmanagement/BlockInfo.java:447 | commitBlock: `!isComplete()` | TestBlockToken#testBlockTokenInLastLocatedBlockLegacy | up | UNSAT (HG7) |
| hdfs-adhoc-16 | H/server/blockmanagement/BlockInfo.java:428 | `uc != null && !isComplete()` | TestClientProtocolForPipelineRecovery#testUpdatePipeLineAfterDNReg | up | UNSAT (HG7; was RUN_DEFECT until E1) |
| hdfs-adhoc-19 | H/server/datanode/BPOfferService.java:777 | the DNA_FINALIZE bpid equals the BPOS bpid | TestDFSFinalize#testFinalize | up | UNSAT (HG7) |
| hdfs-adhoc-20 | H/server/datanode/BPOfferService.java:615 | `txid >= lastActiveClaimTxId` | TestClientProtocolForPipelineRecovery#testPipelineRecoveryOnOOB | up | UNSAT (HG7) |
| hdfs-adhoc-21 | H/server/datanode/BPServiceActor.java:290 (throw at :293) | NN software version < the DN's minimum NN version | TestDFSInputStream#testSkipWithRemoteBlockReader | startup | open: clock-driven seed give-ups (80+ with sorted listings, SL2; R4A): time model (A2) |
| hdfs-adhoc-22 | H/server/datanode/BlockPoolSliceStorage.java:393 | namespaceID: VERSION vs NN | TestDFSStartupVersions#testVersions | up | open: time-model class |
| hdfs-adhoc-23 | same file :399 | blockpoolID: VERSION vs NN | TestDFSStartupVersions#testVersions | up | open: time-model class |
| hdfs-adhoc-24 | same file :421 | stored LV/cTime newer than the namespace | TestDFSUpgrade#testUpgrade | up | rerun HG8B (3 h budget): SL1 cut by the budget (seed replay 21 min); listing fix merged (give-ups 84 -> 5) |
| hdfs-adhoc-25 | same file :185 | cTime mismatch | TestDFSStartupVersions#testVersions | up | open: time-model class |
| hdfs-adhoc-26 | same file :621 | cannot roll back to a newer state | TestDFSRollback#testRollback | up | rerun HG8B (3 h budget): SL1 cut by the budget; listing fix merged (give-ups 89 -> 12) |
| hdfs-adhoc-27 | same file :510 | namespaceID equal during the upgrade | TestDatanodeLayoutUpgrade#testUpgradeToIdBasedLayout | startup | UNSAT at FIXED_POINT (HG7R, SL1) |
| hdfs-adhoc-28 | H/server/datanode/BlockRecoveryWorker.java:565 | `bpos==null` in getDatanodeID | TestBlockRecovery2#testRecoveryTimeout | up | UNSAT but NO-SYMBOL (HG7R): bpos lookup pinned; its writers ran before the window (a constant chain): to confirm after D1 |
| hdfs-adhoc-29 | same file :604 | `bpos==null` in getActiveNamenodeForBP | TestBlockRecovery2#testRecoveryTimeout | up | UNSAT but NO-SYMBOL (HG7R): bpos lookup pinned; writers before the window: to confirm after D1 |
| hdfs-adhoc-30 | same file :609 | `activeNN==null` | TestBlockRecovery2#testRecoveryTimeout | up | UNSAT at FIXED_POINT (HG7R): 4 roots; scope batch 2 (recoveryId) still owed |
| hdfs-adhoc-31 | H/server/datanode/DataNode.java:1838 | `bpos==null` in getBPOSForBlock | TestDiskError#testDataTransferWhenBytesPerChecksumIsZero | up | UNSAT but NO-SYMBOL (HG7R): blockPoolManager.get pinned; the in-window addBlockPool unplanned -> container writers (D1) |
| hdfs-adhoc-33 | H/server/datanode/DataStorage.java:259 | `bpStorage != null` (hot swap) | TestDataNodeHotSwapVolumes#testAddOneNewVolume | up | UNSAT at FIXED_POINT (HG7R, SL1) |
| hdfs-adhoc-34 | same file :741 | namespaceIDs incompatible | TestDFSStartupVersions#testVersions | up | open: time-model class |
| hdfs-adhoc-35 | same file :750 | clusterIDs incompatible | TestDFSStartupVersions#testVersions | up | open: time-model class |
| hdfs-adhoc-37 | same file :942 | cannot roll back to a newer state | TestDFSRollback#testRollback | up | rerun HG8B (3 h budget): SL1 cut by the budget; listing fix merged (give-ups 80 -> 13) |
| hdfs-adhoc-38 | H/server/namenode/FSDirAppendOp.java:123 | the file's storage policy is LAZY_PERSIST (append refused) | TestFileAppend#testAppendTwice | up | UNSAT at FIXED_POINT (SW1, 13 symbols, none unbound, unbounded); swapped in for 17 (owner 2026-10-05) |
| hdfs-adhoc-39 | same file :133 | the last block is COMMITTED, not COMPLETE | TestFileAppend#testAppendTwice | up | UNSAT at FIXED_POINT (HG7R; 126 obligations, 8 paths); SL1 once OCCURRENCE_ADDRESS_SHARED (block-report ops, timing; A3 queue) |
| hdfs-adhoc-40 | same file :139 | the last block is not sufficiently replicated | TestFileAppend#testAppendTwice | up | UNSAT at FIXED_POINT (HG7R) |
| hdfs-adhoc-45 | H/server/namenode/FSEditLog.java:1471 | `!isSegmentOpen()` in endCurrentLogSegment | TestEditLog#testSimpleEditLog[1] | up | UNSAT at FIXED_POINT but NO-SYMBOL (SW1L-45): the edit log's segment state is the NameNode's own, set by its own thread (to read by hand); swapped in for 43 (owner 2026-10-05) |
| hdfs-adhoc-48 | H/server/namenode/INodeDirectory.java:356 | `oldChild == children.get(i)` | TestRenameWithSnapshots#testRenameUndo_1 | up | UNSAT at FIXED_POINT (HG7R): children list modeled, the way left at a concrete guard |
| hdfs-adhoc-49 | H/server/namenode/snapshot/DirectorySnapshottableFeature.java:189 | `n+1 > snapshotQuota` | TestNestedSnapshots#testNestedSnapshots | up | UNSAT at FIXED_POINT (HG7R; 209 obligations) |
| hdfs-adhoc-50 | same file :198 | duplicate snapshot name | TestNestedSnapshots#testNestedSnapshots | up | UNSAT at FIXED_POINT (HG7R, SL1; 141 obligations, 3 paths) |
| hdfs-adhoc-52 | H/server/namenode/snapshot/FSImageFormatPBSnapshot.java:467-468 (marked `hdfs-17960`) | serialized snapshots `i != sm.getNumSnapshots()` | TestFSImageWithSnapshot#testSaveLoadImage | up | UNSAT at FIXED_POINT (HG8Z): declared at the test thread's first image save (FSImageFormatProtobuf.Saver.save, one snapshot; `first` named a rebuilt cluster's format-time save, 0 snapshots, which made the check vacuous); 68 seed give-ups (clock class) |

Summary (2026-10-06, rounds HG9/HG9B/HG9L/SW1 on the merged body; round-verify with UNBOUND): done -- UNSAT at the
fixed point, z3 unsat on the file, unbounded, no unbound handoff -- 11 19 20 26 27 29 30 33 37 38 49 50, and 28 31 45 48
over a chain constant in the window (28 31: the block-pool map filled before the window, removed only after the
target in unnamed work; 48: a single-thread operation under the namesystem lock; 45: the edit log's own segment
state); 10 SAT confirmed, reproduced 10/10. Owed: 15 16 39 40 (the guard's decider never in the fatal predicate: A4),
07 (a relayed QJM segment: A4), 12 14 (unbound handoffs: A1), 05 06 08 09 (task rounds bounded at 32 paths: D1),
21 22 23 24 25 34 35 52 (the time model: A2). Swapped: 32 for 05; 01 17 43 for 06 38 45 (owner 2026-10-05).

## HDFS named bug checks (10)

| case | bug | mechanism (mandate) | state |
| --- | --- | --- | --- |
| hdfs-17897 | striped checksum treats InvalidEncryptionKeyException as an IO failure | IPC door fault | PASS (HG7N, R4A on r4) |
| hdfs-17899-bug1 | stale block key after a failed key refresh (Balancer) | IPC door fault | PASS (HG5A, PS3, RIH1) |
| hdfs-17899-bug2 | same (SPS) | IPC door fault | PASS (RIH1, cone.py without the FREE exemption: the key id bound by its message family) |
| hdfs-17899-bug3 | same (source DN) | IPC door fault | PASS (HG5A, RIH1) |
| hdfs-17960 | ordered=false lets a duplicate delete record decrement numSnapshots | CONFIG | PASS (HG5A, HCL1, PS3) |
| hdfs-17967-pathA/B/C | three DN relay paths abandon on ERROR_UNKNOWN_KEY | IPC door fault | PASS (HG5A; pathA WHF1) |
| hdfs-bugs-slowdisk-zero | bug_study HDFS #15: max slow disks 0 leaves a stale exclusion list | STATE re-pairing | PASS (HG5A) |
| hdfs-11741 | a stale block key after expiry (its own tree gc/hdfs-11741-r4) | CLOCK_SKEW | PASS in HG7N (CLOCK_SKEW, both clocks in the cone, key id bound); timing-dependent: the one handoff rule (A3, in review) binds the witness path; paths through an uninstrumented balancer move still HELD (closure fix owed); native reproduction of a clock owed (A4) |

## Solr, HBase, ZooKeeper: the study checks (their turn comes after HDFS)

None of these study points is marked in its system's tree yet, except solr-adhoc-22 (solr-18406's throw).

### solr
| check | site (our tree) | guard | workload (test) | state |
| --- | --- | --- | --- | --- |
| solr-adhoc-05 | C cloud/ZkController.java:1274 | replica gone from the node's state right after `waitForState` saw it | AddReplicaTest#testAddMultipleReplicas | not marked yet (the system's turn: TODO) |
| solr-adhoc-07 | same:1326 | `cc.getCore(name) == null` during register | same | not marked yet (the system's turn: TODO) |
| solr-adhoc-09 | C cloud/api/collections/DeleteReplicaCmd.java:278 | `!callable.call()`: `waitForCoreNodeGone` false twice | DeleteReplicaTest#deleteReplicaAndVerifyDirectoryCleanup | not marked yet (the system's turn: TODO) |
| solr-adhoc-10 | C cloud/api/collections/MaintainRoutedAliasCmd.java:117 | `RoutedAlias.fromProps(props) == null` with non-empty props | TimeRoutedAliasUpdateProcessorTest#test | not marked yet (the system's turn: TODO) |
| solr-adhoc-13 | C cloud/api/collections/RoutedAlias.java:350 | after MAINTAINROUTEDALIAS + `aliasesManager.update()` the alias list lacks the new collection | TimeRoutedAliasUpdateProcessorTest#testPreemptiveCreation | not marked yet (the system's turn: TODO) |
| solr-adhoc-14 | C cloud/api/collections/SplitShardCmd.java:167 | `exists(live_nodes/<leader node>) == null` | SplitShardTest#doTest | not marked yet (the system's turn: TODO) |
| solr-adhoc-19 | C core/CoreContainer.java:1330 | node says non-legacy (`legacyCloud` != "true") and the CREATE carries no coreNodeName (Overseer s... | AddReplicaTest#testAddMultipleReplicas never sets legacyCloud (no w... | not marked yet (the system's turn: TODO) |
| solr-adhoc-21 | same:1765 | this core's replica present in docCollection on reload | CollectionReloadTest#testReloadedLeaderStateAfterZkSessionLoss | not marked yet (the system's turn: TODO) |
| solr-adhoc-22 | C core/IndexDeletionPolicyWrapper.java:179 | requested generation deleted / older than latest | TestPullReplica#testAddDocs (study); our case TestCausynthPullRepli... | marked: = solr-18406 (PASS on main, V25) |
| solr-adhoc-31 | same:1477 | FORCELEADER refused: slice leader ACTIVE in this node's view | ForceLeaderTest#testReplicasInLowerTerms (@Nightly; base AbstractFu... | not marked yet (the system's turn: TODO) |
| solr-adhoc-38 | same:1031 | cluster state says we lead, `cloudDesc.isLeader()` still false after 5 x 500 ms | CloudHttp2SolrClientTest#testAliasHandling (solrj); core: TestPullR... | not marked yet (the system's turn: TODO) |
| solr-adhoc-39 | C update/processor/RoutedAliasUpdateProcessor.java:247 (thrown at R... | node's alias view lacks the alias on a commit | TimeRoutedAliasUpdateProcessorTest#test | not marked yet (the system's turn: TODO) |
| solr-adhoc-40 | same:133 (thrown at RoutedAlias.java:72, rewrapped :123) | same at processor creation | same | not marked yet (the system's turn: TODO) |

### hbase
| check | site (our tree) | guard | workload (test) | state |
| --- | --- | --- | --- | --- |
| hbase-adhoc-04r | AbstractStateMachineTableProcedure.java:163 (re-sited to the server) | `!ts.isEnabledOrEnabling()` | `TestMobStoreScanner#testMobStoreScanner` (admin.flush -> FlushTabl... | not marked yet (the system's turn: TODO) |
| hbase-adhoc-07r | SnapshotManager.java:1046 (re-sited to the server) | table state ENABLED at restore | `TestRestoreFlushSnapshotFromClient#testRestoreSnapshot` (3 RS) | not marked yet (the system's turn: TODO) |
| hbase-adhoc-08 | `master/ClusterSchemaServiceImpl.java:111` | `TableNamespaceManager.cache.get(ns)==null` | `namespace/TestNamespaceAuditor#testTableOperations` (2 masters, qu... | not marked yet (the system's turn: TODO) |
| hbase-adhoc-10 | `master/assignment/AssignmentManager.java:765` | `regionNode.getProcedure()!=null` | `regionserver/TestRegionMove#testDisableAndMove` (2 RS) | not marked yet (the system's turn: TODO) |
| hbase-adhoc-11 | `AssignmentManager.java:769` | `!regionNode.isInState(expected)` | same | not marked yet (the system's turn: TODO) |
| hbase-adhoc-12 | `AssignmentManager.java:772` | `isTableDisabled(table)` | same | not marked yet (the system's turn: TODO) |
| hbase-adhoc-13 | `master/assignment/MergeTableRegionsProcedure.java:499` | `regionStateStore.hasMergeRegions(ri)` (meta Get) | master/assignment/TestMergeTableRegionsProcedure#testMergeTwoRegio... | not marked yet (the system's turn: TODO) |
| hbase-adhoc-14 | `MergeTableRegionsProcedure.java:503` | `regionStates.getRegionState(enc)==null` | same | not marked yet (the system's turn: TODO) |
| hbase-adhoc-15 | `MergeTableRegionsProcedure.java:507` | `!state.isOpened()` | same | not marked yet (the system's turn: TODO) |
| hbase-adhoc-19 | `master/procedure/ModifyTableProcedure.java:134` | unmodified CF count != modified (reopenRegions=false) | master/procedure/TestModifyTableProcedure#testModifyWillNotReopenR... | not marked yet (the system's turn: TODO) |
| hbase-adhoc-20 | `ModifyTableProcedure.java:138` | `isCoprocModified()` | testModifyWillNotReopenRegions / testModifyTableWithCoprocessorA... | not marked yet (the system's turn: TODO) |
| hbase-adhoc-21 | `namespace/NamespaceStateManager.java:130` | regions - tableRegions + incr > maxRegions | named testRestoreSnapshotQuotaExceed REACHES it by design; use T... | not marked yet (the system's turn: TODO) |
| hbase-adhoc-22 | `NamespaceStateManager.java:168` | regionCount + numRegions > maxRegions | named testTableOperations REACHES :168 and :160 by design; use T... | not marked yet (the system's turn: TODO) |
| hbase-adhoc-24 | `procedure/ZKProcedureMemberRpcs.java:210` (caught at :217) | `!isPBMagicPrefix(znode data)` | master/procedure/TestFlushTableProcedureWithDoNotSupportFlushTable... | not marked yet (the system's turn: TODO) |
| hbase-adhoc-31 | `RSRpcServices.java:1880` | RS startcode != request's serverStartCode | `TestRegionMove#testDisableAndMove` | not marked yet (the system's turn: TODO) |
| hbase-adhoc-34 | `AuthenticationTokenSecretManager.java:160` | `allKeys.get(keyId)==null` after refreshKeys | `security/token/TestGenerateDelegationToken#testOnlyToken` (SecureT... | not marked yet (the system's turn: TODO) |
| hbase-adhoc-37 | `MasterAddressTracker.java:206` | master znode data == null | `regionserver/http/TestRSStatusPage#testStatusPage` (direct LocalHB... | not marked yet (the system's turn: TODO) |

### zk
| check | site (our tree) | guard | workload (test) | state |
| --- | --- | --- | --- | --- |
| zk-adhoc-01 | SessionTrackerImpl.java:317 | `session.isClosing()` in `checkSession` | QuorumPeerMainTest#testQuorum (exists). The guard is also evaluated... | not marked yet (the system's turn: TODO) |
| zk-adhoc-02 | SessionTrackerImpl.java:323 | `session.owner != owner` | testQuorum (exists, cannot throw); equivalent QuorumTest#testSessio... | not marked yet (the system's turn: TODO) |
| zk-adhoc-03 | SessionTrackerImpl.java:330 | `session == null \|\| session.isClosing()` in `setOwner` (createSession Prep, PrepRequestProcesso... | testQuorum; ClientBase equivalent as 01 | not marked yet (the system's turn: TODO) |
| zk-adhoc-04 | ZooKeeperServer.java:1537 | `connReq.lastZxidSeen > zkDb.dataTree.lastProcessedZxid` | testQuorum (exists, cannot throw); candidate ReadOnlyModeTest#testS... | not marked yet (the system's turn: TODO) |
| zk-adhoc-06 | quorum/Leader.java:1515 | `ss.isMoreRecentThan(leaderStateSummary)` in `waitForEpochAck` | testQuorum | not marked yet (the system's turn: TODO) |
| zk-adhoc-07 | quorum/Learner.java:522 | LEADERINFO `newEpoch < acceptedEpoch` | QuorumRestartTest#testRollingRestart (exists) | not marked yet (the system's turn: TODO) |
| zk-adhoc-10 | quorum/ObserverMaster.java:371 | head of `proposedPkts` zxid != committed zxid (smaller) | ObserverMasterTest#testInOrderCommits(boolean) (exists; parameteriz... | not marked yet (the system's turn: TODO) |
| zk-adhoc-11 | quorum/QuorumPeer.java:1177 | `currentEpoch < epochOf(lastProcessedZxid)` and no `currentEpoch.tmp` | CurrentEpochWriteFailureTest#testReadCurrentEpochFromAcceptedEpochT... | not marked yet (the system's turn: TODO) |
| zk-adhoc-12 | quorum/QuorumPeer.java:1197 | `acceptedEpoch < currentEpoch` | testQuorum | not marked yet (the system's turn: TODO) |
| zk-adhoc-13 | quorum/ReadOnlyZooKeeperServer.java:126 | `isGlobalSession(sessionId)` at a session renewal on an RO peer | ReadOnlyModeTest#testGlobalSessionInRO (exists); prefer #testConnec... | not marked yet (the system's turn: TODO) |

## Solr, HBase, ZooKeeper: the bug checks

| case | bug | mechanism | state |
| --- | --- | --- | --- |
| solr-18406 (= solr-adhoc-22) | the leader deletes a generation after the reservation expires | CLOCK_SKEW | PASS on main (V25) |
| solr-18413 | a MIGRATE route rule expires; the update looks up a deleted collection | CLOCK_SKEW | PASS on main (V25); regressed on branch solr-bug-reindex (seed replay stalls) |
| solr-bugs-reindex-cleanup | #04: a failed same-target reindex leaves the alias; cleanup throws | ZK/HTTP door fault | no witness yet (branch solr-bug-reindex) |
| solr-bugs-migrate-buffer-leak | #17: a failure after REQUESTBUFFERUPDATES leaves the target core BUFFERING | door fault | admitted, no case |
| solr-bugs-overseer-lock-leak | #50: OperationTimeout in markTaskAsRunning leaks the lock | ZK door fault | admitted, no case |
| solr-bugs-snapshot-no-active | #16: CREATESNAPSHOT skips non-ACTIVE replicas and reports success | stale Overseer view | admitted, no case |
| solr-bugs-restore-construction | #26: a failed RESTORE leaves slices in CONSTRUCTION | HTTP door fault | admitted, no case |
| solr-bugs-tra-start-overwrite | #20: TimeRoutedAlias writes a stale aliases snapshot over a newer alias | STATE re-pairing | admitted, no case |
| hbase-bugs-master-active-time | #14: a non-monotonic activeTime makes the new master reject an old OPENED report | CLOCK | branch hbase-startup, blocked on two design questions (TODO HBase) |
| hbase-bugs-backup-lock-reply-lost | HBase-2 #16: a lost CAS reply makes the retry fail on its own lock | HBase RPC RESPONSE door | admitted, no case (needs the door) |
| hbase-bugs-ns-rsgroup-removal | HBase-2 #01: rsgroup removal cannot see an in-flight namespace creation | STATE re-pairing | admitted, no case |
| zk-bugs-quota-init | #01: the quota limit is committed before the stat node | ZK write door fault | PASS on main (V12+) |
| zk-bugs-election-offer | #05: a competitor's offer vanishes before getData | STATE re-pairing | PASS on main (V18+) |
| zk-bugs-container-reuse | #33: ContainerManager deletes a node recreated at the same path | STATE re-pairing | admitted, no case (self-written ClientBase test) |

Not admitted: HDFS-2 #09 reencrypt-negative-sleep (the chain ends in a JDK-internal negative-sleep exception; dropped
after HG1), ZooKeeper #32 (a contrib GUI tool).

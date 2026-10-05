<!-- Moved into the repo at the 2026-10-05 handover from /bigtemp/vnr3ne/analysis/study-2026-10-04/hdfs.md (investigator tables of 2026-10-04, read against our trees). Ids never move. Live status per check: docs/checks/README.md and docs/handover/STATE.md. -->
# HDFS: the study's ad hoc coordination checks on our tree (2026-10-04)

Read-only investigation. Our tree: `/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx` (`gc/hdfs-unified-dtx` `51f1e058380`, Hadoop
trunk 3.6.0-SNAPSHOT of 2026-05-13 plus the adapter). `/bigtemp/vnr3ne/wt/hadoop-hdfs-bugs` is the same base plus #15.
The study (study.txt) audited HDFS 3.4.3, so every line below was looked up again in our tree. Paths are short:
`H/` = `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/`, `C/` = `hadoop-hdfs-project/hadoop-hdfs-client/src/main/java/org/apache/hadoop/hdfs/`.
In scope lists: `hdfs:` / `client:` / `common:` are system.sh's class roots.

## What holds for every check (read this first)

1. **Workload mode.** With `-Dcausynth.cluster.automatic=true` (`CausynthCluster.AUTOMATIC`), every MiniDFSCluster a test
   builds is configured (nothing expires; socket/RPC timeouts 6 h), registered whole (`auto<n>/nn<i>`, `auto<n>/dn<i>`),
   and the first cluster opens the window with one request after start-up. So any MiniDFSCluster test runs as written.
   Three consequences:
   - A guard that only runs while a cluster starts (format, the DataNode handshake, loading storage) runs **before**
     the default window. It needs the opt-in `recording_window=startup` (owner ruling 12). This applies to 21 and 46.
   - **QJM tests (05-10) build only a MiniJournalCluster.** The adapter has no hooks there, so the JournalNodes are not
     registered and no window opens. The tree needs one small adapter change: MiniJournalCluster hooks like
     MiniDFSCluster's, i.e. register each JournalNode (`JournalNodeRpcServer`, `Journal`) as `auto<n>/jn<i>`, register
     the test's QuorumJournalManager as the client source, open the window after `waitActive`, and apply
     `CausynthCluster.configure` (the test sets `ipc.client.connection.maxidletime=0`). `createSpyingQJM` uses Mockito
     spies of `IPCLoggerChannel`, which is a replay risk.
   - The RBF module (`hadoop-hdfs-rbf`) is outside `system_paths` (hadoop-hdfs only), and there is no Router node
     adapter. Every Router bug in part B is out for that reason alone.
2. **Marker rewrite.** `Preconditions.checkState/checkArgument` and Java `assert` sites have no `throw new` at the line.
   The tree must replace them with `if (!(cond)) throw new @CausynthExceptionTarget("hdfs-adhoc-NN") IllegalStateException(msg)`
   (`IllegalArgumentException` for checkArgument, `AssertionError` for assert). These are: 03, 05, 06, 09, 15, 16, 17,
   18, 19, 20, 27, 33, 45, 46, 47, 48, 51, 53. Item 21 builds the exception into a local (`ive`) and throws it two lines
   later, so it must become one `throw new @...`. Item 07 is already `throw new AssertionError` and needs only the
   annotation. Items 11 and 52 already carry markers (the regression cases); add the new id to the marker's id list.
3. **Degenerate checks.** For 22-26, 32, 34, 35, 37, 41, 43 and 44 the named test already throws at the site: it
   expects the exception. Recording the passing run therefore already reaches the throw. The case must declare a
   **non-throwing occurrence** of the region as its target where the test has one:
   - compatible version combinations (22, 23, 25, 34, 35);
   - successful upgrades and rollbacks (24, 26, 37);
   - the `deleteBlockPool` after `refreshNamenodes` (32);
   - a same-root rename (41);
   - truncates to a smaller length (44).
   Item 43 has none: its only evaluation is the expected throw.
4. **IO rule.** Every DataNode storage/VERSION guard (22-27, 34, 35, 37) compares fields that were read from disk. The
   fsimage-load guard (47) and JournalNode restarts (07) also go through disk. These are kept as checks (owner
   ruling 2026-10-04) but marked C.
5. **Locks are not HB edges on main.** For the NameNode block-state invariants (15-17), a STATE re-pairing between two
   reads under the FSNamesystem write lock is formally eligible, but CONFIRM refutes it. No witness is expected.

## A. Every study item (53)

| id | our file:line | kind | guard (one line) | coordination? | counterfactual that could flip it / why none | IO ok? | test in our tree | fit |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 01 | C/DFSInputStream.java:517 | throw EOFException | the NN returns no located block for an offset (`newBlocks==null \|\| count==0`) | Y: the client's cached file view vs the NN's INodeFile | none in the test: no concurrent truncate or delete. An INITIAL pairing of the NN's blocks read is HB-ordered after the write (close, then open). A getBlockLocations FAULT surfaces as the RPC's own exception, not as EOF | ok | TestPread#testPreadDFS | C |
| 02 | C/DataStreamer.java:428 | throw IllegalStateException | ErrorState: `badNodeIndex==restartingNodeIndex && waitForRestart` | weak: the DN's OOB-restart ack vs the client's error indices (client-local state machine) | `waitForRestart` comes from the test hook `skipRollingRestartWait()=true`, which is not a root. The ack stream has no door | ok | TestClientProtocolForPipelineRecovery#testPipelineRecoveryOnRemoteDatanodeUpgrade | C |
| 03 | C/DataStreamer.java:1430 | assert | PIPELINE_CLOSE recovery: `lastAckedSeqno == endOfBlock.seqno-1` | weak: DN acks (ResponseProcessor thread) vs the streamer's queue | the client waits for every ack before PIPELINE_CLOSE, so re-pairing `lastAckedSeqno` to an older write is refuted by that wait. The ack stream has no door | ok | ...#testAddingDatanodeDuringClosing | C |
| 04 | C/DataStreamer.java:973 | throw InterruptedIOException | `monotonicNowNanos()-begin > writeTimeout` while waiting for an ack | weak: a timeout on the DN ack, i.e. two clock reads by one thread | CLOCK (client `Time.monotonicNowNanos`) fires the designed timeout trivially, and automatic mode makes writeTimeout 6 h. A witness would say nothing | ok | ...#testAddingDatanodeDuringClosing | C |
| 05 | H/qjournal/client/QuorumOutputStream.java:106 | assert | `bufToSend.getLength()==numReadyBytes` | N (local double buffer) | none | ok | TestQuorumJournalManager#testSingleWriter (JN adapter needed) | C |
| 06 | H/qjournal/client/QuorumOutputStream.java:108 | assert | `data.length==bufToSend.getLength()` | N | none | ok | same | C |
| 07 | H/qjournal/server/Journal.java:926 | throw new AssertionError | acceptRecovery would discard a committed txn | Y: the new writer's recovery proposal vs this JN's committedTxnId | Paxos quorum intersection guarantees the relation; no single flip breaks it | **no**: the test stops and restarts JNs, so committedTxnId and paxos data are reloaded from disk | ...#testRecoverAfterIncompleteRecovery | C |
| 08 | H/qjournal/server/Journal.java:487 | throw IOException | `reqInfo.epoch < lastPromisedEpoch` | Y: the writer epoch in RequestInfo vs the JN's promise | only a second writer raises the promise, and testSingleWriter has one. Re-pairings yield 0 or 1 only | ok | testSingleWriter | C |
| 09 | H/qjournal/server/Journal.java:504 | checkArgument | `reqInfo.committedTxId >= committedTxnId` | Y: the writer's committed txid vs the JN's | the per-logger single-thread executor and the IPC serial keep requests in order; no single flip lowers the value | ok | testSingleWriter | C |
| 10 | H/qjournal/server/Journal.java:518 | throw IOException | `reqInfo.epoch != lastWriterEpoch` | Y: the epoch carried by `journal()` vs the JN's lastWriterEpoch, which `startLogSegment` sets | **FAULT** at the request door of `startLogSegment` to one JN. The quorum still succeeds, and `IPCLoggerChannel` does not mark that logger out of sync. The JN keeps INITIAL `lastWriterEpoch=0`; the next `sendEdits` sends `journal(epoch 1)` and the check throws | ok (`PersistentLongFile.value` lives in memory) | testSingleWriter | **A** (needs the JN adapter) |
| 11 | H/security/token/block/BlockTokenSecretManager.java:582 (marked) | throw InvalidEncryptionKeyException | `allKeys.get(DEK keyId)==null` | Y: NN key rotation vs the DN's key set (KeyUpdateCommand via heartbeat; NN clears needKeyUpdate on send) | = the eight known cases: a FAULT on the DN heartbeat response that carries the KeyUpdateCommand, after rotations. The study's test has no rotation in its window, so it would need two NN rotations (CLOCK at HeartbeatManager, nested; 11741 showed how hard that is) | ok | TestEncryptedTransfer#testEncryptedReadDefaultAlgorithmCipherSuite (parameterized) | **A** (covered); B- with this test |
| 12 | same file :541 | throw InvalidToken | retrievePassword: `allKeys.get(token keyId)==null` | Y: as 11, but the block token instead of the DEK | the FAULT of 11 on the DN's KeyUpdateCommand response, after two rotations. With encryption on, the SASL check (:582) runs first, and the DEK's key is never older than the token's, so the case needs **encryption off** | ok | named test; better: an encryption-off variant of TestCausynthDataTransferRpcFailure#testReplicationAfterModeledKeyRefreshRpcFailure | **B** |
| 13 | same file :461 | throw InvalidToken | password check of the 4-argument Token overload | - | **no production caller** in our tree: BlockPoolTokenSecretManager's 4-argument Token overload is never called, and DataXceiver:1465 uses the 6-argument one. No cluster test (NO_PATH) | - | none | **DROP** |
| 14 | same file :441 | throw InvalidToken | 6-argument: password from the DN's key != the token password from the NN's key | Y: NN vs DN key bytes for one keyId | needs two different keys under one id; key bytes come from KeyGenerator, which is not a root | ok | TestEncryptedTransfer#testEncryptedReadDefaultAlgorithmCipherSuite | C |
| 15 | H/server/blockmanagement/BlockInfo.java:447 | checkState | commitBlock: `!isComplete()` | N: `commitOrCompleteLastBlock` returns first if the block is complete, under the FSN write lock | a re-pairing between the two reads is refuted (same lock) | ok | TestBlockToken#testBlockTokenInLastLocatedBlockLegacy | C |
| 16 | H/server/blockmanagement/BlockInfo.java:428 | checkState | `uc != null && !isComplete()` | N: `checkUCBlock` runs first, under the write lock | none | ok | TestClientProtocolForPipelineRecovery#testUpdatePipeLineAfterDNReg | C |
| 17 | H/server/blockmanagement/BlockManager.java:2871 | checkArgument | `!storedBlock.isComplete()` | N: `isBlockUnderConstruction` runs just before, under the same lock | none | ok | TestAddStripedBlocks#testAddUCReplica | C |
| 18 | H/server/blockmanagement/DatanodeDescriptor.java:537 | assert | injectStorage: the existing storage `== s` | weak: the PROVIDED storage map vs heartbeats | none. Evaluation needs a second provided-storage update (WORKLOAD_UNCERTAIN); MiniKdc | ok | TestSecureAliasMap#testSecureConnectionToAliasMap | C |
| 19 | H/server/datanode/BPOfferService.java:777 | assert | the DNA_FINALIZE bpid equals the BPOS bpid | nominal: NN command vs DN BPOS | the strings are fixed at format; no root | ok | TestDFSFinalize#testFinalize | C |
| 20 | H/server/datanode/BPOfferService.java:615 | assert | `txid >= lastActiveClaimTxId` | Y: NN HA txid vs the DN's last claim | the NN txid is monotonic. Daemon ticks are separate roots, so a re-pairing to an older edit-log write is formally eligible, but CONFIRM refutes it | ok | ...#testPipelineRecoveryOnOOB | C |
| 21 | H/server/datanode/BPServiceActor.java:290 (throw at :293) | throw (new, then `throw ive`) | NN software version < the DN's minimum NN version | nominal | String config (`dfs.datanode.min.supported.namenode.version`) is not a root. Runs at the DN handshake, i.e. at start-up | ok | TestDFSInputStream#testSkipWithRemoteBlockReader | C |
| 22 | H/server/datanode/BlockPoolSliceStorage.java:393 | throw IOException | namespaceID: VERSION vs NN | storage vs NN | VERSION file | **no** | TestDFSStartupVersions#testVersions (degenerate) | C |
| 23 | same file :399 | throw IOException | blockpoolID: VERSION vs NN | storage vs NN | VERSION file | **no** | same (degenerate) | C |
| 24 | same file :421 | throw IOException | stored LV/cTime newer than the namespace | storage vs NN | VERSION file | **no** | TestDFSUpgrade#testUpgrade (degenerate) | C |
| 25 | same file :185 | throw IOException | cTime mismatch | storage vs NN | VERSION file | **no** | TestDFSStartupVersions#testVersions (degenerate) | C |
| 26 | same file :621 | throw InconsistentFSStateException | cannot roll back to a newer state | storage vs NN | `previous/` VERSION | **no** | TestDFSRollback#testRollback (degenerate) | C |
| 27 | same file :510 | assert | namespaceID equal during the upgrade | storage vs NN | VERSION file | **no** | TestDatanodeLayoutUpgrade#testUpgradeToIdBasedLayout | C |
| 28 | H/server/datanode/BlockRecoveryWorker.java:565 | throw IOException | `bpos==null` in getDatanodeID | Y: the NN's recovery command vs the DN's block-pool lifecycle | only `BlockPoolManager.remove` writes the map, at cluster shutdown, after the window's request has ended | ok | TestBlockRecovery2#testRecoveryTimeout | C (B- if the shutdown is recorded) |
| 29 | same file :604 | throw IOException | `bpos==null` in getActiveNamenodeForBP | as 28 | as 28 | ok | same | C |
| 30 | same file :609 | throw IOException | `activeNN==null` | Y: the DN's view of the active NN (heartbeat HA state) vs the recovery command | `bpServiceToActive` is written at the handshake (before the window) and by `shutdownActor` (shutdown). Non-HA heartbeats never write it | ok | same | C (B- likewise) |
| 31 | H/server/datanode/DataNode.java:1838 | throw IOException | `bpos==null` in getBPOSForBlock | Y: as 28 | no writer of dn0's map in the window (the new DN registers its own map) | ok | TestDiskError#testDataTransferWhenBytesPerChecksumIsZero | C |
| 32 | H/server/datanode/DataNode.java:3826 | throw IOException | the block pool is still running | admin-op guard | the test's first `deleteBlockPool` expects this throw | ok | TestDeleteBlockPool#testDeleteBlockPool (degenerate) | C |
| 33 | H/server/datanode/DataStorage.java:259 | assert | `bpStorage != null` (hot swap) | weak: hot swap vs BP registration | the BP registered at start-up, HB-ordered | ok | TestDataNodeHotSwapVolumes#testAddOneNewVolume | C |
| 34 | same file :741 | throw IOException | namespaceIDs incompatible | storage vs NN | VERSION file | **no** | TestDFSStartupVersions#testVersions (degenerate) | C |
| 35 | same file :750 | throw IOException | clusterIDs incompatible | storage vs NN | VERSION file | **no** | same (degenerate) | C |
| 36 | same file :777 | throw IOException | "BUG: The stored LV" | - | NO_PATH: the assert at :731 fires first, and there is no cluster test | - | none | **DROP** |
| 37 | same file :942 | throw InconsistentFSStateException | cannot roll back to a newer state | storage vs NN | VERSION file | **no** | TestDFSRollback#testRollback (degenerate) | C |
| 38 | H/server/namenode/FSDirAppendOp.java:122 | throw UnsupportedOperationException | append to a LAZY_PERSIST file | N (the file's policy) | none | ok | TestFileAppend#testAppendTwice | C |
| 39 | same file :133 | throw RetriableException | the last block is COMMITTED, not COMPLETE | Y: the client's close/append vs the DN's IBR (COMMITTED to COMPLETE) | **CONFIG** `dfs.namenode.file.close.num-committed-allowed` (field `FSNamesystem.numCommittedAllowed`, read in completeFile) set to 1: close returns with the block COMMITTED, and append sees COMMITTED if the IBR is processed later. Depends on recording order; may also need the IBR re-paired after the read | ok | TestFileAppend#testAppendTwice | B- |
| 40 | same file :139 | throw IOException | the last block is not sufficiently replicated | Y: replica map vs live DN count | 1 DN: when the replica's DN is dead, `liveReplicas >= numLiveDataNodes` holds anyway. Raising minReplication would block completion first | ok | same | C |
| 41 | H/server/namenode/FSDirRenameOp.java:913 | throw SnapshotException | src and dst are under different snapshot roots | N (request validation) | the test throws it on purpose (`validateRename`) | ok | TestRenameWithOrderedSnapshotDeletion#testRename (degenerate) | C |
| 42 | H/server/namenode/FSDirTruncateOp.java:101 | throw UnsupportedOperationException | truncate a LAZY_PERSIST file | N | none | ok | TestFileTruncate#testTruncateTwiceTogether | C |
| 43 | same file :117 | throw AlreadyBeingCreatedException | a second truncate with another length while the block is under recovery | nominal: second truncate vs ongoing recovery | the test's second truncate expects it; this is the only evaluation | ok | same (degenerate, no non-throwing occurrence) | C |
| 44 | same file :133 | throw HadoopIllegalArgumentException | truncate to a larger size | N (argument) | the test expects it | ok | TestFileTruncate#testTruncateFailure (degenerate) | C |
| 45 | H/server/namenode/FSEditLog.java:1469 | checkState | `isSegmentOpen()` | N (local state machine) | none | ok | TestEditLog#testSimpleEditLog | C |
| 46 | H/server/namenode/FSImage.java:184 | checkState | `fileCount==1` at format | N | runs at format, before the window | ok | TestDFSInputStream#testSkipWithRemoteBlockReader | C |
| 47 | H/server/namenode/FSImageFormatPBINode.java:530 | checkState | EC policy id > 0 when loading | N | the policy id comes from the fsimage | **no** | TestSafeModeWithStripedFile#testStripedFile0 | C |
| 48 | H/server/namenode/INodeDirectory.java:356 | checkState | `oldChild == children.get(i)` | N | none (the test installs a spy) | ok | TestRenameWithSnapshots#testRenameUndo_1 | C |
| 49 | H/server/namenode/snapshot/DirectorySnapshottableFeature.java:189 | throw SnapshotException | `n+1 > snapshotQuota` | N (per-directory constant) | none (the configured limit is a different throw, SnapshotManager:488) | ok | TestSnapshot#testSnapshot | C |
| 50 | same file :198 | throw SnapshotException | duplicate snapshot name | N | none | ok | same | C |
| 51 | same file :601 | checkState | diff roots == `snapshotsByNames.size()` | N (debug dump) | none | ok | same | C |
| 52 | H/server/namenode/snapshot/FSImageFormatPBSnapshot.java:467-468 (marked `hdfs-17960`) | throw (the upstream checkState, already rewritten) | serialized snapshots `i != sm.getNumSnapshots()` | Y-ish: SnapshotManager's global counter vs the per-directory lists | = hdfs-17960 (CONFIG `snapshot.deletion.ordered` plus a restart). The study's test has no deletion or replay | ok (17960's chain) | TestFSImageWithSnapshot#testSaveLoadImage | **A** (covered by hdfs-17960); C with this test |
| 53 | H/server/namenode/visitor/NamespacePrintVisitor.java:160 | checkState | diff roots == numSnapshots | N (print visitor) | none | ok | TestFSImageWithSnapshot#testDoubleRename | C |

## B. bug_study bugs not covered by README §0.3 (HDFS-2 #01-#31, HDFS-3 C01 and #01-#10)

§0.3 judged the first batch (HDFS #01-#15). None of the later bugs is on a study.txt site.

| bug | in our tree (fatal throw) | coordination? | single counterfactual | chain in memory? | cluster test | fit | study item? |
| --- | --- | --- | --- | --- | --- | --- | --- |
| HDFS-2 01 (re-enabled sampling does not restart the slow-disk detector) | yes: `DataNode.reconfSlowDiskParameters` H/server/datanode/DataNode.java:937-942 restarts only if `diskMetrics==null`, and FsVolumeList keeps a final reference to the old object. Fatal: RoundRobinVolumeChoosingPolicy:84 (= slowdisk-zero's throw) | Y | STATE re-pairing of a detector turn to the hook's slow sample, as in #15 | yes | self-written | **C**: the witness does not tell the bug apart from the hook. `addSlowDiskForTesting` sets `overrideStatus=false`, so a correctly restarted detector would republish [SSD] as well. Natural detection needs at least min-outlier-detection disks and timed IO latencies (metrics doubles) | no (shares #15's throw) |
| HDFS-2 02, 05, 06, 08, 16-18, 21, 22, 24, 26-30 | RBF (hadoop-hdfs-rbf) | mostly deterministic Router logic (path, id or namespace mix-ups) | none | - | RBF MiniCluster | C (deterministic; RBF outside system_paths; no Router adapter; 02 is only a recovery window) | no |
| HDFS-2 03 | RBF, MockNamenode | Y | a FAULT would have to be an EOFException specifically | - | RBF | C (RBF; the fault is persistent) | no |
| HDFS-2 04 | BlockManager chooseTarget IOException | weak | needs `-1ms` (invalid operator input, reconfig string) | - | - | C (invalid input) | no |
| HDFS-2 07 | DFSInputStream BlockMissingException (:1018) | weak | needs a value at 2^31 ms through the reconfig string argument (not a CONFIG getter), plus an NN restart | partly | self-written | C (extreme operator value) | no |
| **HDFS-2 09** (re-encryption throttle computes a negative sleep) | **yes**: H/server/namenode/ReencryptionHandler.java:778-794 computes `sleepMs` from a second `throttleTimerAll` read. Negative values fall through `TimedWaits.sleepFor` to JDK `Thread.sleep(long,int)`'s `millis<0` IAE (Java bytecode, a path condition). `run()` returns on Throwable (:368-371) and the zone stays Processing. Fatal: **EncryptionZoneManager.java:666** `throw new IOException("Zone ... is already submitted for re-encryption.")` (`hasRunningZone`) | Y: the admin's START vs the zone status the handler published, with nothing tying that status to the handler thread's life | **CLOCK** (nn0 `Timer.monotonicNowNanos` reads inside StopWatch) | yes, all on the NN; FP arithmetic `(long)(all*ratio)`, which SmtNames lowers to `fp.*` | **self-written**: TestReencryption's cluster tests keep the ratio at 1.0, which returns before the clock code; TestReencryptionHandler#testThrottle is a mocked unit test | **B, ADD** | no |
| HDFS-2 10 | yes (same guard) | Y | none: needs a persisted checkpoint and an NN restart | **no** (IO) | - | C | no |
| HDFS-2 11 | yes: FSTreeTraverser.java:190-193 re-resolves the parent after the lock yield; the IOException branch (:362) leaves the zone Processing | Y (a lookup vs a concurrent delete/replace) | STATE re-pairing of the zone directory's child lookup to the client's create-file | in memory, but through the binary search of `INodeDirectory.children` (byte[] names) in `INodesInPath.resolve`, plus four namespace ops | the pause-hook race tests are not this case | B-, **not added** (not checkable today; 09 already reaches the guard) | no |
| HDFS-2 12 | yes | Y | none: the IOException is injected through `EncryptionFaultInjector`; there is no door | - | - | C | no |
| HDFS-2 13 | yes: DatanodeManager.java:1873 `DisallowedDatanodeException` | Y | none: exclude then include always leaves `isDisallowed`; no passing run exists | - | - | C (deterministic) | no |
| HDFS-2 14 | yes: BlockRecoveryWorker.java:129-183 (a local `null` is no error; an empty syncList means deleteBlock) | Y | **two** flips: the local replica absent AND an InterDatanodeProtocol FAULT. TestBlockRecovery2#testRecoveryTimeout has the topology but no later read (the fatal) | yes | - | C (nested 2, and no fatal in the test) | no |
| HDFS-2 15 | RBF RouterWebHdfsMethods.java:435 | Y | Router-to-ns1 report FAULT; the report is cached | yes | RBF | C (RBF; it recovers when ns1 returns, so it is not hard to recover) | no |
| HDFS-2 19, 20, 23, 31; HDFS-3 01, 04, 06 | yes (e.g. KeyManager.java:117, DFSInputStream:1018, FSNamesystem.java:3238) | weak | only negative or near-MAX operator values; the CONFIG domain hull excludes them | - | - | C (invalid or extreme operator input) | no |
| HDFS-2 25 | DiskBalancer.java:341 | weak | none: deterministic admin sequence, and the throw is the designed refusal | - | - | C | no |
| HDFS-3 C01, 02, 03, 07-10 | RBF | deterministic Router logic | none | - | RBF | C (C01 is not counted by the study) | no |
| HDFS-3 05 | hadoop-common AbstractDelegationTokenSecretManager.java:704 (via Router) | Y (in-memory key vs ZK, across Routers) | ZK store FAULT, plus Router A stopping before it re-stores the key (a second event) | yes | RBF + MiniKdc + ZK | C (no ZK door in the Hadoop tree; RBF; two events) | no |

## C. Known cases mapped to study items

| known case(s) | throw in our trees | study item |
| --- | --- | --- |
| hdfs-17897, hdfs-17899-bug1/2/3, hdfs-17967-pathA/B/C | dtx `BlockTokenSecretManager.java:582` retrieveDataEncryptionKey | **HDFS-11** (study :555) |
| hdfs-11741 | `~/hadoop-hdfs-11741` BlockTokenSecretManager.java:586, the same throw | **HDFS-11** |
| hdfs-17960 | dtx `FSImageFormatPBSnapshot.java:468` (the scaffold turned upstream's checkState into this throw) | **HDFS-52** (study :467) |
| hdfs-bugs-slowdisk-zero | bugs tree `RoundRobinVolumeChoosingPolicy.java:84` | none (not among the 53; HDFS-2 01 shares it) |

## D. The check list (owner ruling 2026-10-04: every study item with a cluster test; 51 kept, 13 and 36 dropped)

Scope classes are a starting set; RootDemand and scope growth add the rest. Shorthands:
- `ipc` = `common:org/apache/hadoop/ipc/Client`, `common:org/apache/hadoop/ipc/Server`.
- `qjm` = `hdfs:.../qjournal/server/Journal`, `hdfs:.../qjournal/server/JournalNodeRpcServer`,
  `hdfs:.../qjournal/client/IPCLoggerChannel`, `hdfs:.../qjournal/client/AsyncLoggerSet`,
  `hdfs:.../qjournal/client/QuorumJournalManager`, `hdfs:.../qjournal/client/QuorumOutputStream`,
  `hdfs:.../util/PersistentLongFile`, plus `ipc`.
- `bk` = system.sh's `blockkey_scope`.
- `dnbp` = `hdfs:.../server/datanode/{BlockRecoveryWorker,BPOfferService,BlockPoolManager,DataNode}`.
- `dnst` = `hdfs:.../server/datanode/{DataStorage,BlockPoolSliceStorage}`, `hdfs:.../server/common/{Storage,StorageInfo}`.
- `snap` = `hdfs:.../server/namenode/snapshot/{DirectorySnapshottableFeature,SnapshotManager}`.

### D.1 Checks with a plausible single counterfactual (run these first)

1. **hdfs-adhoc-10** (fit A). Journal.java:518 (`throw new IOException`, annotate). Workload TestQuorumJournalManager#testSingleWriter.
   Needs the MiniJournalCluster adapter (rule 1). Scope `qjm`.
   Chain: a FAULT on the request door of `startLogSegment(txid 1)` to one JN makes that JN's `Journal.startLogSegment` never
   run, so its `lastWriterEpoch` keeps the INITIAL 0. The quorum still succeeds, and the logger is not out of sync. The
   next `sendEdits` sends `journal(reqInfo.epoch=1)` (the writer epoch crosses the protobuf RequestInfo), and
   `checkWriteRequest` finds 1 != 0 and throws.
2. **hdfs-adhoc-11** (fit A). BlockTokenSecretManager.java:582, already marked: add `hdfs-adhoc-11` to the id list.
   Workload TestEncryptedTransfer#testEncryptedReadDefaultAlgorithmCipherSuite (pick one resolver parameter). Scope `bk`
   plus `hdfs:.../server/datanode/{BPOfferService,DataNode}` and `hdfs:.../server/blockmanagement/{DatanodeManager,HeartbeatManager}`.
   The mechanism is the regression cases': a lost KeyUpdateCommand after rotations. The upstream test has no rotation in
   its window, so it needs two NN key rotations (CLOCK in `HeartbeatManager.Monitor`, nested). Expect this one to be
   hard; the throw stays covered by the eight cases.
3. **hdfs-adhoc-12** (fit B). BlockTokenSecretManager.java:541 (`throw new InvalidToken`, annotate). Named workload
   TestEncryptedTransfer#testEncryptedReadDefaultAlgorithmCipherSuite. Under encryption the DEK check (:582) always
   fires first, so run it on an **encryption-off variant** of
   TestCausynthDataTransferRpcFailure#testReplicationAfterModeledKeyRefreshRpcFailure (one line:
   `DFS_ENCRYPT_DATA_TRANSFER_KEY=false`). Scope `bk` plus `hdfs:.../server/datanode/{BPOfferService,DataNode}`.
   Chain: a FAULT on the target DN's heartbeat response that carries the KeyUpdateCommand (the NN clears `needKeyUpdate`
   on send), and the workload then rotates again. The NN mints the transfer token with a key the DN never got, so in
   `DataXceiver.checkAccess`, then BTSM.checkAccess (6 args), then retrievePassword, `allKeys.get(keyId)==null` throws.
4. **hdfs-adhoc-52** (fit A, covered). FSImageFormatPBSnapshot.java:468, already marked: add the id. Workload
   TestFSImageWithSnapshot#testSaveLoadImage. Scope as hdfs-17960's case.sh. This test has neither a deletion nor an
   edit replay, so with it the fit is C. hdfs-17960 (TestOrderedSnapshotDeletion#testOrderedDeletionWithRestart) is
   the real witness of this throw.
5. **hdfs-adhoc-39** (fit B-). FSDirAppendOp.java:133 (`throw new RetriableException`, annotate). Workload
   TestFileAppend#testAppendTwice. Scope `hdfs:.../server/namenode/{FSDirAppendOp,FSNamesystem,FSDirWriteFileOp}`,
   `hdfs:.../server/blockmanagement/{BlockManager,BlockInfo}`, `ipc`.
   Chain: CONFIG `dfs.namenode.file.close.num-committed-allowed` set to 1 (minted at the `numCommittedAllowed` field
   reads) lets `completeFile` accept the COMMITTED last block. If the DN's IBR (COMMITTED to COMPLETE) is processed
   after the append's state read, the append throws. This needs the recorded IBR to land after the first `completeFile`
   attempt; otherwise the IBR pairing must move too.
6. **hdfs-adhoc-28 / 29 / 30** (fit C, B- only if the cluster's shutdown is inside the recording). BlockRecoveryWorker.java:565 / 604 / 609
   (`throw new IOException`, annotate). Workload TestBlockRecovery2#testRecoveryTimeout. Scope `dnbp`.
   The only writers of the BP map and of `bpServiceToActive` are `BlockPoolManager.remove` and `shutdownActor` at
   shutdown. A STATE re-pairing of a recovery read to those writes (allowed in any recorded order) is a real race of
   recovery against BP shutdown. Automatic mode ends the window's request when shutdown starts.

### D.2 The other study checks (kept per the ruling; fit C, reasons in part A)

| case id | site | marker change | workload | scope (start) |
| --- | --- | --- | --- | --- |
| hdfs-adhoc-01 | C/DFSInputStream.java:517 | annotate | TestPread#testPreadDFS | `client:.../{DFSInputStream,DFSClient}`, `hdfs:.../server/namenode/FSDirStatAndListingOp`, `hdfs:.../server/blockmanagement/BlockManager`, `ipc` |
| hdfs-adhoc-02 | C/DataStreamer.java:428 | annotate | TestClientProtocolForPipelineRecovery#testPipelineRecoveryOnRemoteDatanodeUpgrade | `client:.../{DataStreamer,DataStreamer$ErrorState,DFSOutputStream}` |
| hdfs-adhoc-03 | C/DataStreamer.java:1430 | assert rewrite | ...#testAddingDatanodeDuringClosing | `client:.../{DataStreamer,DFSOutputStream}` |
| hdfs-adhoc-04 | C/DataStreamer.java:973 | annotate | ...#testAddingDatanodeDuringClosing | same |
| hdfs-adhoc-05 | QuorumOutputStream.java:106 | assert rewrite | TestQuorumJournalManager#testSingleWriter (JN adapter) | `qjm` |
| hdfs-adhoc-06 | QuorumOutputStream.java:108 | assert rewrite | same | `qjm` |
| hdfs-adhoc-07 | Journal.java:926 | annotate | ...#testRecoverAfterIncompleteRecovery (JN adapter) | `qjm` |
| hdfs-adhoc-08 | Journal.java:487 | annotate | ...#testSingleWriter | `qjm` |
| hdfs-adhoc-09 | Journal.java:504 | checkArgument rewrite | ...#testSingleWriter | `qjm` |
| hdfs-adhoc-14 | BlockTokenSecretManager.java:441 | annotate | TestEncryptedTransfer#testEncryptedReadDefaultAlgorithmCipherSuite | `bk` |
| hdfs-adhoc-15 | BlockInfo.java:447 | checkState rewrite | TestBlockToken#testBlockTokenInLastLocatedBlockLegacy | `hdfs:.../server/blockmanagement/{BlockInfo,BlockManager}`, `hdfs:.../server/namenode/FSNamesystem` |
| hdfs-adhoc-16 | BlockInfo.java:428 | checkState rewrite | TestClientProtocolForPipelineRecovery#testUpdatePipeLineAfterDNReg | same |
| hdfs-adhoc-17 | BlockManager.java:2871 | checkArgument rewrite | TestAddStripedBlocks#testAddUCReplica | `.../blockmanagement/{BlockManager,BlockInfo,DatanodeStorageInfo}` |
| hdfs-adhoc-18 | DatanodeDescriptor.java:537 | assert rewrite | TestSecureAliasMap#testSecureConnectionToAliasMap (MiniKdc; evaluation uncertain) | `.../blockmanagement/{DatanodeDescriptor,ProvidedStorageMap,BlockManager}` |
| hdfs-adhoc-19 | BPOfferService.java:777 | assert rewrite | TestDFSFinalize#testFinalize | `dnbp`, `hdfs:.../server/datanode/BPServiceActor` |
| hdfs-adhoc-20 | BPOfferService.java:615 | assert rewrite | TestClientProtocolForPipelineRecovery#testPipelineRecoveryOnOOB | same |
| hdfs-adhoc-21 | BPServiceActor.java:290-293 | merge into one `throw new` | TestDFSInputStream#testSkipWithRemoteBlockReader; `recording_window=startup` | `hdfs:.../server/datanode/{BPServiceActor,DNConf}` |
| hdfs-adhoc-22 / 23 / 25 | BlockPoolSliceStorage.java:393 / 399 / 185 | annotate | TestDFSStartupVersions#testVersions (target a compatible combination) | `dnst` |
| hdfs-adhoc-24 | BlockPoolSliceStorage.java:421 | annotate | TestDFSUpgrade#testUpgrade (target a passing upgrade) | `dnst` |
| hdfs-adhoc-26 | BlockPoolSliceStorage.java:621 | annotate | TestDFSRollback#testRollback (target a passing rollback) | `dnst` |
| hdfs-adhoc-27 | BlockPoolSliceStorage.java:510 | assert rewrite | TestDatanodeLayoutUpgrade#testUpgradeToIdBasedLayout | `dnst` |
| hdfs-adhoc-31 | DataNode.java:1838 | annotate | TestDiskError#testDataTransferWhenBytesPerChecksumIsZero | `dnbp` |
| hdfs-adhoc-32 | DataNode.java:3826 | annotate | TestDeleteBlockPool#testDeleteBlockPool (target the post-refresh call) | `dnbp` |
| hdfs-adhoc-33 | DataStorage.java:259 | assert rewrite | TestDataNodeHotSwapVolumes#testAddOneNewVolume | `dnst`, `hdfs:.../server/datanode/fsdataset/impl/FsDatasetImpl` |
| hdfs-adhoc-34 / 35 | DataStorage.java:741 / 750 | annotate | TestDFSStartupVersions#testVersions (compatible combination) | `dnst` |
| hdfs-adhoc-37 | DataStorage.java:942 | annotate | TestDFSRollback#testRollback (passing rollback) | `dnst` |
| hdfs-adhoc-38 / 40 | FSDirAppendOp.java:122 / 139 | annotate | TestFileAppend#testAppendTwice | `.../server/namenode/{FSDirAppendOp,FSNamesystem}`, `.../blockmanagement/{BlockManager,DatanodeManager}` |
| hdfs-adhoc-41 | FSDirRenameOp.java:913 | annotate | TestRenameWithOrderedSnapshotDeletion#testRename (target a same-root rename) | `.../server/namenode/FSDirRenameOp`, `snap` |
| hdfs-adhoc-42 / 43 | FSDirTruncateOp.java:101 / 117 | annotate | TestFileTruncate#testTruncateTwiceTogether (43: only throwing evaluations) | `.../server/namenode/{FSDirTruncateOp,FSNamesystem}` |
| hdfs-adhoc-44 | FSDirTruncateOp.java:133 | annotate | TestFileTruncate#testTruncateFailure (target a smaller-length truncate) | same |
| hdfs-adhoc-45 | FSEditLog.java:1469 | checkState rewrite | TestEditLog#testSimpleEditLog | `.../server/namenode/FSEditLog` |
| hdfs-adhoc-46 | FSImage.java:184 | checkState rewrite | TestDFSInputStream#testSkipWithRemoteBlockReader; `recording_window=startup` | `.../server/namenode/{FSImage,FSNamesystem}` |
| hdfs-adhoc-47 | FSImageFormatPBINode.java:530 | checkState rewrite | TestSafeModeWithStripedFile#testStripedFile0 | `.../server/namenode/FSImageFormatPBINode` |
| hdfs-adhoc-48 | INodeDirectory.java:356 | checkState rewrite | TestRenameWithSnapshots#testRenameUndo_1 | `.../server/namenode/INodeDirectory` |
| hdfs-adhoc-49 / 50 | DirectorySnapshottableFeature.java:189 / 198 | annotate | TestSnapshot#testSnapshot | `snap` |
| hdfs-adhoc-51 | DirectorySnapshottableFeature.java:601 | checkState rewrite | TestSnapshot#testSnapshot | `snap` |
| hdfs-adhoc-53 | NamespacePrintVisitor.java:160 | checkState rewrite | TestFSImageWithSnapshot#testDoubleRename | `.../server/namenode/visitor/NamespacePrintVisitor`, `snap` |

Dropped, with hard reasons:
- **HDFS-13**: no production caller of the 4-argument Token `checkAccess` in our tree, and no cluster test.
- **HDFS-36**: no cluster test; the future-layout case hits the assert at DataStorage.java:731 first.

### D.3 bug_study addition

7. **hdfs-bugs-reencrypt-negative-sleep** (HDFS-2 09; fit B).
   - **Site.** H/server/namenode/EncryptionZoneManager.java:666 (`throw new IOException("Zone ... already submitted")`,
     annotate). It is not a study site. Mark it on `gc/hdfs-bugs`, or on dtx.
   - **Workload.** Self-written, e.g. `TestCausynthReencryptNegativeSleep`, built on TestReencryption's set-up
     (JavaKeyStoreProvider, 1 NN, 1 DN):
     - `dfs.namenode.reencrypt.batch.size=5` and `dfs.namenode.reencrypt.throttle.limit.handler.ratio=0.5`;
     - an encryption zone with 10 files, then rollKey and START;
     - a bounded wait (`CausynthCluster.WINDOW_WAIT_MS`) for Completed;
     - rollKey and START again, expecting success.
   - **Why self-written.** Every TestReencryption cluster test keeps the ratio at 1.0, which returns before the clock
     code. TestReencryptionHandler#testThrottle is a mocked unit test.
   - **Scope.** `hdfs:.../server/namenode/{ReencryptionHandler,ReencryptionHandler$ReencryptionPendingInodeIdCollector,FSTreeTraverser,ReencryptionUpdater,EncryptionZoneManager,FSDirEncryptionZoneOp}`,
     `client:.../protocol/{ReencryptionStatus,ZoneReencryptionStatus}`, `common:org/apache/hadoop/util/{StopWatch,Timer}`.
   - **Chain.** CLOCK skews nn0's `Timer.monotonicNowNanos` reads in the throttle's StopWatches so that
     `all1*0.5 < locked` and `locked/0.5 < all2`. Then `sleepMs < 0`, `Thread.sleep(long,int)` throws IAE,
     `ReencryptionHandler.run` returns on Throwable, and the zone stays Processing. The second START finds
     `hasRunningZone` true and throws. The state is hard to recover: no re-encryption runs until the NN restarts.
   - **Risk.** A STATE re-pairing of the second START's status read to the handler's `markZoneStarted` (Processing)
     write would be a benign early-START witness with the wrong mechanism. Acceptance requires CLOCK_SKEW with the
     throttle clocks in `movedRoots`.

Not added (reasons in part B): HDFS-2 01 (the witness is indistinguishable from the test hook), HDFS-2 11 (namespace
binary search), HDFS-2 14 (two flips), and every Router bug.

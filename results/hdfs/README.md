# HDFS on liftlab (system/hdfs-liftlab): the final .smt of every case

Each case's final formula (`<case>.smt2.gz`, gzip of the run's `schedule/final/candidate.smt2`) and its claim
(`<case>.claim.json`); `index.tsv` names the run each came from (`/bigtemp/vnr3ne/gc-out/hdfs-final/<run>`).
`system/hdfs-liftlab` is the one HDFS branch (owner 2026-10-26: it replaces `system/hdfs` and `system/hdfs1`): HBase's
engine with the Hadoop shim restored, from `system/hdfs-cloudlab` (now the tag `archive/system/hdfs-cloudlab`) with CloudLab's scheduling replaced by liftlab's
(the memory ledger and stream scheduler of `system/hbase`/`system/solr`). The tree is the Hadoop fork's
`graphchecker/hdfs-checks` 899c200cc8e (`-adhoc21` 25b4f1e531f for 21), the image vm-force12.

**Series H1** (2026-10-26/27, the owner: "测出45个hdfs adhoc check的time break down ... 每个独占集群"): every case but
hdfs-11741 ran alone, one at a time, on 12 lifts (lift02-06, 08-10, 12-15: lift11 is the control host, lift07 was down),
the head on lift10. Snapshots: `/u/vnr3ne/gc-run/hl-1` (e2a6aebf9) for the first 25 (17897 .. adhoc-26), `hl-2`
(f7c095f00: plus system/solr's four general fixes -- one task per exposed occurrence, a GROW plan within the task bound,
the report probe's budget and split bound -- none of which a case's verdict rests on) for the other 20. Tree set
`/bigtemp/vnr3ne/wt/hl-trees-1`. **All 45 verdicts equal CloudLab's final rounds** (`archive/system/hdfs-cloudlab`, F1-F7): the 9
named bugs but 11741 PASS (SAT, confirmed in the VM, native 10/10), 10 and 12 SAT (native 10/10), 52 a named bound (z3
did not decide its formula in its budget), the other 33 UNSAT_CLOSED. hdfs-11741 was not run on liftlab (owner); its row
is CloudLab's F7.

**Run one case:** `env GC_OUT=<out> GC_TREES=<tree set> CAUSYNTH_CUSTOM_JDK_HOME=<image> CASE_TIMEOUT_SECONDS=<budget>
tools/rounds/launch-run.sh <checkout of system/hdfs-liftlab> <case> <tag>`; **all, each alone:** `tools/rounds/run-series.sh
<round> experiments/hadoop/hdfs-cases.tsv system/hdfs-liftlab=<checkout>` ([../../docs/REPRODUCE.md](../../docs/REPRODUCE.md)
§1-§5). The table is `final-stats.py --order H1 --alone H1 --out /bigtemp/vnr3ne/gc-out/hdfs-final` over the run dirs:
seeding = PREFLIGHT..IMPORT and ZKKEYS (static passes, recording, seed replay); exploration = EXPLORE; compose+solver =
COMPOSE + SOLVE + DECIDE; other = CONFIRM + EMIT + REPRODUCE; regions / occurrences = the final closure.

The 45 alone: 62555 s (17.4 h) -- seeding 26126 s (42 %), exploration 32924 s (53 %), compose+solver 2775 s (4 %), other
534 s (1 %). The same 45 on CloudLab, concurrent: 139409 s. The long seedings (22-26, 34, 35, 37: 1600-2200 s) are their
whole-workload seed replays (`replay_timeout_s` 7200 for 24, 26, 37).

| case | run | mode | claim | mechanism | native | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |
| --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| hdfs-17897 | H1-17897 | alone | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 407 | 246 | 129 | 6 | 23 | - | 12 | 16 | 1 |
| hdfs-17899-bug1 | H1-17899-bug1 | alone | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 437 | 199 | 203 | 9 | 24 | - | 15 | 26 | 2 |
| hdfs-17899-bug2 | H1-17899-bug2 | alone | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 403 | 232 | 134 | 5 | 29 | - | 11 | 23 | 1 |
| hdfs-17899-bug3 | H1-17899-bug3 | alone | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 371 | 196 | 131 | 19 | 22 | - | 9 | 18 | 1 |
| hdfs-17960 | H1-17960 | alone | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 501 | 224 | 244 | 9 | 22 | - | 6 | 15 | 6 |
| hdfs-17967-pathA | H1-17967-pathA | alone | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 349 | 190 | 128 | 5 | 23 | - | 12 | 22 | 2 |
| hdfs-17967-pathB | H1-17967-pathB | alone | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 343 | 193 | 115 | 9 | 23 | - | 11 | 18 | 1 |
| hdfs-17967-pathC | H1-17967-pathC | alone | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 358 | 200 | 121 | 10 | 24 | - | 12 | 23 | 1 |
| hdfs-adhoc-05 | H1-adhoc-05 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 2030 | 329 | 1661 | 27 | 9 | - | 17 | 54 | 15 |
| hdfs-adhoc-06 | H1-adhoc-06 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 2019 | 331 | 1647 | 29 | 9 | - | 17 | 54 | 16 |
| hdfs-adhoc-08 | H1-adhoc-08 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 720 | 335 | 357 | 19 | 6 | - | 9 | 15 | 14 |
| hdfs-adhoc-09 | H1-adhoc-09 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 582 | 353 | 195 | 25 | 6 | - | 12 | 29 | 17 |
| hdfs-adhoc-10 | H1-adhoc-10 | alone | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 566 | 338 | 191 | 11 | 23 | - | 12 | 23 | 3 |
| hdfs-adhoc-11 | H1-adhoc-11 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 947 | 393 | 508 | 27 | 12 | - | 33 | 169 | 13 |
| hdfs-adhoc-12 | H1-adhoc-12 | alone | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 440 | 263 | 140 | 10 | 25 | - | 10 | 13 | 1 |
| hdfs-adhoc-14 | H1-adhoc-14 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1297 | 306 | 952 | 24 | 8 | - | 26 | 311 | 30 |
| hdfs-adhoc-15 | H1-adhoc-15 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1198 | 263 | 898 | 19 | 14 | - | 13 | 82 | 26 |
| hdfs-adhoc-16 | H1-adhoc-16 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1607 | 300 | 1261 | 23 | 17 | - | 18 | 166 | 27 |
| hdfs-adhoc-19 | H1-adhoc-19 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1011 | 531 | 402 | 71 | 4 | - | 9 | 12 | 18 |
| hdfs-adhoc-20 | H1-adhoc-20 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 646 | 366 | 241 | 27 | 8 | - | 21 | 93 | 8 |
| hdfs-adhoc-22 | H1-adhoc-22 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 2451 | 1655 | 764 | 19 | 6 | - | 21 | 222 | 8 |
| hdfs-adhoc-23 | H1-adhoc-23 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 2350 | 1601 | 719 | 17 | 6 | - | 21 | 221 | 8 |
| hdfs-adhoc-24 | H1-adhoc-24 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 2882 | 1796 | 1056 | 17 | 6 | - | 21 | 196 | 7 |
| hdfs-adhoc-25 | H1-adhoc-25 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 2467 | 1698 | 729 | 23 | 9 | - | 22 | 221 | 19 |
| hdfs-adhoc-26 | H1-adhoc-26 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 8082 | 2226 | 5805 | 33 | 9 | - | 21 | 218 | 22 |
| hdfs-adhoc-27 | H1-adhoc-27 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 956 | 547 | 381 | 17 | 6 | - | 18 | 94 | 7 |
| hdfs-adhoc-28 | H1-adhoc-28 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 484 | 335 | 134 | 9 | 4 | - | 3 | 3 | 6 |
| hdfs-adhoc-31 | H1-adhoc-31 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 392 | 263 | 114 | 9 | 4 | - | 2 | 2 | 4 |
| hdfs-adhoc-33 | H1-adhoc-33 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 604 | 388 | 196 | 12 | 6 | - | 3 | 3 | 9 |
| hdfs-adhoc-34 | H1-adhoc-34 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 2527 | 1716 | 778 | 18 | 6 | - | 21 | 224 | 7 |
| hdfs-adhoc-35 | H1-adhoc-35 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 3826 | 1733 | 2061 | 18 | 7 | - | 22 | 224 | 10 |
| hdfs-adhoc-37 | H1-adhoc-37 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 5429 | 2094 | 3284 | 34 | 9 | - | 21 | 216 | 16 |
| hdfs-adhoc-38 | H1-adhoc-38 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 460 | 312 | 128 | 13 | 4 | - | 14 | 81 | 10 |
| hdfs-adhoc-45 | H1-adhoc-45 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 374 | 285 | 78 | 6 | 4 | - | 4 | 4 | 4 |
| hdfs-adhoc-48 | H1-adhoc-48 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 398 | 245 | 132 | 14 | 4 | - | 7 | 43 | 16 |
| hdfs-adhoc-49 | H1-adhoc-49 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1243 | 308 | 892 | 30 | 9 | - | 11 | 86 | 21 |
| hdfs-adhoc-50 | H1-adhoc-50 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1366 | 419 | 906 | 28 | 9 | - | 11 | 88 | 30 |
| hdfs-adhoc-52 | H1-adhoc-52 | alone | RUN_DEFECT | NO_SUPPORTED_WITNESS | - | 3394 | 544 | 916 | 1902 | 23 | - | 9 | 179 | 91 |
| hdfs-bugs-slowdisk-zero | H1-bugs-slowdisk-zero | alone | SAT_CANDIDATE | STATE_PAIRING_FLIPPED | 10/10 | 402 | 184 | 180 | 10 | 25 | - | 5 | 6 | 4 |
| hdfs-11741 | CloudLab F7-11741 (not run on liftlab) | concurrent, CloudLab | SAT_CANDIDATE | CLOCK_SKEW | 0/10 | 18022 | 530 | 6091 | 1855 | 628 | 8918 (1) | 19 | 111 | 26 |
| hdfs-adhoc-07 | H1-adhoc-07 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 3408 | 404 | 2899 | 78 | 22 | - | 17 | 64 | 37 |
| hdfs-adhoc-21 | H1-adhoc-21 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 788 | 426 | 314 | 30 | 9 | - | 8 | 8 | 11 |
| hdfs-adhoc-29 | H1-adhoc-29 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 555 | 295 | 246 | 8 | 4 | - | 3 | 3 | 9 |
| hdfs-adhoc-30 | H1-adhoc-30 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 478 | 302 | 160 | 11 | 4 | - | 5 | 8 | 9 |
| hdfs-adhoc-39 | H1-adhoc-39 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 580 | 290 | 260 | 21 | 4 | - | 11 | 88 | 14 |
| hdfs-adhoc-40 | H1-adhoc-40 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 427 | 272 | 134 | 14 | 4 | - | 9 | 26 | 10 |

45 of 46 cases; wall 62555 s (17.4 h); seeding 26126, exploration 32924, compose+solver 2775, other 534, refuted claims 0 s

## Reading per case

Each reading was written on CloudLab's final runs (the F rounds); H1's verdict of every case equals it.

A SAT counts when CONFIRM confirmed it in the VM, its claim moved a root (or names the faultless mechanism), and REPRODUCE
ran natively (k/N); a named bug also needs its mandated mechanism (`report.py` PASS). An UNSAT counts at its FIXED_POINT
with z3 unsat on the file, no BLOCKING, and either substantive (`tools/analysis/vacuity.py`) or vacuous by construction
with the reason, read in the code (CHECKING trap 24; the guard readings are STATUS "HDFS checks", system/hdfs's). No case
found a new bug: every SAT is a named bug or a designed tolerance, as on system/hdfs.

- **hdfs-17897**: **PASS** (HDFS-17897): an IPC REQUEST fault on dn0's heartbeat (MARKER_FLIPPED), confirmed, 10/10 natively, control 0/10. Its earlier development runs (C3, DD1, L1) claimed faultless re-pairings first, 13 refuted by CONFIRM; the own-witness pass (agent D, merged before F1) claims the explored fault world.
- **hdfs-17899-bug1 / bug2 / bug3**: **PASS** (HDFS-17899): a heartbeat or registration fault loses nn0's block-key update, the DataNode misses the key (MARKER_FLIPPED), each 10/10. bug2's D5-1 claims were 8 refuted re-pairings; F4 claimed the fault world.
- **hdfs-17960**: **PASS** (HDFS-17960): the configuration root `dfs.namenode.snapshot.deletion.ordered` moved to false (MARKER_FLIPPED), 10/10.
- **hdfs-17967-pathA / pathB / pathC**: **PASS** (HDFS-17967): a key update lost with a failed heartbeat on each path (MARKER_FLIPPED), each 10/10.
- **hdfs-bugs-slowdisk-zero**: **PASS** (owner bug): STATE_PAIRING_FLIPPED with no root moved, 10/10 natively, control 0/10 (REPRODUCE plants the turn-counted order in a world that plants no root, c8d40a5d8).
- **hdfs-11741**: SAT, confirmed in the VM, the mandated mechanism (HDFS-11741, CLOCK_SKEW): on the merged DECIDE (F7) the explored clock world, nn0's key-manager clock (`updateKeys`, +20 h) and the balancer's (+30 h) among its moved clocks, is claimed in its own run on its own path's polarity, and CONFIRM's replay planted the clocks and reached the fatal ("required block key (keyID=...) doesn't exist"); F7's claim loop made five claims: three confirmed claims each reproduced 0 of 10 natively, the clocks planted but the plant's two ORDER rows on dn1's `removeExpiredKeys` never coming in a native run (control 0/10), and CONFIRM refuted one (STATE pairing: the run read `allKeys` from another writer than the model joined), so the first confirmed claim stands as the fallback (`final/unreproduced/0000`; the loop's 8918 s are the table's refuted-claims column). system/hdfs reproduced it 10/10 natively with the serial-number hook applied; here no SERIAL_NO root moves and that order is TODO. F1 on the earlier DECIDE ran out its budget (EXPLORATION_CUT) without claiming the explored clock world. F8 (one claim, the branch's declaration) was stopped in EXPLORE on the owner's call; F7 (agent D's DECIDE branch `hcF7d`) is its final row.
- **hdfs-adhoc-10**: SAT, confirmed, 10/10: a LOCAL_IO SYNC fault at jn0's `lastWriterEpoch` persist fails the writer's next `journal()` (`Journal.checkWriteRequest`:518). QJM's designed tolerance (a quorum of 2 of 3 goes on), not a new bug.
- **hdfs-adhoc-12**: SAT, confirmed, 10/10: the target DataNode's heartbeat REQUEST fault loses the KeyUpdateCommand, so a token under nn0's new key misses at `retrievePassword`:541; the known 17899/17967 class. F1 lost a heartbeat race (BLOCKING TOPOLOGY_DIVERGENCE, 8 re-pairing claims refuted by CONFIRM); F5 claimed the fault world.
- **hdfs-adhoc-05, 06**: UNSAT, vacuous by construction: every path's fatal arm literal false; `numReadyBytes` and `flushTo` read the same ready half of the double buffer on one thread under the stream's lock (06: `bufToSend` is allocated at `numReadyBytes`).
- **hdfs-adhoc-07**: UNSAT at world depth 0 (F7, 4901 s), z3 unsat, no defect; vacuous at that depth (every path's target phi literal false or missing): the fatal at `Journal.acceptRecovery` needs the QJM client to relay a `prepareRecovery` segment other than jn0's current one, which only nested faults produce. system/hdfs closed it substantively at depth 6 (11113 s on liftlab, 3451 leaves); on CloudLab F1 at depth 6 ran out its 43200 s budget (EXPLORATION_CUT, 3776 obligations cancelled), so 07 runs at the family's default depth (RULES: depth k for a bug case's k counterfactuals; 07 is a study check).
- **hdfs-adhoc-08, 09**: UNSAT, substantive (69 and 1 free paths): the request's epoch / committed txid are the single writer's own, the IPC-serial check rejects an out-of-order request first.
- **hdfs-adhoc-11**: UNSAT (F6, 2185 s), vacuous by construction (NO_ROOT): dn0 holds nn0's key from its registration and no rotation runs in the window. F1 diverged on a race (a heartbeat flip ending dn0's block pool before or after the client's first READ_BLOCK named dn0's second SASL connection a read retry or the checksum) and ran out 12 waves; the tree's TestEncryptedTransfer reads without block-acquire retries (f6) and 11 declares 24 waves.
- **hdfs-adhoc-14**: UNSAT, vacuous by construction (literal false): the DataNode recomputes the token's password from the key nn0 sent verbatim, over the same identifier fields. Its closure needs more than 128 tasks (declared 256).
- **hdfs-adhoc-15, 16**: UNSAT, substantive: no pairing nulls the block's under-construction feature before its commit. Their closures outgrew the default 64 tasks (the family declares 128).
- **hdfs-adhoc-19**: UNSAT, vacuous by construction (NO_ROOT): both block-pool ids are Strings fixed for the cluster (no tracked cells, STATUS defect 34).
- **hdfs-adhoc-20**: UNSAT, vacuous by construction (NO_ROOT): `lastActiveClaimTxId` is its INITIAL -1 at the first ACTIVE claim and the heartbeat's txid is non-negative; the roots only decide which tick claims.
- **hdfs-adhoc-21**: UNSAT, vacuous by construction (literal false): both versions are Strings no symbol tracks (TODO Scope B); its tree runs the handshake on a joined thread and trims the workload's skip loop.
- **hdfs-adhoc-22, 23, 25, 26, 34, 35, 37**: UNSAT, vacuous by construction (NO_ROOT): the compared namespace id / block pool id / cTime / layout / clusterID are read from VERSION files this cluster wrote itself before the window (IO rule, class C). 24, 26, 37 declare a 7200 s replay bound (their whole upgrade/rollback workloads replay in 2957-3687 s on CloudLab).
- **hdfs-adhoc-24**: UNSAT, substantive (10 of 11 paths free): the stored layout and cTime have the VERSION load and the upgrade's own stores as writers, all from one NameNode.
- **hdfs-adhoc-27**: UNSAT, substantive: `setNamespaceID` copies the NameNode's id into the storage before the upgrade.
- **hdfs-adhoc-28, 29**: UNSAT, vacuous by construction (NO_ROOT): the block-pool map is filled at DataNode start-up before the window and changed only at shutdown. On `f3` (the recovery's primary by DataNode UUID); F1 recovered on the other DataNode than the recording and reached no target.
- **hdfs-adhoc-30**: UNSAT, substantive (36 free paths): dn1's active-NameNode proxy is set at its first heartbeat and nothing in the window clears it (f3).
- **hdfs-adhoc-31**: UNSAT, vacuous by construction (NO_ROOT): the same block-pool map as 28.
- **hdfs-adhoc-33**: UNSAT, substantive: the builder's block pool ids are the keys the same DataStorage registered under its lock.
- **hdfs-adhoc-38**: UNSAT, vacuous by construction (NO_ROOT): LAZY_PERSIST's policy id is the constant 15.
- **hdfs-adhoc-39, 40**: UNSAT resting on open arms their flips closed (vacuity.py): 39's `getBlockUCState()` arm (1 refuted world), 40's `isSufficientlyReplicated` arm (1 refuted world, 15 paths sharing it): under each flip the workload's earlier step fails, so the append's occurrence never runs (STATUS rows, CHECKING traps 5, 18).
- **hdfs-adhoc-45**: UNSAT, vacuous by construction (NO_ROOT): the edit log's `state` is set and read by one thread under its monitor.
- **hdfs-adhoc-48**: UNSAT, vacuous by construction: an identity compare of references the renaming thread took itself under the write lock states no term (VM.md §5.2).
- **hdfs-adhoc-49**: UNSAT, vacuous by construction (NO_ROOT): the snapshot count is the list's own under the write lock; the test never exceeds the quota.
- **hdfs-adhoc-50**: UNSAT, vacuous by construction (literal false): the duplicate-name search compares the test's distinct constant names; on HBase's engine the guard decides with no term (system/hdfs: 14 writer arms of the sorted list).
- **hdfs-adhoc-52**: the run row is RUN_DEFECT (F7, 6285 s) on one BLOCKING DECLARATION_MISSING `formula:timeout`: the composer's own whole ask ran out of memory (220 s) and its 128 valuations, each timing out path by path, used the decide budget; the exported formula is unsat on the file (z3, both arithmetic engines, 35 s), at the FIXED_POINT with no other defect, and substantive (369 of 369 paths free over the IPC response roots): the saver counts the snapshots it writes against SnapshotManager's count under the namesystem lock, and this workload deletes no snapshot twice. Its tree sizes a LightWeightGSet for 64 MB (F1 lost 225 replays to stalls walking a 33M-bucket INodeMap). The composer's one-shot memory is TODO 11.

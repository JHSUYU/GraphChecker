# HDFS on HBase's engine, on CloudLab: the final .smt of every case

Each case's final formula (`<case>.smt2.gz`, gzip of the run's `schedule/final/candidate.smt2`) and its claim
(`<case>.claim.json`); `index.tsv` names the run each came from (`/bulk/gc-out/hdfs-final/<run>` on the cluster). Every
case ran on `system/hdfs-cloudlab` (HBase's engine with the Hadoop shim restored) on CloudLab's node0-node4 (Xeon E5-2660
v2, 40 logical cores and 251 GB each), image `/bulk/vm/hbase/j2sdk-image`, every round concurrent with the others (8-13
campaigns at once, load 25-55 on 40 CPUs), so no case ran alone.

| round | snapshot (commit) | tree set (fork commit of `hadoop-hdfs-study-r7`) | cases |
| --- | --- | --- | --- |
| F1 | `hcF1` (9c1bbe157) | `f1` (75cb90e9dfe; 21: 9478e60313f; 11741: 6c86fca9a2b) | the final series, every case, 8 lanes then 5 more |
| F2 | `hcF2` (453dffd7c), `hcF2b` (614d75631), `hcF2c` (654456ced) | `f1` | 16, 24, 26, 37; 14; 15 |
| F3 | `hcF2` | `f3` (0d2b473db63: a block recovery's primary by DataNode UUID) | 28, 29, 30 |
| F4 | `hcF2c` (654456ced) | `f1` | the 11 cases F1 had not started at 11:58 (same engine, the family's 128 tasks) |
| F5 | `hcF5` (f6d277c51) | `f1`; 52 on `f5` (57e091c8af6: a LightWeightGSet sized for 64 MB) | 12, 14 (256 tasks), 52 |
| F6 | `hcF6` (55141de02) | `f6` (899c200cc8e: TestEncryptedTransfer without block-acquire retries) | 11 (24 waves) |
| F7 | `hcF7a` (94fce7127); `hcF7d` (b6408caa6, agent D's DECIDE branch); `hcF7` (e0deb39c1, the merge) | `f6`; 11741 on `f1` | 07 (depth 0); 11741; 52 |
| F8 | `hcF8` (741d1fdea: the merge plus 11741's one claim) | `f1` | 11741, stopped in EXPLORE on the owner's call (2026-10-25); no row |

F1-F7a run one engine: between 9c1bbe157 and 94fce7127 only case declarations (`experiments/hadoop/*/case.sh`,
`hdfs-cases.tsv`) and the reading tool `tools/analysis/vacuity.py` changed. F7's 11741 and 52 add DECIDE's last changes
(agent D, merged as e0deb39c1 after three independent reviews: the recording asked first, an explored clock world as the
last rank claimed in its own run on its own path's polarity, the free formula asked whole first where no run observed
the fatal); offline on the final corpora of 17897, 17899-bug2, 17967-pathB, 17960, adhoc-10, adhoc-09 and adhoc-16 they
leave every claim unchanged. A case's later round supersedes its earlier
one (`collect-results.sh F7,F6,F5,F4,F3,F2,F1`); the superseded runs stay in `/bulk/gc-out/hdfs-final` (F1-12's eight claims
refuted by CONFIRM, F1-52's stalled replays, F1-14/15/16's truncated closures, F1-24/26/37's replays past 2400 s,
F1-28/29's recovery on the other DataNode, F1-11's divergence) as the evidence for each declaration or workaround
(STATUS "Per-system surface", LESSONS §10).

**Run one case:** `cd <snapshot> && env GC_OUT=<out> GC_TREES=<tree set> CAUSYNTH_CUSTOM_JDK_HOME=<image> CASES=<case>
CASE_TIMEOUT_SECONDS=<budget> PRUNE=0 tools/rounds/launch-round.sh <snapshot> <ROUND>`; **all:** `tools/rounds/run-series.sh
<round> experiments/hadoop/hdfs-cases.tsv system/hdfs-cloudlab=<snapshot>`, or lanes of it side by side
([../../docs/REPRODUCE.md](../../docs/REPRODUCE.md) §9). The table is `final-stats.py --order F7,F6,F5,F4,F3,F2,F1` over the
run dirs: seeding = PREFLIGHT..IMPORT and ZKKEYS (static passes, recording, seed replay); exploration = EXPLORE;
compose+solver = COMPOSE + SOLVE + DECIDE; other = CONFIRM + EMIT + REPRODUCE; regions / occurrences = the final closure.

| case | run | mode | claim | mechanism | native | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |
| --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| hdfs-17897 | F1-17897 | concurrent | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 960 | 380 | 525 | 4 | 45 | - | 12 | 19 | 10 |
| hdfs-17899-bug1 | F4-17899-bug1 | concurrent | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 1020 | 388 | 540 | 4 | 83 | - | 15 | 30 | 4 |
| hdfs-17899-bug2 | F4-17899-bug2 | concurrent | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 1179 | 487 | 626 | 4 | 59 | - | 11 | 29 | 14 |
| hdfs-17899-bug3 | F1-17899-bug3 | concurrent | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 1428 | 479 | 867 | 4 | 73 | - | 9 | 21 | 23 |
| hdfs-17960 | F1-17960 | concurrent | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 1299 | 578 | 624 | 4 | 89 | - | 6 | 15 | 12 |
| hdfs-17967-pathA | F1-17967-pathA | concurrent | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 1056 | 402 | 576 | 4 | 69 | - | 12 | 23 | 10 |
| hdfs-17967-pathB | F4-17967-pathB | concurrent | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 645 | 377 | 220 | 3 | 40 | - | 11 | 18 | 1 |
| hdfs-17967-pathC | F4-17967-pathC | concurrent | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 959 | 401 | 510 | 4 | 40 | - | 12 | 24 | 8 |
| hdfs-adhoc-05 | F1-adhoc-05 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 3582 | 737 | 2769 | 51 | 18 | - | 17 | 54 | 61 |
| hdfs-adhoc-06 | F4-adhoc-06 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 2867 | 583 | 2209 | 52 | 16 | - | 17 | 54 | 70 |
| hdfs-adhoc-08 | F1-adhoc-08 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 2742 | 500 | 2204 | 20 | 14 | - | 9 | 15 | 39 |
| hdfs-adhoc-09 | F1-adhoc-09 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 2422 | 541 | 1837 | 28 | 11 | - | 12 | 29 | 61 |
| hdfs-adhoc-10 | F1-adhoc-10 | concurrent | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 1201 | 621 | 530 | 4 | 42 | - | 12 | 23 | 2 |
| hdfs-adhoc-11 | F6-adhoc-11 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 2185 | 923 | 1179 | 37 | 17 | - | 33 | 175 | 37 |
| hdfs-adhoc-12 | F5-adhoc-12 | concurrent | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 1262 | 636 | 516 | 4 | 101 | - | 10 | 15 | 7 |
| hdfs-adhoc-14 | F5-adhoc-14 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 3443 | 694 | 2691 | 28 | 15 | - | 26 | 168 | 77 |
| hdfs-adhoc-15 | F2-adhoc-15 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1901 | 635 | 1218 | 12 | 27 | - | 13 | 89 | 28 |
| hdfs-adhoc-16 | F2-adhoc-16 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 6316 | 666 | 5503 | 45 | 86 | - | 18 | 183 | 119 |
| hdfs-adhoc-19 | F1-adhoc-19 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 2671 | 853 | 1778 | 20 | 16 | - | 9 | 13 | 41 |
| hdfs-adhoc-20 | F1-adhoc-20 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1778 | 924 | 808 | 28 | 9 | - | 21 | 99 | 13 |
| hdfs-adhoc-22 | F1-adhoc-22 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 4764 | 2818 | 1900 | 20 | 10 | - | 21 | 230 | 7 |
| hdfs-adhoc-23 | F1-adhoc-23 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 3239 | 2814 | 393 | 9 | 7 | - | 21 | 230 | 7 |
| hdfs-adhoc-24 | F2-adhoc-24 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 10374 | 4060 | 6238 | 43 | 16 | - | 21 | 206 | 13 |
| hdfs-adhoc-25 | F1-adhoc-25 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 5130 | 3004 | 2048 | 43 | 15 | - | 22 | 234 | 25 |
| hdfs-adhoc-26 | F2-adhoc-26 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 10897 | 4620 | 6219 | 27 | 15 | - | 21 | 225 | 9 |
| hdfs-adhoc-27 | F1-adhoc-27 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 3077 | 1493 | 1534 | 22 | 14 | - | 18 | 102 | 7 |
| hdfs-adhoc-28 | F3-adhoc-28 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1606 | 687 | 889 | 17 | 9 | - | 3 | 3 | 19 |
| hdfs-adhoc-31 | F4-adhoc-31 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 941 | 626 | 301 | 6 | 5 | - | 2 | 2 | 6 |
| hdfs-adhoc-33 | F1-adhoc-33 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 2178 | 945 | 1183 | 22 | 20 | - | 3 | 3 | 22 |
| hdfs-adhoc-34 | F1-adhoc-34 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 5050 | 2794 | 2196 | 28 | 15 | - | 21 | 229 | 8 |
| hdfs-adhoc-35 | F1-adhoc-35 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 9041 | 2892 | 6101 | 20 | 10 | - | 22 | 233 | 10 |
| hdfs-adhoc-37 | F2-adhoc-37 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 13268 | 4749 | 8460 | 28 | 15 | - | 21 | 231 | 9 |
| hdfs-adhoc-38 | F4-adhoc-38 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1403 | 720 | 650 | 10 | 15 | - | 14 | 83 | 27 |
| hdfs-adhoc-45 | F4-adhoc-45 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 862 | 650 | 198 | 5 | 5 | - | 4 | 4 | 4 |
| hdfs-adhoc-48 | F4-adhoc-48 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1123 | 608 | 486 | 15 | 8 | - | 7 | 43 | 44 |
| hdfs-adhoc-49 | F1-adhoc-49 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1699 | 506 | 1138 | 35 | 12 | - | 11 | 86 | 51 |
| hdfs-adhoc-50 | F1-adhoc-50 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 4816 | 841 | 3891 | 53 | 18 | - | 11 | 88 | 73 |
| hdfs-adhoc-52 | F7-adhoc-52 | concurrent | RUN_DEFECT | NO_SUPPORTED_WITNESS | - | 6285 | 848 | 3390 | 1989 | 43 | - | 9 | 215 | 123 |
| hdfs-bugs-slowdisk-zero | F4-bugs-slowdisk-zero | concurrent | SAT_CANDIDATE | STATE_PAIRING_FLIPPED | 10/10 | 926 | 318 | 516 | 6 | 82 | - | 5 | 6 | 5 |
| hdfs-11741 | F7-11741 | concurrent | SAT_CANDIDATE | CLOCK_SKEW | 0/10 | 18022 | 530 | 6091 | 1855 | 628 | 8918 (1) | 19 | 111 | 26 |
| hdfs-adhoc-07 | F7-adhoc-07 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 4901 | 638 | 3977 | 123 | 153 | - | 17 | 64 | 75 |
| hdfs-adhoc-21 | F1-adhoc-21 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1318 | 757 | 502 | 43 | 12 | - | 8 | 8 | 10 |
| hdfs-adhoc-29 | F3-adhoc-29 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1423 | 681 | 707 | 15 | 15 | - | 3 | 3 | 15 |
| hdfs-adhoc-30 | F3-adhoc-30 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1843 | 794 | 1003 | 27 | 14 | - | 5 | 9 | 31 |
| hdfs-adhoc-39 | F1-adhoc-39 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1398 | 631 | 730 | 19 | 9 | - | 11 | 97 | 39 |
| hdfs-adhoc-40 | F4-adhoc-40 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 931 | 568 | 335 | 14 | 8 | - | 9 | 26 | 18 |

46 of 46 cases; wall 157431 s (43.7 h); seeding 52397, exploration 88806, compose+solver 4854, other 2043, refuted claims 8918 s

## Reading per case

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

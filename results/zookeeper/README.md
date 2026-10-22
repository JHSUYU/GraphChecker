# ZooKeeper: the final .smt of every case

Each case's final formula is `<case>.smt2.gz`, the gzip of the run's `schedule/final/candidate.smt2`. Its claim is
`<case>.claim.json`. `index.tsv` names the run each came from (`/bigtemp/vnr3ne/gc-out/zookeeper-final/<run>`).

**5 of the 6 bug checks PASS, and 4 of the owner's 5 bugs.** The owner's five are quota-init, election-offer,
container-reuse, trunc-sync (ZOOKEEPER-5094) and observer-master (ZOOKEEPER-5088). retry-seq-quota (bug_study #32) is
the sixth bug check. trunc-sync is "not detected" (owner 2026-10-21; TODO ZooKeeper 1).

The runs used `system/zookeeper` snapshots `zk-int-12` (d4fbcd97c; F1B, F1S, F1C, F1D) and `zk-int-13` (d73c28302: the
same engine plus D's COMPOSE fix, heldOwn and the onFatalPath FLIP; F1E, F1F, F2*). The tree is
`graphchecker/zookeeper-checks` 2b6e17bf8 (tree set zk-int-trees-11); 04 and 13 ran on zk-int-trees-12 (`gc/zk-hostseed`
51b213562, the RO client's constant host seed). The image is vm-force13. int-13 differs from int-12 only in COMPOSE;
an offline A/B over every final run is identical except om, so the int-12 runs stand.

The owner's rule (2026-10-20/21, as for HBase): runs under 30 min are kept from the concurrent rounds (F1*); every longer
case ran again alone on all 14 hosts (F2B bugs, F2S study checks). Every case's configuration is in
`experiments/zookeeper/*/case.sh`, `zk-adhoc/checks.tsv` and `workflow.properties`.

**Run one case:** `CAUSYNTH_CUSTOM_JDK_HOME=<image> GC_TREES=<tree set> tools/rounds/launch-run.sh <snapshot of
system/zookeeper> <case> <tag>` (OPERATIONS.md §10; build the tree set with `GC_TREES=<dir> ZOOKEEPER_MAVEN_REPO=<repo>
experiments/zookeeper/prepare-trees.sh`). **Run all:** `tools/rounds/run-series.sh <round>
experiments/zookeeper/zookeeper-cases.tsv system/zookeeper=<snapshot>`.

The table below is `final-stats.py` over the run dirs. Its columns:
- seeding: PREFLIGHT..IMPORT and ZKKEYS (static passes, recording, seed replay)
- exploration: EXPLORE
- compose+solver: COMPOSE + SOLVE + DECIDE
- other: CONFIRM + EMIT + REPRODUCE
- refuted claims: the compose and CONFIRM of the claims CONFIRM refuted before the last one (their number in brackets);
  `stage_metrics.tsv` times only the last claim, so this is the wall the stages leave uncovered (02: 3 claims, cont: 1)
- regions / occurrences: the final closure (distinct regions; its execution-plan rows); rounds: EXPLORE's generations

The columns sum to the wall but for 2-6 s of stage start-up per case (45 s in all). Of the 4.8 h, exploration takes 59 %,
seeding 24 %, the refuted claims 8 %, other 6 % and compose+solver 3.5 %; z3 runs inside COMPOSE (SOLVE
itself is under 1 s per case).

| case | run | mode | claim | mechanism | native | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |
| --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| zk-adhoc-01 | F2S-01 | alone | SAT_UNCONFIRMED | CLOCK_SKEW | - | 1418 | 149 | 842 | 94 | 330 | - | 9 | 38 | 27 |
| zk-adhoc-02 | F2S-02 | alone | SAT_UNCONFIRMED | STATE_PAIRING_FLIPPED | - | 3548 | 288 | 1626 | 62 | 339 | 1233 (3) | 10 | 168 | 27 |
| zk-adhoc-03 | F1C-03 | concurrent | SAT_CANDIDATE | CLOCK_SKEW | 4/10 | 423 | 146 | 194 | 64 | 17 | - | 10 | 36 | 5 |
| zk-adhoc-04 | F1E-04 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1212 | 331 | 856 | 17 | 6 | - | 6 | 13 | 13 |
| zk-adhoc-06 | F1S-06 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 964 | 313 | 565 | 73 | 10 | - | 23 | 55 | 19 |
| zk-adhoc-07 | F1S-07 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 829 | 403 | 407 | 10 | 7 | - | 8 | 31 | 6 |
| zk-adhoc-10 | F1S-10 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1016 | 328 | 670 | 7 | 6 | - | 4 | 157 | 10 |
| zk-adhoc-11 | F2S-11 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 2335 | 552 | 1646 | 55 | 78 | - | 7 | 78 | 38 |
| zk-adhoc-12 | F1C-12 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 996 | 208 | 741 | 36 | 8 | - | 6 | 16 | 23 |
| zk-adhoc-13 | F1E-13 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 229 | 166 | 48 | 9 | 4 | - | 9 | 20 | 3 |
| zk-bugs-quota-init | F1C-quota | concurrent | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 270 | 155 | 86 | 4 | 23 | - | 6 | 46 | 1 |
| zk-bugs-election-offer | F2B-offer | alone | SAT_CANDIDATE | STATE_PAIRING_FLIPPED | 10/10 | 256 | 132 | 54 | 26 | 41 | - | 4 | 39 | 8 |
| zk-bugs-container-reuse | F1B-cont | concurrent | SAT_CANDIDATE | STATE_PAIRING_FLIPPED | 10/10 | 572 | 201 | 70 | 79 | 70 | 153 (1) | 6 | 26 | 3 |
| zk-bugs-retry-seq-quota | F1C-rseq | concurrent | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 350 | 175 | 147 | 6 | 19 | - | 8 | 69 | 6 |
| zk-bugs-trunc-sync | F2B-trunc | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 2420 | 244 | 2053 | 41 | 76 | - | 8 | 46 | 84 |
| zk-bugs-observer-master | F1F-om | concurrent | SAT_CANDIDATE | STATE_PAIRING_FLIPPED | 4/10 | 494 | 282 | 171 | 15 | 20 | - | 12 | 19 | 6 |

16 of 16 cases; wall 17332 s (4.8 h); seeding 4073, exploration 10176, compose+solver 598, other 1054, refuted claims 1386 s

## Reading per case

- **zk-bugs-quota-init**: **PASS** (owner bug: the partial quota). A ZOOKEEPER WRITE fault on createQuota's limit-node
  create, which is committed but whose reply is lost. The retry takes the update branch and reads a stat node that was never
  created, so FinalRequestProcessor throws NoNode at the retry's getData. Native 10/10.
- **zk-bugs-election-offer**: **PASS** (owner bug: the orphaned election offer). No fault. The election thread's
  toLeaderOffers getData of a competitor's offer joins that competitor's delete, so `start()` fails without deleting its
  own offer. Native 10/10.
- **zk-bugs-container-reuse**: **PASS** (owner bug: the container cleanup). On the widened-window workload, the client's
  getData pairs with the cleanup's remove of the replacement node. Native 10/10.
- **zk-bugs-retry-seq-quota**: **PASS** (bug_study #32, the sixth bug check). A ZOOKEEPER fault on the first sequential
  create's reply makes ZooKeeperRetry create again, and the hard count quota refuses the next create. Native 10/10.
- **zk-bugs-trunc-sync**: **not detected** (ZOOKEEPER-5094, PR 2459; owner 2026-10-21). UNSAT_CLOSED at world depth 1.
  The follower's second life's NEWLEADER FAULT world was reached and admitted (ZB15), but life 2 is recorded only in the
  re-run of a flipped world, and that flip (an IO fault on life 3's log open) stops life 3 before the replay that would
  throw. TODO ZooKeeper 1 holds the designed fix.
- **zk-bugs-observer-master**: **PASS** (ZOOKEEPER-5088, PR 2454). A pairing in the observer's sync: the observer-master
  follower's pending proposal never reaches the OM's queue, no INFORM is sent, and the observer throws at
  ZKDatabase:341. Native 4/10 (F1F-om on zk-int-13).
- **zk-adhoc-01**: SAT_UNCONFIRMED, the normal FP filter. The claim is refused in its confirmation replay (NOT_ADMITTED):
  the replay published no root mint row for the expirer turn's clock root REGION.a45a7fec..in.dd072c9c that the claim
  moves. Earlier runs ended at the leader's racing ACK hand-overs (TODO ZooKeeper 8). F2S-01, alone, 1418 s.
- **zk-adhoc-02**: SAT_UNCONFIRMED, the normal FP filter. Every STATE_PAIRING_FLIPPED claim (a LearnerHandler's `Request.setOwner`
  paired after Prep's `validateCreateRequest` getOwner) is refuted by CONFIRM's ORDER: that getOwner never exits while the
  setOwner is held. F2S-02, alone, 3548 s.
- **zk-adhoc-03**: SAT CLOCK_SKEW, confirmed in the VM. The leader's clock at SESSION_EXPIRY#1 jumps, so the expirer
  expires the session and setOwner throws SessionExpired. Native 4/10 (control 0/10).
- **zk-adhoc-04**: UNSAT_CLOSED, substantive (7 of 7 paths free, no root), correct for its workload (B's host seed and
  probe hold).
- **zk-adhoc-06**: UNSAT_CLOSED, substantive. ACKEPOCH's summary and the leader's both come from fresh disks; the one
  re-pairable read offers only fresh-disk writers.
- **zk-adhoc-07**: UNSAT_CLOSED, substantive. LEADERINFO's envelope epoch is a constant at the learner, and no explored
  writer of acceptedEpoch exceeds the proposed epoch.
- **zk-adhoc-10**: UNSAT, vacuous by construction (class C). The head check reads the envelope zxid
  (QuorumPacket.getZxid) on F's own thread, and no root carries it.
- **zk-adhoc-11**: UNSAT, vacuous by construction (class C, IO rule). The epoch files and the replayed log are file
  state no symbol carries. F2S-11, alone, 2335 s.
- **zk-adhoc-12**: UNSAT_CLOSED, substantive. On a fresh ensemble both epochs take the same expression of each writer,
  so the strict `<` cannot hold.
- **zk-adhoc-13**: UNSAT_CLOSED, substantive (1 of 2 paths free). The global-session map read is offered another writer,
  and none expires the session in time.

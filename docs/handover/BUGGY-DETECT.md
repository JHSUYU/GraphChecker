# Old bugs that make an ad hoc check fail, put back on today's trees (the four systems)

Standard (owner 2026-10-26): a bug counts only if GraphChecker's witness fires the point's OWN declared throw. It is
detected when the formula is SAT, CONFIRM realizes the witness in the VM, native REPRODUCE reproduces it k/N with the
control 0/N, and report.py passes. Where the fixed code also reaches the throw in the witness world, the case README
says so ("caveat"). A check truly beyond GraphChecker's capability is not forced (owner 2026-10-26).

Source: the owner's list of 73 old bugs. 21 make an ad hoc check's own throw fail: HDFS-6325 is excluded (its point's
guard IS the fix), HDFS-17897, -17899, -17967 and SOLR-18406 are existing GraphChecker bug checks, so 16 were put back by
hand on each system's current tree, one fork branch each (`graphchecker/<sys>-bug-<jira>`). Four more HDFS bugs
(15590, 16689, 11890, 13145) were dropped by the owner: their witnesses fire another throw or none.

The first runs were on CloudLab (2026-10-25..27, the run names in the table; that cluster is no longer used). Round B1
(2026-10-28) ran every runnable case again on liftlab, the cases beside each other on the workers
(`/bigtemp/vnr3ne/gc-out/buggy-detect/accept-B1-<case>`). Round E1 (2026-10-29, the owner) ran them once more, each
case alone on the 11 workers, for the time breakdown (`/bigtemp/vnr3ne/gc-out/buggy-detect-exclusive/accept-E1-<case>`;
"Time" below). Each branch's `results/<sys>-buggy/` holds E1's formulas, claims and time table, B1's table below it.

| system | bug | point | CloudLab, 2026-10-26 | B1, liftlab, 2026-10-28 | E1, liftlab, each alone, 2026-10-29 | mechanism | caveat |
| --- | --- | --- | --- | --- | --- | --- | --- |
| HDFS | HDFS-11741 | hdfs-adhoc-11 | **SAT, native 10/10** (B11741b) | **SAT, native 10/10**, control 0/10, 884 s | **SAT, native 10/10**, control 0/10, 1123 s | CLOCK_SKEW, nn0 + target-dn clocks | the fix checks the Balancer's own clock, unmoved |
| HDFS | HDFS-17383 | hdfs-adhoc-12 | **SAT, native 10/10** (B17383a) | **SAT, native 10/10**, control 0/10, 572 s | **SAT, native 10/10**, control 0/10, 530 s | lost heartbeat reply from the standby | -- |
| HDFS | HDFS-12931 | hdfs-adhoc-11 | **SAT, native 10/10** (B12931a) | **SAT, native 10/10**, control 0/10, 368 s | **SAT, native 10/10**, control 0/10, 400 s | lost key-update heartbeat reply | the DataNode throws first on the fixed code too |
| HDFS | HDFS-5766 | hdfs-adhoc-11 | **SAT, native 10/10** (B5766a) | **SAT, native 10/10**, control 0/10, 516 s | **SAT, native 10/10**, control 0/10, 391 s | lost key-update heartbeat request | same |
| HDFS | HDFS-10609 | hdfs-adhoc-11 | **SAT, native 10/10** (B10609a) | **SAT, native 10/10**, control 0/10, 506 s | **SAT, native 10/10**, control 0/10, 556 s | lost key-update heartbeat request | same |
| HDFS | HDFS-14075 | hdfs-adhoc-45 | **SAT, native 10/10** (B14075c) | **SAT, native 10/10**, control 0/10, 463 s | **SAT, native 10/10**, control 0/10, 490 s | LOCAL_IO fault on roll 1's edits open | -- (the fix terminates the NN) |
| HDFS | HDFS-14311 | hdfs-adhoc-24 | not detected: a capability limit (B14311a-f) | not detected, as on CloudLab: formula UNSAT_CLOSED and substantive (vacuity.py: 9 paths, 8 free; 1 of 5 reads offered another writer), report.py FAIL as expected, 2333 s | not detected, as before: UNSAT_CLOSED and substantive (vacuity.py: 9 paths, 8 free; 1 of 5 reads offered another writer), report.py FAIL as expected, 2521 s | the intended STATE re-pairing (vol2's layoutVersion read <- vol1's upgrade-task write) is never realized: the engine offers the reader's own task, created after the read, as a concurrent writer, and CONFIRM's pairing hold sits after the reads that decide the guard | the only CloudLab witness (B14311d) was the race by timing, native 0/10 |
| HBase | HBASE-15039 | hbase-adhoc-34 | **SAT, native 10/10** (HB15039b) | **SAT, native 10/10**, control 0/10, 755 s | **SAT, native 8/10**, control 0/10, 850 s | STATE: the watcher's addKey after the validation | -- (the fix refreshes) |
| HBase | HBASE-20642 | hbase-adhoc-04 | **SAT, native 10/10 by IDENTITY §9 shape** (HB20642f; exact id 0/10, control 0/10; accepted by the owner 2026-10-27) | **SAT, native by shape 10/10** (exact id 0/10), control 0/10, 1393 s (681 s of them 5 claims CONFIRM refuted first) | **SAT, native by shape 10/10** (exact id 0/10), control 0/10, 1504 s (819 s of them 7 claims CONFIRM refuted first) | lost DisableTable reply, retry with a new nonce | the retry's handler has no recorded address; native runs answer it by the rule CONFIRM uses, decided by arrival order |
| HBase | HBASE-28533 | hbase-adhoc-15 | not reachable on today's code (no run) | no run (put back only) | no run | the merge constructor's checkOnline refuses first | the lowest world reaching :507 never runs the buggy rollback |
| ZooKeeper | ZOOKEEPER-710 | zk-adhoc-02 | **SAT, native 10/10** (ZB6) | **SAT, native 10/10**, control 0/10, 308 s | **SAT, native 10/10**, control 0/10, 311 s | STATE: the owner read paired with the takeover's REVALIDATE | the fixed-tree control is also SAT 10/10 (plain world) |
| ZooKeeper | ZOOKEEPER-2886 | zk-adhoc-02 | **SAT, native 10/10** (ZB6) | **SAT, native 10/10**, control 0/10, 294 s | **SAT, native 10/10**, control 0/10, 300 s | same, multi-only | same |
| Solr | SOLR-9440 | solr-adhoc-31 | **SAT, native 10/10** (S9440b) | **SAT, native 6/10**, control 0/10, 907 s | **SAT, native 10/10**, control 0/10, 576 s | ZooKeeper SessionExpired on node1's leader-election create during the core CREATE | -- (the fixed code evicts the frozen view) |
| Solr | SOLR-6101 | solr-adhoc-19 | **SAT, native 10/10** (S6101g) | **SAT, native 10/10**, control 0/10, 884 s | **SAT, native 10/10**, control 0/10, 632 s | CONFIG legacyCloud true -> false cluster-wide (field-backed via a tree workaround) | -- (the fixed code assigns a coreNodeName) |
| Solr | SOLR-6197 | solr-adhoc-19 | **SAT, native 10/10** (S6197g) | **SAT, native 10/10**, control 0/10, 988 s | **SAT, native 10/10**, control 0/10, 539 s | same, MIGRATE | -- |
| Solr | SOLR-6763 | solr-adhoc-38 | not reachable on today's code (no run): masked by SOLR-7844 | no run (no tree branch) | no run | -- | -- |

Tally (16 put back): **13 detected and accepted** -- HDFS-11741, -17383, -12931, -5766, -10609, -14075; HBASE-15039,
-20642; ZOOKEEPER-710, -2886; SOLR-9440, -6101, -6197 (of these 5 with the caveat that the fixed code also reaches the
throw in the witness world, and HBASE-20642 reproduced natively by IDENTITY §9 shape); 1 not detected, a capability limit
(HDFS-14311); 2 not reachable on today's code (HBASE-28533, SOLR-6763). B1 on liftlab gives the same verdict, mechanism
and CONFIRM for every case; native REPRODUCE differs only for SOLR-9440 (6/10 on liftlab, 10/10 on CloudLab; the
control 0/10 on both). E1, each case alone, gives every verdict, mechanism and CONFIRM again; native REPRODUCE: SOLR-9440
10/10 alone, HBASE-15039 8/10 alone (10/10 in B1), every control 0/10. Plus 4 existing GraphChecker bug checks at own
throws (HDFS-17897, -17899, -17967, SOLR-18406).

## Time, each case alone (round E1, 2026-10-29)

One case at a time on the 11 liftlab workers (lift02-06, 08-10, 12-14), nothing else running, each system's snapshot
`/u/vnr3ne/gc-run/bd-<x>-1` (the engine of these branches) and tree set `/bigtemp/vnr3ne/wt/bd-trees-1`; the driver is
`/bigtemp/vnr3ne/analysis/buggy-detect-exclusive-2026-10-28/series-E1.sh`, the log beside it. seeding = PREFLIGHT..IMPORT
(+ZKKEYS); exploration = EXPLORE; compose+solver = COMPOSE + SOLVE + DECIDE; other = CONFIRM + EMIT + REPRODUCE (native
10 runs + control 10); refuted = the claims CONFIRM refuted before the last; the rest of the wall is launch and teardown.

| system | bug | verdict | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted (s) |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| HDFS | HDFS-11741 | detected | 1123 | 299 | 634 | 149 | 26 | - |
| HDFS | HDFS-17383 | detected | 530 | 331 | 158 | 8 | 27 | - |
| HDFS | HDFS-12931 | detected | 400 | 244 | 119 | 8 | 21 | - |
| HDFS | HDFS-5766 | detected | 391 | 241 | 117 | 4 | 21 | - |
| HDFS | HDFS-10609 | detected | 556 | 273 | 244 | 8 | 24 | - |
| HDFS | HDFS-14075 | detected | 490 | 348 | 112 | 3 | 20 | - |
| HDFS | HDFS-14311 | not detected (UNSAT_CLOSED) | 2521 | 1188 | 1285 | 22 | 9 | - |
| HBase | HBASE-15039 | detected | 850 | 303 | 409 | 10 | 113 | - |
| HBase | HBASE-20642 | detected | 1504 | 334 | 332 | 15 | 4 | 819 (7 claims) |
| ZooKeeper | ZOOKEEPER-710 | detected | 311 | 165 | 108 | 10 | 21 | - |
| ZooKeeper | ZOOKEEPER-2886 | detected | 300 | 157 | 107 | 10 | 21 | - |
| Solr | SOLR-9440 | detected | 576 | 336 | 143 | 4 | 71 | - |
| Solr | SOLR-6101 | detected | 632 | 283 | 292 | 8 | 32 | - |
| Solr | SOLR-6197 | detected | 539 | 273 | 220 | 8 | 34 | - |
| **13 detected** | | | **8202** | 3587 (43.7 %) | 2995 (36.5 %) | 245 (3.0 %) | 435 (5.3 %) | 819 (10.0 %) |
| **all 14** | | | **10723** | 4775 (44.5 %) | 4280 (39.9 %) | 267 (2.5 %) | 444 (4.1 %) | 819 (7.6 %) |

A detected case takes 300-1504 s alone (median 530 s). Against B1 (side by side, 11171 s for the 14): the Solr cases
are 28-45 % faster alone (seeding 273-336 s, B1 539-657 s with the three seeding at once); HDFS-11741 is slower alone
(1123 s, B1 884 s) over the same closure and the same replays, every replay slower on every worker (median 119 s, B1
95 s), not explained; the rest are at most 13 % slower than in B1, or faster.

## Time, the whole exploration (round N1, 2026-10-29)

The owner: "不要中途replay碰到就停，而是完整跑完所有exploration", each case alone again. Twelve of E1's fourteen
explorations ended WITNESSED: the first admitted replay that observed the fatal at the declared occurrence was composed
over the corpus as it stood, CONFIRM accepted it, and the queued and running work was dropped (HDFS-11741: 1109 queued
obligations; HBASE-20642: 426 unlanded jobs). N1 runs those twelve with `CAUSYNTH_STREAM_STOP_AT_WITNESS=false` (`run_engine.sh` `stream_stop_at_witness`, `docs/design/PIPELINE.md`): no
session is a witness, every exploration runs to FIXED_POINT, and COMPOSE, SOLVE, DECIDE and CONFIRM run once over the
whole corpus. HDFS-14311 and HBASE-15039
reached FIXED_POINT in E1 and are not run again. The E1 workers and trees, snapshots `/u/vnr3ne/gc-run/bd-<x>-2` (the
E1 engine plus that key), 12 h per case, driver `/bigtemp/vnr3ne/analysis/buggy-detect-full-2026-10-29/series-N1.sh`,
runs `/bigtemp/vnr3ne/gc-out/buggy-detect-full/accept-N1-<case>`.

| system | bug | report.py | rounds / verdicts, E1 -> N1 | wall (s), E1 -> N1 | seeding (s) | exploration (s), E1 -> N1 | compose+solver (s), E1 -> N1 | other (s) | refuted claims (s) |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| ZooKeeper | ZOOKEEPER-2886 | PASS | 5 / 57 -> 12 / 128 | 300 -> 595 | 160 | 107 -> 375 | 10 -> 10 | 47 | - |
| ZooKeeper | ZOOKEEPER-710 | PASS | 5 / 112 -> 12 / 122 | 311 -> 589 | 164 | 108 -> 366 | 10 -> 6 | 46 | - |
| HDFS | HDFS-12931 | PASS | 1 / 11 -> 10 / 67 | 400 -> 611 | 241 | 119 -> 237 | 8 -> 103 | 23 | - |
| HDFS | HDFS-5766 | PASS | 1 / 11 -> 13 / 68 | 391 -> 679 | 243 | 117 -> 309 | 4 -> 97 | 24 | - |
| HDFS | HDFS-14075 | PASS | 2 / 12 -> 6 / 16 | 490 -> 475 | 354 | 112 -> 84 | 3 -> 5 | 23 | - |
| HDFS | HDFS-17383 | PASS | 1 / 19 -> 15 / 75 | 530 -> 916 | 324 | 158 -> 477 | 8 -> 81 | 29 | - |
| HDFS | HDFS-10609 | PASS | 2 / 42 -> 27 / 235 | 556 -> 859 | 265 | 244 -> 399 | 8 -> 161 | 28 | - |
| Solr | SOLR-9440 | PASS | 9 / 36 -> 30 / 135 | 576 -> 1065 | 338 | 143 -> 603 | 4 -> 33 | 75 | - |
| Solr | SOLR-6197 | **FAIL** (below) | 15 / 79 -> 38 / 105 | 539 -> 948 | 279 | 220 -> 605 | 8 -> 11 | 37 | - |
| Solr | SOLR-6101 | PASS | 21 / 113 -> 45 / 125 | 632 -> 940 | 275 | 292 -> 601 | 8 -> 16 | 34 | - |
| HBase | HBASE-20642 | PASS | 3 / 28 -> 27 / 534 | 1504 -> 1720 | 320 | 332 -> 463 | 15 -> 51 | 110 | 776 (8 claims; E1 819) |
| HDFS | HDFS-11741 | PASS | 9 / 347 -> 38 / 3354 | 1123 -> 2551 | 252 | 634 -> 1369 | 149 -> 794 | 127 | - |
| **12 cases** | | | | **7352 -> 11948** | 3215 (26.9 %) | 2586 -> 5888 (49.3 %) | 235 -> 1368 (11.4 %) | 603 (5.0 %) | 776 (6.5 %) |

Every exploration reached FIXED_POINT (none the budget); every claim is SAT, CONFIRM again, native REPRODUCE as in E1
(10/10, HBASE-20642 exact id 0/10 and by shape 10/10, every control 0/10). Against E1 the 12 take 1.63 times the wall
and 2.28 times the exploration; with HBASE-15039 from E1 the 13 detected there take 12798 s (median 859 s): seeding
27 %, exploration 49 %, compose+solver 11 %, other 6 %, refuted claims 6 %; with HDFS-14311 the 14 take 15319 s. E1's
exploration column holds its witness attempt (that COMPOSE and CONFIRM ran inside EXPLORE, and the final stages reused
them); in N1 COMPOSE reads the whole corpus (HDFS-11741: 793 s of its 794 over 3354 verdicts, SOLVE 0.5 s) and CONFIRM
is a replay of its own. HBASE-20642 decided 8 claims before the last both times (N1: 2 CONFIRM refuted, 6 confirmed
and natively 0/10 by exact id; E1: 7 and 1); the first confirmed claim stands.

SOLR-6197 is SAT, confirmed, natively 10/10 with the control 0/10, but report.py FAILs it: 20 BLOCKING
TOPOLOGY_DIVERGENCE rows (`explore/SlotTable#take`, "a replacement, not growth"). Two admitted replays of one world
(obligations 265d7b401e0d73ea and a5972cb95766e3f7, the latter re-run under the grown tree, the session CONFIRM chose)
pair the anchor's core create (`CoreContainer.create`) reads of five `state.json` fields with the overseer's first
`setData` of `state.json` in one and its second in the other: which version the core create reads is a race the replay
does not pin. E1 ended WITNESSED before a second session of that world was in its corpus.

Branches (github.com/JHSUYU): GraphChecker `system/hdfs-buggy-detect`, `system/hbase-buggy-detect`,
`system/zookeeper-buggy-detect`, `system/solr-buggy-detect`, each `system/<x>` (liftlab) plus that system's old-bug cases
and their engine support; the forks' `graphchecker/hdfs-bug-<jira>` (hadoop), `graphchecker/hbase-bug-<jira>` (hbase),
`graphchecker/zk-bug-<jira>` and `graphchecker/zk-bug-<jira>-control` (zookeeper), `graphchecker/solr-bug-<jira>`
(solr). Each case's README (`experiments/<sys>/<sys>-buggy-<jira>/`; ZooKeeper's `zk-buggy-<jira>`) has the bug, what
was put back, the workload and its workarounds, every declaration, the runs and the reading.

Engine support, on these branches only, each independently reviewed:
- HDFS (for 14311): ba6580331, 131bf16d9, 7f562ef37, 252ed18da, 6a7c74e61, 838b0c888 (an earlier or later concurrent
  writer may move past a write the reader cannot pass; per-version proposals; holds after the passed write's activation
  exits, decided by Arms' one rule).
- HBase: 948e4779f (the reply legs of a turn's earlier requests are control producers), 93a168e87 + 298508ffa (one
  implementation of IDENTITY §9, `AnswerOrder`, used by CONFIRM and native REPRODUCE; `reproduced` stays exact-only,
  by-shape counted apart). Rejected and reverted: 455a6dd66 (017dcf890).
- ZooKeeper: bba07d7d1 (CONFIRM holds at the nearest instrumented claim when the submitter is uninstrumented), on the
  integration line of 2026-10-25 (own-context answer by counts; the String-length range as a side condition; the GROW
  re-run swap rules).
- Solr: 61e881776 + e5c894636 + ad3d08028 (native REPRODUCE plants a field-backed CONFIG root at the plan's read sites,
  guarded by a GETFIELD count; getter CONFIG roots stay refused).
- CloudLab's host ledger in hundredths of a core (f82385bcc, 35a513aa7) was reverted with CloudLab's scheduling layer
  when the branches came to liftlab (2026-10-28).

Decided by the owner (2026-10-27/28): the 5 caveated cases count as detected (the bug makes the ad hoc check fail);
HBASE-20642's by-shape native reproduction is accepted; HDFS-14311 (capability limit), HBASE-28533 and SOLR-6763 (not
reachable on today's code) are closed as they stand. Left as follow-ups, not done: a CONFIRM change for HDFS-14311's
post-fatal ORDER timeout (needs the owner's sign-off); the native getter-CONFIG plant scope (wider than the VM, kept
disabled); three minor native-plant report gaps (fieldUnwritten silent while the window is closed; a planned method
with no GETFIELD; a class the agent fails to rewrite); native verification of HBASE-28533 and SOLR-6763 (started and
stopped by the owner, nothing committed).

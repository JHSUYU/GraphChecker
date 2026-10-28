# Old bugs that make an ad hoc check fail, detected on today's trees (CloudLab 2026-10-26; liftlab B1 2026-10-28)

Standard (owner 2026-10-26): a bug counts only if GraphChecker's witness fires the point's OWN declared throw. SAT is
accepted when CONFIRM realizes it in the VM, native REPRODUCE reproduces it k/N with control 0/N, and report.py passes.
Where the fixed code also reaches the throw in the witness world, the case README says so ("caveat"). The owner
(2026-10-26): a check truly beyond GraphChecker's capability is not forced.

Source list: the owner's 73 old bugs (`all_73_bugs.txt`, with its own-throw rows `own-throw.txt`: kept on the CloudLab
cluster only, no liftlab copy). 21 own-throw bugs: 20 usable (HDFS-6325 excluded: its point's guard IS the fix),
4 of them existing GraphChecker bug checks (HDFS-17897, -17899, -17967, SOLR-18406), so 16 put back by hand on each
system's current tree, one fork branch each.

| system | bug | point | CloudLab, 2026-10-26: verdict (run) | mechanism | caveat | liftlab, B1 |
| --- | --- | --- | --- | --- | --- | --- |
| HDFS | HDFS-11741 | hdfs-adhoc-11 | **SAT, native 10/10** (B11741b) | CLOCK_SKEW, nn0 + target-dn clocks | the fix checks the Balancer's own clock, unmoved | B1 (lead fills in) |
| HDFS | HDFS-17383 | hdfs-adhoc-12 | **SAT, native 10/10** (B17383a) | lost heartbeat reply from the standby | -- | B1 (lead fills in) |
| HDFS | HDFS-12931 | hdfs-adhoc-11 | **SAT, native 10/10** (B12931a) | lost key-update heartbeat reply | the DataNode throws first on the fixed code too | B1 (lead fills in) |
| HDFS | HDFS-5766 | hdfs-adhoc-11 | **SAT, native 10/10** (B5766a) | lost key-update heartbeat request | same | B1 (lead fills in) |
| HDFS | HDFS-10609 | hdfs-adhoc-11 | **SAT, native 10/10** (B10609a) | lost key-update heartbeat request | same | B1 (lead fills in) |
| HDFS | HDFS-14075 | hdfs-adhoc-45 | **SAT, native 10/10** (B14075c) | LOCAL_IO fault on roll 1's edits open | -- (the fix terminates the NN) | B1 (lead fills in) |
| HDFS | HDFS-14311 | hdfs-adhoc-24 | not detected: a capability limit (B14311a-f) | the intended STATE re-pairing (vol2's layoutVersion read <- vol1's upgrade-task write) is never realized: the engine offers the reader's own task, created after the read, as a concurrent writer, and CONFIRM's pairing hold sits after the reads that decide the guard | the only witness found (B14311d) was the race by timing, native 0/10 | B1 (lead fills in) |
| HBase | HBASE-15039 | hbase-adhoc-34 | **SAT, native 10/10** (HB15039b) | STATE: the watcher's addKey after the validation | -- (the fix refreshes) | B1 (lead fills in) |
| HBase | HBASE-20642 | hbase-adhoc-04 | **SAT, native 10/10** (HB20642f; native REPRODUCE answered by IDENTITY §9 shape 10/10, exact id 0/10, control 0/10; accepted by the owner 2026-10-27) | lost DisableTable reply, retry with a new nonce | the retry's handler has no recorded address; native runs answer it by the rule CONFIRM uses, decided by arrival order | B1 (lead fills in) |
| HBase | HBASE-28533 | hbase-adhoc-15 | not reachable on today's code (no run) | the merge constructor's checkOnline refuses first | the lowest world reaching :507 never runs the buggy rollback | no run (as on CloudLab) |
| ZooKeeper | ZOOKEEPER-710 | zk-adhoc-02 | **SAT, native 10/10** (ZB6) | STATE: the owner read paired with the takeover's REVALIDATE | the fixed-tree control is also SAT 10/10 (plain world) | B1 (lead fills in) |
| ZooKeeper | ZOOKEEPER-2886 | zk-adhoc-02 | **SAT, native 10/10** (ZB6) | same, multi-only | same | B1 (lead fills in) |
| Solr | SOLR-9440 | solr-adhoc-31 | **SAT, native 10/10** (S9440b) | ZooKeeper SessionExpired on node1's leader-election create during the core CREATE | -- (the fixed code evicts the frozen view) | B1 (lead fills in) |
| Solr | SOLR-6101 | solr-adhoc-19 | **SAT, native 10/10** (S6101g) | CONFIG legacyCloud true -> false cluster-wide (field-backed via a tree workaround) | -- (the fixed code assigns a coreNodeName) | B1 (lead fills in) |
| Solr | SOLR-6197 | solr-adhoc-19 | **SAT, native 10/10** (S6197g) | same, MIGRATE | -- | B1 (lead fills in) |
| Solr | SOLR-6763 | solr-adhoc-38 | not reachable on today's code (no run): masked by SOLR-7844 | -- | -- | no run (as on CloudLab) |

Tally (16 put back): **13 detected and accepted** (HDFS-11741, -17383, -12931, -5766, -10609, -14075; HBASE-15039,
-20642; ZOOKEEPER-710, -2886; SOLR-9440, -6101, -6197 -- of these 5 with the caveat that the fixed code also reaches the
throw in the witness world, and HBASE-20642 reproduced natively by IDENTITY §9 shape, accepted by the owner); 1 not
detected, a capability limit (HDFS-14311); 2 not reachable on today's code (HBASE-28533, SOLR-6763). The owner
(2026-10-27) accepted HBASE-20642's by-shape reproduction and closed HDFS-14311, HBASE-28533 and SOLR-6763 as they stand. Plus 4 existing GraphChecker
bug checks at own throws (HDFS-17897, -17899, -17967, SOLR-18406).

Branches (pushed to github.com/JHSUYU, owner 2026-10-27): GraphChecker `system/hdfs-buggy-detect`, `system/hbase-buggy-detect`,
`system/zookeeper-buggy-detect`, `system/solr-buggy-detect`; the forks' (`JHSUYU/{hadoop,hbase,zookeeper,solr}`)
`graphchecker/{hdfs,hbase,zk,solr}-bug-<jira>`. Each case's README (`experiments/<sys>/<sys>-buggy-<jira>/`) has the bug,
what was put back, the workload and its workarounds, every declaration, the runs and the reading.

**On liftlab (2026-10-28).** Each buggy-detect branch is now its system's liftlab branch (`system/<x>`) plus the
cases and the engine support below; the CloudLab scheduling layer is reverted on it (the host ledger charges memory,
no lift above 70 %), and the CloudLab branches are the tags `archive/system/<x>-cloudlab`. Series B1 runs every case
again: tree set `/bigtemp/vnr3ne/wt/bd-trees-1` (each system's `experiments/<sys>/prepare-trees.sh` with
`GC_TREES=/bigtemp/vnr3ne/wt/bd-trees-1 GC_M2=/bigtemp/vnr3ne/m2/bd-1`), snapshots `/u/vnr3ne/gc-run/bd-<x>-1` (x = hdfs,
hbase, zookeeper, solr), outputs `/bigtemp/vnr3ne/gc-out/buggy-detect/accept-B1-<case>` (an HDFS case without its
`hdfs-` prefix), launched by `tools/rounds/launch-round.sh` with `CASES=` the system's buggy cases; each branch's
START-HERE has the commands. Its column above is B1's verdict, run and native k/N.

Engine support, on these branches only, each independently reviewed:
- HBase: 948e4779f (the reply legs of a turn's earlier requests are control producers), f82385bcc (host ledger in
  hundredths, also Solr 35a513aa7: CloudLab scheduling, reverted on liftlab), 93a168e87 + 298508ffa (one implementation of IDENTITY §9, `AnswerOrder`, used by
  CONFIRM and native REPRODUCE; `reproduced` stays exact-only, by-shape counted apart). Rejected and reverted: 455a6dd66.
- ZooKeeper: bba07d7d1 (CONFIRM holds at the nearest instrumented claim when the submitter is uninstrumented).
- HDFS: ba6580331, 131bf16d9, 7f562ef37, 252ed18da, 6a7c74e61, 838b0c888 (an earlier or later concurrent writer may move
  past a write the reader cannot pass; per-version proposals; holds after the passed write's activation exits).
- Solr: 61e881776 + e5c894636 + ad3d08028 (native REPRODUCE plants a field-backed CONFIG root at the plan's read sites,
  guarded by a GETFIELD count; getter CONFIG roots stay refused).

Decided by the owner (2026-10-27/28): the 5 caveated cases count as detected (the bug makes the ad hoc check fail); HBASE-20642's by-shape native reproduction is accepted; HDFS-14311 (capability
limit), HBASE-28533 and SOLR-6763 (not reachable on today's code) are closed as they stand; the branches are pushed.
Left as follow-ups, not done: a CONFIRM change for HDFS-14311's post-fatal ORDER timeout; the native getter-CONFIG plant
scope (wider than the VM, kept disabled); three minor native-plant report gaps (`fieldUnwritten` silent while the window is
closed; a planned method with no GETFIELD; a class the agent fails to rewrite).

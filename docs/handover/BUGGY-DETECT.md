# Old bugs that make an ad hoc check fail, put back on today's trees and detected (buggy-detect)

Standard (owner 2026-10-26): a bug counts only if GraphChecker's witness fires the point's OWN declared throw. SAT is
accepted when CONFIRM realizes it in the VM, native REPRODUCE reproduces it k/N with control 0/N, and report.py passes.
Where the fixed code also reaches the throw in the witness world, the case README says so ("caveat"). The owner
(2026-10-26): a check truly beyond GraphChecker's capability is not forced.

Source: the owner's list of 73 old bugs (`all_73_bugs.txt`, the rows whose bug "fires this point's own throw"). 21
own-throw bugs: 20 usable (HDFS-6325 excluded: its point's guard IS the fix), 4 of them existing GraphChecker bug checks
(HDFS-17897, -17899, -17967, SOLR-18406), so 16 put back by hand on each system's current tree, one fork branch each.

The record so far is the CloudLab series of 2026-10-26..28 (the CloudLab ports are the tags
`archive/system/<x>-cloudlab`). Every case runs again on liftlab as round B1 (`/bigtemp/vnr3ne/gc-out/buggy-detect`,
`accept-B1-<case>`), each system's cases from its buggy-detect branch; its column pairs with CloudLab's.

| system | bug | point | case | CloudLab, 2026-10-26 (run) | liftlab B1 | mechanism | caveat |
| --- | --- | --- | --- | --- | --- | --- | --- |
| HDFS | HDFS-11741 | hdfs-adhoc-11 | hdfs-buggy-11741 | **SAT, native 10/10** (B11741b) | B1 (lead fills in) | CLOCK_SKEW, nn0 + target-dn clocks | the fix checks the Balancer's own clock, unmoved |
| HDFS | HDFS-17383 | hdfs-adhoc-12 | hdfs-buggy-17383 | **SAT, native 10/10** (B17383a) | B1 (lead fills in) | lost heartbeat reply from the standby | -- |
| HDFS | HDFS-12931 | hdfs-adhoc-11 | hdfs-buggy-12931 | **SAT, native 10/10** (B12931a) | B1 (lead fills in) | lost key-update heartbeat reply | the DataNode throws first on the fixed code too |
| HDFS | HDFS-5766 | hdfs-adhoc-11 | hdfs-buggy-5766 | **SAT, native 10/10** (B5766a) | B1 (lead fills in) | lost key-update heartbeat request | same |
| HDFS | HDFS-10609 | hdfs-adhoc-11 | hdfs-buggy-10609 | **SAT, native 10/10** (B10609a) | B1 (lead fills in) | lost key-update heartbeat request | same |
| HDFS | HDFS-14075 | hdfs-adhoc-45 | hdfs-buggy-14075 | **SAT, native 10/10** (B14075c) | B1 (lead fills in) | LOCAL_IO fault on roll 1's edits open | -- (the fix terminates the NN) |
| HDFS | HDFS-14311 | hdfs-adhoc-24 | hdfs-buggy-14311 | not detected: a capability limit (B14311a-f) | B1 (lead fills in) | the intended STATE re-pairing (vol2's layoutVersion read <- vol1's upgrade-task write) is never realized: the engine offers the reader's own task, created after the read, as a concurrent writer, and CONFIRM's pairing hold sits after the reads that decide the guard | the only witness found (B14311d) was the race by timing, native 0/10 |
| HBase | HBASE-15039 | hbase-adhoc-34 | hbase-buggy-15039 | **SAT, native 10/10** (HB15039b) | B1 (lead fills in) | STATE: the watcher's addKey after the validation | -- (the fix refreshes) |
| HBase | HBASE-20642 | hbase-adhoc-04 | hbase-buggy-20642 | **SAT, native 10/10** (HB20642f; native REPRODUCE answered by IDENTITY §9 shape 10/10, exact id 0/10, control 0/10; accepted by the owner 2026-10-27) | B1 (lead fills in) | lost DisableTable reply, retry with a new nonce | the retry's handler has no recorded address; native runs answer it by the rule CONFIRM uses, decided by arrival order |
| HBase | HBASE-28533 | hbase-adhoc-15 | -- (README only) | not reachable on today's code (no run) | -- (no case) | the merge constructor's checkOnline refuses first | the lowest world reaching :507 never runs the buggy rollback |
| ZooKeeper | ZOOKEEPER-710 | zk-adhoc-02 | zk-buggy-710 | **SAT, native 10/10** (ZB6) | B1 (lead fills in) | STATE: the owner read paired with the takeover's REVALIDATE | the fixed-tree control is also SAT 10/10 (plain world) |
| ZooKeeper | ZOOKEEPER-2886 | zk-adhoc-02 | zk-buggy-2886 | **SAT, native 10/10** (ZB6) | B1 (lead fills in) | same, multi-only | same |
| Solr | SOLR-9440 | solr-adhoc-31 | solr-buggy-9440 | **SAT, native 10/10** (S9440b) | B1 (lead fills in) | ZooKeeper SessionExpired on node1's leader-election create during the core CREATE | -- (the fixed code evicts the frozen view) |
| Solr | SOLR-6101 | solr-adhoc-19 | solr-buggy-6101 | **SAT, native 10/10** (S6101g) | B1 (lead fills in) | CONFIG legacyCloud true -> false cluster-wide (field-backed via a tree workaround) | -- (the fixed code assigns a coreNodeName) |
| Solr | SOLR-6197 | solr-adhoc-19 | solr-buggy-6197 | **SAT, native 10/10** (S6197g) | B1 (lead fills in) | same, MIGRATE | -- |
| Solr | SOLR-6763 | solr-adhoc-38 | -- (README only) | not reachable on today's code (no run): masked by SOLR-7844 | -- (no case) | -- | -- |

Tally (16 put back), CloudLab 2026-10-26: **13 detected and accepted** (HDFS-11741, -17383, -12931, -5766, -10609,
-14075; HBASE-15039, -20642; ZOOKEEPER-710, -2886; SOLR-9440, -6101, -6197 -- of these 5 with the caveat that the fixed
code also reaches the throw in the witness world, and HBASE-20642 reproduced natively by IDENTITY §9 shape, accepted by
the owner); 1 not detected, a capability limit (HDFS-14311); 2 not reachable on today's code (HBASE-28533, SOLR-6763).
Plus 4 existing GraphChecker bug checks at own throws (HDFS-17897, -17899, -17967, SOLR-18406). Liftlab B1: B1 (lead
fills in).

Decided by the owner (2026-10-27/28): the 5 caveated cases count as detected (the bug makes the ad hoc check fail);
HBASE-20642's by-shape native reproduction is accepted; HDFS-14311 (capability limit), HBASE-28533 and SOLR-6763 (not
reachable on today's code) are closed as they stand; the branches are pushed.

Branches (github.com/JHSUYU, pushed 2026-10-27): GraphChecker `system/hdfs-buggy-detect`, `system/hbase-buggy-detect`,
`system/zookeeper-buggy-detect`, `system/solr-buggy-detect` -- each its system's ad hoc branch (`system/hdfs-liftlab`,
`system/hbase`, `system/zookeeper`, `system/solr`) plus the old-bug cases and their engine support; the forks'
`graphchecker/hdfs-bug-<jira>` (hadoop), `graphchecker/hbase-bug-<jira>`, `graphchecker/zk-bug-<jira>` (and
`-control`, the same workloads on the fixed code), `graphchecker/solr-bug-<jira>`. Each case's README
(`experiments/<sys>/<sys>-buggy-<jira>/`; ZooKeeper's `zk-buggy-<jira>`) has the bug, what was put back, the workload and
its workarounds, every declaration, the runs and the reading.

Engine support, on these branches only, each independently reviewed:
- HBase: 948e4779f (the reply legs of a turn's earlier requests are control producers), 93a168e87 + 298508ffa (one
  implementation of IDENTITY §9, `AnswerOrder`, used by CONFIRM and native REPRODUCE; `reproduced` stays exact-only,
  by-shape counted apart). Rejected and reverted: 455a6dd66.
- ZooKeeper: bba07d7d1 (CONFIRM holds at the nearest instrumented claim when the submitter is uninstrumented).
- HDFS: ba6580331, 131bf16d9, 7f562ef37, 252ed18da, 6a7c74e61, 838b0c888 (an earlier or later concurrent writer may move
  past a write the reader cannot pass; per-version proposals; holds after the passed write's activation exits).
- Solr: 61e881776 + e5c894636 + ad3d08028 (native REPRODUCE plants a field-backed CONFIG root at the plan's read sites,
  guarded by a GETFIELD count; getter CONFIG roots stay refused).
- CloudLab's core ledger in hundredths (HBase f82385bcc, Solr 35a513aa7) went with the rest of CloudLab's scheduling
  layer when each branch was put back on liftlab (2026-10-27/28): the host ledger charges memory, 70 % of a lift.

Left as follow-ups, not done: a CONFIRM change for HDFS-14311's post-fatal ORDER timeout; the native getter-CONFIG plant
scope (wider than the VM, kept disabled); three minor native-plant report gaps (each branch's TODO "Buggy-detect").

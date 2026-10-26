# Old bugs that make an ad hoc check fail, detected on today's trees (2026-10-26, final)

Standard (owner 2026-10-26): a bug counts only if GraphChecker's witness fires the point's OWN declared throw. SAT is
accepted when CONFIRM realizes it in the VM, native REPRODUCE reproduces it k/N with control 0/N, and report.py passes.
Where the fixed code also reaches the throw in the witness world, the case README says so ("caveat"). The owner
(2026-10-26): a check truly beyond GraphChecker's capability is not forced.

Source list: node1 `/users/ZhenyuLi/oldbug/all_73_bugs.txt` (own-throw rows: `own-throw.txt` in
/bulk/analysis/buggy-detect-2026-10-26). 21 own-throw bugs: 20 usable (HDFS-6325 excluded: its point's guard IS the fix),
4 of them existing GraphChecker bug checks (HDFS-17897, -17899, -17967, SOLR-18406), so 16 put back by hand on each
system's current tree, one fork branch each.

| system | bug | point | verdict | mechanism | caveat |
| --- | --- | --- | --- | --- | --- |
| HDFS | HDFS-11741 | hdfs-adhoc-11 | **SAT, native 10/10** (B11741b) | CLOCK_SKEW, nn0 + target-dn clocks | the fix checks the Balancer's own clock, unmoved |
| HDFS | HDFS-17383 | hdfs-adhoc-12 | **SAT, native 10/10** (B17383a) | lost heartbeat reply from the standby | -- |
| HDFS | HDFS-12931 | hdfs-adhoc-11 | **SAT, native 10/10** (B12931a) | lost key-update heartbeat reply | the DataNode throws first on the fixed code too |
| HDFS | HDFS-5766 | hdfs-adhoc-11 | **SAT, native 10/10** (B5766a) | lost key-update heartbeat request | same |
| HDFS | HDFS-10609 | hdfs-adhoc-11 | **SAT, native 10/10** (B10609a) | lost key-update heartbeat request | same |
| HDFS | HDFS-14075 | hdfs-adhoc-45 | **SAT, native 10/10** (B14075c) | LOCAL_IO fault on roll 1's edits open | -- (the fix terminates the NN) |
| HDFS | HDFS-14311 | hdfs-adhoc-24 | not detected: a capability limit (B14311a-f) | the intended STATE re-pairing (vol2's layoutVersion read <- vol1's upgrade-task write) is never realized: the engine offers the reader's own task, created after the read, as a concurrent writer, and CONFIRM's pairing hold sits after the reads that decide the guard | the only witness found (B14311d) was the race by timing, native 0/10 |
| HBase | HBASE-15039 | hbase-adhoc-34 | **SAT, native 10/10** (HB15039b) | STATE: the watcher's addKey after the validation | -- (the fix refreshes) |
| HBase | HBASE-20642 | hbase-adhoc-04 | SAT confirmed in the VM (HB20642f); native REPRODUCE by IDENTITY §9 shape 10/10, by exact id 0/10, control 0/10 -- **owner to decide** whether the by-shape count is accepted | lost DisableTable reply, retry with a new nonce | the retry's handler has no recorded address; native runs answer it by the rule CONFIRM uses, decided by arrival order |
| HBase | HBASE-28533 | hbase-adhoc-15 | not reachable on today's code (no run) | the merge constructor's checkOnline refuses first | the lowest world reaching :507 never runs the buggy rollback |
| ZooKeeper | ZOOKEEPER-710 | zk-adhoc-02 | **SAT, native 10/10** (ZB6) | STATE: the owner read paired with the takeover's REVALIDATE | the fixed-tree control is also SAT 10/10 (plain world) |
| ZooKeeper | ZOOKEEPER-2886 | zk-adhoc-02 | **SAT, native 10/10** (ZB6) | same, multi-only | same |
| Solr | SOLR-9440 | solr-adhoc-31 | **SAT, native 10/10** (S9440b) | ZooKeeper SessionExpired on node1's leader-election create during the core CREATE | -- (the fixed code evicts the frozen view) |
| Solr | SOLR-6101 | solr-adhoc-19 | **SAT, native 10/10** (S6101g) | CONFIG legacyCloud true -> false cluster-wide (field-backed via a tree workaround) | -- (the fixed code assigns a coreNodeName) |
| Solr | SOLR-6197 | solr-adhoc-19 | **SAT, native 10/10** (S6197g) | same, MIGRATE | -- |
| Solr | SOLR-6763 | solr-adhoc-38 | not reachable on today's code (no run): masked by SOLR-7844 | -- | -- |

Tally (16 put back): **12 fully accepted** (HDFS-11741, -17383, -12931, -5766, -10609, -14075; HBASE-15039;
ZOOKEEPER-710, -2886; SOLR-9440, -6101, -6197 -- of these 5 with the caveat that the fixed code also reaches the throw in
the witness world); 1 SAT confirmed with native 10/10 by shape only (HBASE-20642, owner's call); 1 not detected, a
capability limit (HDFS-14311); 2 not reachable on today's code (HBASE-28533, SOLR-6763). Plus 4 existing GraphChecker
bug checks at own throws (HDFS-17897, -17899, -17967, SOLR-18406).

Branches (nothing pushed): GraphChecker `system/hdfs-buggy-detect`, `system/hbase-buggy-detect`,
`system/zookeeper-buggy-detect`, `system/solr-buggy-detect`; forks `graphchecker/{hdfs,hbase,zk,solr}-bug-<jira>` in
`/bulk/hadoop`, `/bulk/hbase`, `/bulk/zookeeper`, `/bulk/solr`. Each case's README (`experiments/<sys>/<sys>-buggy-<jira>/`)
has the bug, what was put back, the workload and its workarounds, every declaration, the runs and the reading.

Engine support, on these branches only, each independently reviewed:
- HBase: 948e4779f (the reply legs of a turn's earlier requests are control producers), f82385bcc (host ledger in
  hundredths; also Solr 35a513aa7), 93a168e87 + 298508ffa (one implementation of IDENTITY §9, `AnswerOrder`, used by
  CONFIRM and native REPRODUCE; `reproduced` stays exact-only, by-shape counted apart). Rejected and reverted: 455a6dd66.
- ZooKeeper: bba07d7d1 (CONFIRM holds at the nearest instrumented claim when the submitter is uninstrumented).
- HDFS: ba6580331, 131bf16d9, 7f562ef37, 252ed18da, 6a7c74e61, 838b0c888 (an earlier or later concurrent writer may move
  past a write the reader cannot pass; per-version proposals; holds after the passed write's activation exits).
- Solr: 61e881776 + e5c894636 + ad3d08028 (native REPRODUCE plants a field-backed CONFIG root at the plan's read sites,
  guarded by a GETFIELD count; getter CONFIG roots stay refused).

Open for the owner:
1. HBASE-20642: accept native reproduction answered by IDENTITY §9 shape (10/10) or require the exact id (0/10).
2. HDFS-14311's second blocker would need a CONFIRM change (an ORDER timeout after the fatal refutes); not done.
3. The native getter-CONFIG plant scope (wider than the VM) stays disabled; three minor native-plant report gaps are
   noted in /bulk/analysis/buggy-detect-2026-10-26/6101-notes.md.
4. Push: nothing is pushed. Superseded tree sets and snapshots under /bulk are kept.

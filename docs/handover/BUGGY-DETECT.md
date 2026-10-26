# Old bugs that make an ad hoc check fail, detected on today's trees (2026-10-26, final)

Standard (owner 2026-10-26): a bug counts only if GraphChecker's witness fires the point's OWN declared throw. SAT is
accepted when CONFIRM realizes it in the VM, native REPRODUCE reproduces it k/N with control 0/N, and report.py passes.
Where the fixed code also reaches the throw in the witness world, the case README says so ("caveat").

Source list: node1 `/users/ZhenyuLi/oldbug/all_73_bugs.txt` (own-throw rows: `own-throw.txt` here). 21 own-throw bugs:
20 usable (HDFS-6325 excluded: its point's guard IS the fix), 4 of them existing GraphChecker bug checks (HDFS-17897,
-17899, -17967, SOLR-18406), so 16 put back by hand on each system's current tree.

| system | bug | point | verdict | mechanism | caveat |
| --- | --- | --- | --- | --- | --- |
| HDFS | HDFS-11741 | hdfs-adhoc-11 | **SAT, native 10/10** (B11741b) | CLOCK_SKEW, nn0 + target-dn clocks | fix checks the Balancer's own clock, unmoved |
| HDFS | HDFS-17383 | hdfs-adhoc-12 | **SAT, native 10/10** (B17383a) | lost heartbeat reply from the standby | -- |
| HDFS | HDFS-12931 | hdfs-adhoc-11 | **SAT, native 10/10** (B12931a) | lost key-update heartbeat reply | DN throws first on fixed code too |
| HDFS | HDFS-5766 | hdfs-adhoc-11 | **SAT, native 10/10** (B5766a) | lost key-update heartbeat request | same |
| HDFS | HDFS-10609 | hdfs-adhoc-11 | **SAT, native 10/10** (B10609a) | lost key-update heartbeat request | same |
| HDFS | HDFS-14075 | hdfs-adhoc-45 | **SAT, native 10/10** (B14075c) | LOCAL_IO fault on roll 1's edits open | -- (fix terminates the NN) |
| HDFS | HDFS-14311 | hdfs-adhoc-24 | not detected (B14311a-e): only witness was the race by timing with an incidental LOCAL_IO marker, native 0/10 (control 1/10) | intended STATE re-pairing blocked by two named engine limits (carried-anchor concurrency of the reader's own task; post-fatal ORDER timeout refutes in CONFIRM) | -- |
| HBase | HBASE-15039 | hbase-adhoc-34 | **SAT, native 10/10** (HB15039b) | STATE: watcher's addKey after validation | -- (fix refreshes) |
| HBase | HBASE-20642 | hbase-adhoc-04 | SAT confirmed in VM; native throws at :163 10/10 but not at the exact anchor id (not accepted) | lost DisableTable reply, retry with new nonce | retry's handler answered by shape only in the VM |
| HBase | HBASE-28533 | hbase-adhoc-15 | does not reach its own throw on today's code (no run) | merge constructor's checkOnline refuses first | lowest world to :507 never runs the buggy rollback |
| ZooKeeper | ZOOKEEPER-710 | zk-adhoc-02 | **SAT, native 10/10** (ZB6) | STATE: owner read paired with takeover's REVALIDATE | fixed-tree control also SAT 10/10 (plain world) |
| ZooKeeper | ZOOKEEPER-2886 | zk-adhoc-02 | **SAT, native 10/10** (ZB6) | same, multi-only | same |
| Solr | SOLR-9440 | solr-adhoc-31 | SAT confirmed in VM, witness discriminates; native 0/10 (not accepted) | ConnectionLoss on the Overseer's ACTIVE write | needed order not in the claim's cone |
| Solr | SOLR-6101 | solr-adhoc-19 | SAT confirmed in VM, report.py PASS (S6101e); engine REPRODUCE NATIVE_PLANT_UNSUPPORTED (getter-return config); scratch native 10/10 at :1330, control 0/3 | CONFIG legacyCloud true->false at the node's reads | fixed tree also throws 10/10 in that node-only world; cluster-wide world planned but not realized (S6101d) |
| Solr | SOLR-6197 | solr-adhoc-19 | same (S6197e): SAT confirmed, PASS; engine REPRODUCE unsupported; scratch native 10/10, control 0/3 | same | same (S6197d) |
| Solr | SOLR-6763 | solr-adhoc-38 | not reachable on today's code (no run): masked by SOLR-7844 | -- | -- |

Tally (16 put back): 9 fully accepted (CONFIRM + engine native REPRODUCE 10/10 + report.py PASS: HDFS-11741, -17383,
-12931, -5766, -10609, -14075, HBASE-15039, ZOOKEEPER-710, -2886); 3 SAT confirmed at the own throw with native
evidence outside the engine's REPRODUCE (HBASE-20642: native 10/10 at :163 but not at the exact anchor id;
SOLR-6101, -6197: engine plant unsupported, scratch native 10/10); 1 SAT confirmed in the VM only (SOLR-9440, native
0/10); 1 not detected (HDFS-14311, two named engine limits); 2 not reachable on today's code (HBASE-28533, SOLR-6763).
Plus 4 existing GraphChecker bug checks at own throws (HDFS-17897, -17899, -17967, SOLR-18406).

Branches (nothing pushed): GraphChecker `system/hdfs-buggy-detect`, `system/hbase-buggy-detect`,
`system/zookeeper-buggy-detect`, `system/solr-buggy-detect`; forks
`graphchecker/{hdfs,hbase,zk,solr}-bug-<jira>` in `/bulk/hadoop`, `/bulk/hbase`, `/bulk/zookeeper`, `/bulk/solr`.

Engine support on these branches only (each independently reviewed): HBase 948e4779f (reply legs of a turn's earlier
requests are control producers), f82385bcc (ledger in hundredths; also on Solr 35a513aa7); ZooKeeper bba07d7d1 (CONFIRM
holds at the nearest instrumented claim); HDFS (merged e2cff35b1) ba6580331 + 131bf16d9 + 7f562ef37 + 252ed18da + 6a7c74e61 + 838b0c888
(earlier/later-write overtaking, per-version proposals, hold after the overtaken write's frame). Rejected and reverted: HBase
455a6dd66 (REPRODUCE by shape).

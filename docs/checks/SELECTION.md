<!-- Moved into the repo at the 2026-10-05 handover from /bigtemp/vnr3ne/analysis/study-2026-10-04/SELECTION.md (investigator tables of 2026-10-04, read against our trees). Ids never move. Live status per check: docs/checks/README.md and docs/handover/STATE.md. -->
# Narrowed selection (owner ruling 2026-10-04 late morning)

Owner: per system a SUBSET of the earlier study.txt points -- HDFS 38 points / 36 checked, Solr 21 / 13, HBase 30 /
17, ZooKeeper unchanged (13 / 10). Chosen for: GraphChecker adapts to and covers them, they interact with the control
plane, and a checked point has a high-quality cluster unit test (self-written only for a high-quality bug without
one). Every known bug (named cases, bug_study admissions) stays a check, and every study point a known bug sits on is
kept. One point may carry several checks (several cluster tests or bug paths): more checks than points is good.
Numbering stays the study numbering (hdfs-adhoc-NN, solr-adhoc-NN, ...): ids never move.

## HDFS: 38 points, 36 checked (+ 10 named bug checks)

Checked (36): 01, 05, 07, 08, 09, 10, 11, 12, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
33, 34, 35, 37, 39, 40, 43, 48, 49, 50, 52.
Swapped (owner 2026-10-05, "32直接换成05吧"): 32 out, 05 in. 32's removal of the block pool from
`bpByBlockPoolId` runs in the exiting actor thread, which started before the window (unnamed work), so no explored
world can reach the throw; the startup window (rounds HG8W) diverged in cluster start-up. 05 (the QJM output stream's
buffer flush, NN->JN, `TestQuorumJournalManager#testSingleWriter`) is the first alternate of the swap rule: UNSAT at
its fixed point in round HG8W.
- QJM writer/journal epochs 07-10; block-token keys 11, 12, 14 (11 carries hdfs-17897, 17899-bug1/2/3, 17967-pathA/B/C,
  11741); NN block state vs commit 15-17; NN commands and HA txid at the DN 19, 20; NN/DN version handshake 21; DN
  storage vs NN namespace at registration, upgrade and rollback 22-27, 34, 35, 37; block recovery vs block-pool
  shutdown 28-31; hot swap 33; QJM output stream 05; append vs IBR 39, 40; truncate vs recovery 43; rename / snapshots 48-50,
  52 (52 carries hdfs-17960); client located blocks vs NN 01.
Points without a check (2): 13 (4-argument token password check: no cluster test), 18 (PROVIDED storage injection:
no hadoop-hdfs cluster test reaches it inside the window).
Dropped (15): 02, 03, 04 (client-local DataStreamer state / ack timeout), 06 (local double buffer), 32 (swapped out), 36 (no test),
38, 41, 42, 44 (request validation / file policy), 45, 46, 47 (local state machine, format, fsimage load), 51, 53
(debug dumps).
Named bug checks (10): hdfs-11741, hdfs-17897, hdfs-17899-bug1/2/3, hdfs-17960, hdfs-17967-pathA/B/C,
hdfs-bugs-slowdisk-zero (its own point, RoundRobinVolumeChoosingPolicy:84).

## Solr: 21 points, 13 checked (+ 8 bug checks)

Checked (13): 05, 07, 09, 10, 13, 14, 19, 21, 22, 31, 38, 39, 40 (22 = solr-18406's throw).
Points without a check (8): 01, 06, 15, 16, 18, 34, 36, 37.
Dropped (19): 02, 03, 04, 08, 11, 12, 17, 20, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 35 (request validation,
startup config, test hooks, local invariants, unreachable or untested).
Bug checks (8): solr-18406, solr-18413, solr-bugs-reindex-cleanup, solr-bugs-{migrate-buffer-leak, overseer-lock-leak,
snapshot-no-active, restore-construction, tra-start-overwrite}.

## HBase: 30 points, 17 checked (+ 3 bug checks)

Checked (17): 04r, 07r, 08, 10, 11, 12, 13, 14, 15, 19, 20, 21, 22, 24, 31, 34, 37.
Points without a check (13): 01, 02, 16, 17, 18, 23, 27, 28, 29, 30, 32, 33, 35.
Dropped (8): 03, 05, 06, 09, 25, 26, 36, 38 (NO_PATH, no coordination).
Bug checks (3): hbase-bugs-master-active-time (#14), hbase-bugs-backup-lock-reply-lost, hbase-bugs-ns-rsgroup-removal.

## ZooKeeper: 13 points, 10 checked (+ 3 bug checks), unchanged

Checked (10): 01, 02, 03, 04, 06, 07, 10, 11, 12, 13. Points without a check (3): 05 (dead throw), 08, 09 (NO_PATH).
Bug checks (3): zk-bugs-quota-init, zk-bugs-election-offer, zk-bugs-container-reuse.

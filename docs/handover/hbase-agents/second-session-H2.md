# H2 (ZooKeeper; #11 master-active-time, 24, 34, 37): second session, 2026-10-19 23:50 to 2026-10-20 11:10

All four cases are finished; no process of H2's is left on any lift. Runs: `/bigtemp/vnr3ne/gc-out/hbase-zk/accept-<TAG>`.

| case | run | verdict | vacuity | time |
| --- | --- | --- | --- | --- |
| hbase-bugs-master-active-time (#11) | NZ12-mat; native rerun repro-NZ13-mat | **PASS**: SAT MARKER_FLIPPED, moving only `CONFIG:causynth.hbase.master.clock.skew.ms.later` = -2001 (master1's configured clock skew); confirmed in the VM; report.py PASS; reproduced natively 3/10, control 0/10 | not vacuous | 810 s (+ 6 min rerun) |
| hbase-adhoc-34 | NZ3-34 | **PASS**: SAT MARKER_FLIPPED (a ZooKeeper READ SessionExpired on keys/1's getData), reproduced 10/10, control 0/10 | not vacuous | 1684 s |
| hbase-adhoc-24 | NZ3-24 (light load) | UNSAT_CLOSED | vacuous: needs a znode's absence as state (TODO HBase 10) | 1739 s |
| hbase-adhoc-37 | HZ2-37 (first session) | UNSAT_CLOSED | vacuous, TODO HBase 10 | - |

#11's native 3/10: all 10 planted runs threw at master1's first report; 7 under another upstream anchor (native timing picks which
open request rs0 served), TODO HBase 11.

## #11: the path (what each attempt taught, LESSONS §9)
1. CONFIRM refused a CLOCK_SKEW claim whose root only re-run sessions minted -> CONFIRM looks the mint up in the arm session (2a42e96d4).
2. INITIAL pairing of master1's `masterActiveTime` read (no happens-before through the volatile `serviceStarted`) and other
   sessions' wall-clock constants on the hand-off arms.
3. A holder field moved the guard off `masterActiveTime`, so master0's activation was no longer demanded; an `= 0` initializer is
   useless (the engine's INITIAL is the value after `<init>`); a guard joined by `&`/`&&` has no term (branch-produced booleans are
   concrete in the VM); a run-relative clock moved the wall offset into a per-session JVM-start constant.
4. Owner ruling 2026-10-20: "#11可以直接workaround". Tree: in automatic mode `masterActiveTime` starts at Long.MAX_VALUE, and at
   activation is the master's start code (a run constant) plus `conf.getLong("causynth.hbase.master.clock.skew.ms.first|.later", 0)`
   (constant keys: ConfigRoots names only constant keys; one key = one symbol on every node, so per-master keys), with the skew's
   domain declared in `experiments/hbase/hbase-bugs/root-domains.jsonl` (+-600000).
5. Engine: the free-model witness keeps roots outside the selected path's cone at their recorded values (275e72578); a
   fatal-observing explored session's planted world is a valuation (49c5698b7) and REPRODUCE plants CONFIG roots at their getter;
   the native plant drops an answer equal to what the producer sent anyway (57de8ed4e).

## Commits
- GraphChecker `hbase-zk` (all merged, gated on lift10): f6e07b3c9 (declared-read receivers for PLAN's fetches), cf142b588 (34's
  ZOOKEEPER client faults), 2a42e96d4 (CONFIRM mint lookup), 9bee1d02c / e25774a82 / dc8e095d2 (root domains), 275e72578,
  49c5698b7 (= 81970af67 + merge), 57de8ed4e, docs 54aacfe3f, a11779416, 59b6eb253, 4b5266eed, 92ee77a9e.
- Tree `gc/hb-zk` (all in `gc/hbase-checks`): 5e7f0688a5 (34's workload), b52b4f06ce (24's light load), 8073aa2e77, e2e501c48e,
  190d7eda00 (#11's workaround), 26bae096c3 (merge).

## Left
TODO HBase 10 (absence as state: 24, 37), 11 (native upstream-anchor drift), 17 (no happens-before through a volatile publication),
20 (the formula pins `.later` to -2001 alone). Snapshots `gc-run/hb2-zk-1..8` and tree sets `wt/hb2-zk-trees-1..10` kept; hb2-zk-7,
hb2-zk-8 and trees-10 are #11's evidence. Readings: `/bigtemp/vnr3ne/analysis/hbase-2026-10-20/readings.md`; offline evidence
`analysis/hbase-2026-10-20/zk-offline-nz10..12`.

# SURVEY-runtime — cleanup round 3 (S3), read-only survey of `runtime/` (2026-09-16)

Tree: `/tmp/claude-20003/-opt-GraphChecker/99c84a54-86ac-44a4-a030-760f664ae2a1/scratchpad/wt-stage`, tip **089a36aad**
(`git log --oneline -1`; worktree clean). Package `src/main/java/edu/uva/liftlab/graphchecker/runtime/` =
**26 files, 24,639 lines** (`wc -l`). No edits, no builds, no campaigns were run.

## 0. Method, honesty ledger, in-flight areas

- Member spans: `cleanup2/members.py` (brace matcher) → `cleanup3/members.txt` (2,237 rows). Cluster line counts are
  **disjoint line ranges** summed by awk (`cleanup3/crr_clusters.txt`, `cleanup3/rrp_clusters.txt`); CRR ranges cover
  6,421 of 6,467 lines (the rest are single blank/brace lines between clusters), RRP 3,493 of 3,529.
- Reader counts: `cleanup3/refs.sh <OwningFile> <name>…` greps `\bname\b` over `src/main/java`, `src/test/java`,
  `/opt/hadoop-hdfs-*`, `/opt/solr`, `run_engine.sh`. Every "0 readers" below is that script's output.
- **Read in full by me**: ConcolicRegionRuntime (6,467), RuntimeRegionPlanner 985–1480 + 1560–1745 + 2064–2140 +
  member map, ConcolicTaskPlan 54–560 + member map. **Not read**: RRP 77–984, 1481–1559, 1746–2063, 2141–3528 bodies
  (verdicts there rest on the member map + call-site greps and say so); ConcolicTaskPlan 560–1796 bodies.
- The other five file groups were read in full by three parallel readers whose reports I merged and spot-verified
  (`mergeBatch`, the two workload passes, `dependencyRole` census re-measured by me).
- **Firing evidence** is the clean 17960 campaign `$MY/final-6f6f88ec6/out/hdfs-17960` (verification #7, the pass that
  closed the case) and the 11741 corpus `$MY/final-05f4bf265-11741/out/hdfs-11741` (campaign #2, killed at wave 1;
  its sessions predate `SessionManifest`, so roles come from `$MY/x14/reconstruct-manifests.py`). `$MY` =
  `/tmp/claude-20003/-opt-GraphChecker/10153a9a-290a-45d1-b3c9-072f259e090e/scratchpad`.
- **Row census** (mine, `wc -l` over `schedule/iteration-0000/sessions/*/`):

  | corpus | sessions | activations (focused) | decisions | reads | writes | roots | targets | gaps | exports | attaches |
  |---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
  | 17960 | 3 | 266 (6) | 3,333 | 75 | 100 | 3 MARKER | 6 | 50 | 0 | 0 |
  | 11741 | 81 | 32,227 (721) | 8,318 | 16,083 | 25,206 | 1,021 (937 CLOCK, 84 INTEGRAL) | 194 | 11,805 | 53,424 | 3,554 |

  Context forms: 17960 ROOT 218 / ANCHOR 42 / **LOST 6**; 11741 ROOT 24,269 / ANCHOR 7,958 / LOST 0.
  Activation `instrumented=false`: 0 (17960), 24,961 (11741).
  **The only gap kinds that fire in either corpus**: `LINEAGE_LOST` (40 / 10,214), `TASK_UNANSWERED` (4 / 1,106),
  `MESSAGE_CONTEXT_REFUSED` (6 / 484) — all `cls=DIAGNOSTIC`. Every other refusal vocabulary in the package did not
  fire on either corpus; that is stated per cluster, and it is *not* by itself a deletion reason.
- Plan census: `execution_task_plan.jsonl` 45 rows (17960) / 84 (11741); `goalKind` = TARGET_REACH_CLOSURE 2 / 4, rest
  REGION_PATH_CLOSURE; every row `admission.state=EXECUTABLE`, 0 blockers; `targetBranch` on 2 / 4 rows;
  `observedWriteSites` non-empty on 2 rows (17960) and 0 rows (11741); `edgeBindings` non-empty on **every** row
  (up to 1,568 entries); `dependencyRole` = VALUE_FRONTIER 14,004 / CONCRETE_STRUCTURE_CARRIER **86** (17960), 21 CSC (11741).
- **In-flight, do not collide**: X15 owns `explore/ObligationFactory` + `runtime/FocusedReplay` focus rows (marked
  in §1.9 and excluded from every mandate below). No G/C mandate is open on `runtime/` at this tip per the memory log
  (`graphchecker-refactor-goal.md` tail: X14 merged 6f6f88ec6, 089a36aad is the artifact commit).

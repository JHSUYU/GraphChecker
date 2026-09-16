---
name: subagent-rules-of-engagement
description: "Checklist every Opus subagent prompt/mandate must contain (owner 2026-09-13: \"你要好好控制子agent，说清楚你的要求，要不然子agent就乱搞了\")"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 3230912f-3427-4c18-a306-eb2005a43b37
  modified: 2026-09-13T20:06:30.026Z
---

Every subagent mandate states, explicitly:
1. **Design frame** — link/paste [[graphchecker-core-design-principle]]: runtime propagation carries values; the graph only scopes; composer = ⋁(π∧φ) per anchor. Any change that adds a rule deciding "what matters" outside the root-dependence slice, or reconstructs values offline, is REJECTED at review.
2. **File ownership** — exact directories/classes the agent may edit; everything else read-only. Parallel agents never share a file.
3. **Definition of done per chunk** — tests green (`mvn -o -q test`), offline validation on NAMED corpora with expected observables (e.g. laneZ FINAL_READY; laneAR allKeys contains SYM[X]), line counts before/after for the files touched, gap codes registered in GapLedger, report path + tip.
4. **Forbidden** — no campaigns mid-round (one per case at the end, only when told); no git checkout/stash/reset/commit/clean in /opt/hadoop-*; no edits to other worktrees or main; no engine code naming HDFS classes (config only); no new heuristics/caps/defaults; no "synthesize a value" fallbacks; no merging (planner merges).
5. **Reporting** — facts with evidence (file:line, corpus rows); say plainly when acceptance is NOT met; do not stop to ask when a fail-closed generic choice exists; commit early (rate limits).
6. **Planner review before merge** — read the report, grep the diff for forbidden patterns (new candidate/arm/selector logic, HDFS names in src/main, unregistered gap codes, silent fallbacks), run the suite, then merge.

**Why:** on 2026-09-13 agents drifted (stitching patches, a fail-closed change that broke the seed replay, campaigns after every chunk) whenever a mandate left one of these implicit.

**Added 2026-09-13 17:30 after the laneAW regression:**
7. **Deleting a published member** requires listing its readers by `git grep` on the merged staging tip AND on every in-flight branch, in the commit message. (Chunk 4 of the runtime round deleted `OBSERVED_COMMUNICATION_CAPTURES` with three live readers → PLAN died for bug3/17897/11741.)
8. **Integration campaign after every merge**: run 17960 (≈9 min) on the merged tip before starting the next round. Two rounds green on their own branches were red together (laneAW).
9. **Validation corpora must not be pruned**: the harness prunes each case dir to CASE_CAP_MB (300 MB) at case end, deleting worker summaries/obligations needed for offline re-drives. CASE_CAP_MB does NOT stop pruning (the keep-list is applied regardless; the cap is only reported). Since 2026-09-13 20:50 launch validation lanes with `FINAL_KEEP_ALL=1` (lib_final.sh skips fin_prune_case).

**Added 2026-09-14 11:00 (owner: "测试太多了，测试要始终维持在几十个，不许超过100个"):**
10. **Test cap**: src/test stays at a few dozen `@Test` methods, hard cap 100. Every mandate says "no net new @Test methods": fold a new behaviour into the existing rule's test (assertion or table row) or replace the test it supersedes; report before/after counts. See [[test-count-cap]].
11. **Never rebuild a case's /opt/hadoop-* tree while a lane on that case is running**: the harness freezes productionClasses at SETUP and refuses at EMIT if the tree's sha changed ("frozen input productionClasses changed after it was frozen"), voiding the whole run (lane11741h, 2 h lost on 2026-09-14). Check `$SP_NEW/lane*/launch.log` for a START without END on that case before any tree rebuild.

**Added 2026-09-14 22:45 (owner: "你要对子agent控制的比较好，你自己不能太信任子agent。你要规划的比较详细，包括对他们代码读写的反馈"):**
12. **Do not trust subagent reports at face value.** Every mandate is detailed (files, corpus, expected observables, exact commands). After each report the planner gives explicit feedback on what the agent read and wrote (what to keep, what to revert, what it missed), verifies the claimed evidence with its own light checks (grep the diff, count tests, look at the named corpus rows), and only then merges or re-dispatches.

**Review rule added 2026-09-15 (evening, after R1/S1):** a subagent's "set by nothing / no reader" claim is accepted only with the grep it ran, and the grep must cover `run_engine.sh`, ALL of `experiments/**` (the per-case adapters `execute.sh`/`run.sh`/`case.sh`/`classpath.sh`/`workflow.properties`), `src/test/**`, and the hadoop trees' `src`. S1 and R1 both declared `causynth.junit.ignore.timeout` "set by nothing" while every `experiments/hadoop/*/execute.sh:40` passed it; R1 then deleted the only runner that could run the JUnit 5 workloads, which the one thorough verification caught (R3 restores one runner). The planner spot-checks one such claim per mandate with its own grep before merging.

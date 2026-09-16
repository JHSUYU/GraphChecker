---
name: serial-campaigns-only
description: User ruling on campaign concurrency — was strictly serial (2026-09-12 morning); relaxed 2026-09-12 20:00 to at most TWO campaigns in parallel under conditions
metadata:
  type: feedback
---

2026-09-12 20:00 the user approved ("OK。那就两路吧") at most TWO experiment campaigns in parallel, replacing the earlier strict-serial ruling ("我们先一个一个跑通吧，不要并行跑了"). Conditions I proposed and they accepted: (1) never a third lane (disk peaks 6–10 GB/case); (2) z3 verdicts from inside a campaign are not trusted — re-run probe_final.sh on candidate.smt2 when the host is idle; (3) both lanes share one frozen jar, no rebuild while either runs; (4) pair a heavy case with a light one (bug3+11741, then bug2+17897, bug1 last after the owner fixes its try/catch); (5) do not start lanes on stale experiment config — wait for fix/experiment-config to land.

**Why:** two campaigns + profiling once drove load to ~51 on 40 cores and turned sat formulas into z3 timeouts; with load ~2.5 and 187 GB RAM two lanes are safe if verdicts are re-probed offline.

**How to apply:** before dispatching, `ps` for running run_branch.sh/run_engine.sh; at most one other lane may be active; other agents may still do offline work but at most one heavy JVM (≤16 GB) alongside. Related: [[graphchecker-verification-runbook]], [[graphchecker-refactor-goal]].

**Added 2026-09-15 06:30 (planner):** never `git merge`/edit/rebuild in `$SPO/wt-stage` while a lane runs FROM it — bash reads run_engine.sh incrementally and each stage re-reads the jar; merges of finished agent branches wait until the lane ends (E5 e9d3e489c was held for laneA3 for this reason). Use the Monitor tool (until-loop on the campaign log) instead of polling by hand.

**Added 2026-09-15 13:50 (planner mistake):** before deleting a VM image or a worktree, `pgrep -af '<path>'` — a recording launched by an agent was still running on build20 when I deleted it (the JVM survived on open files, but a relaunch would have failed). Delete superseded images only after every lane/record is confirmed finished.

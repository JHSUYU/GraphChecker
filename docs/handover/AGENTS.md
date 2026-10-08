# Working with agents (the owner's rules and the leads' method, long-term)

This file is part of every agent's long-term memory ([RULES.md](RULES.md)). The binding numbers, from
the owner on 2026-10-04 ("具体写代码coding agent最多4个。读，reveiw的可以稍微多点。但是reveiw要在关键，复杂的地方采用"):
- **At most 4 coding agents at once.**
- Read-only investigators and reviewers may be a few more.
- A review agent is used only at key, complex places: VM, schedule and identity, soundness of
  COMPOSE and CONFIRM. One per batch, before the merge.
- A slot is refilled only with work on the current round's critical path.

The rest of this file is how the leads applied that, with their lessons. It ends with the
2026-10-06 session.


The owner wants throughput: "这里明显能并行的你就并行。你自己管理好代码分支，之后的merge什么即可" /
"这种多个job明显可以并行啊" / "总之，你要积极主动地利用多agent。去审查代码细节。一旦你有不确定就要去找". And
a budget: "合理分配多agent", "减轻一些fan out的规模".

**When to use an agent**
- Any job with **no dependency on another job runs NOW, in parallel, whatever phase it belongs
  to**: independent work packages, offline gates, live rounds, investigations. Serialize only on a
  real dependency (a package needs another's merged API; a round needs a fix merged).
- Root-causing a failed campaign, implementing a written work package, a code audit of a stage,
  and an independent review of a large diff are agent jobs.
- The moment you are unsure about a code detail (what a function does, whether a capability
  exists, why a run failed), send an agent to find out instead of assuming.
- Do small things yourself: a targeted grep/read, a small fix, conflict resolution, merges,
  reviewing a short diff.

**How many and how**
- **At most 4 coding agents at once** (owner 2026-10-04: "具体写代码coding agent最多4个。读，reveiw的可以稍微多点。但是reveiw要在关键，复杂的地方采用"; read-only investigators and reviewers may be a few more, reviews only at key, complex places; refill a slot only with the current round's critical path) (the owner's budget: "不要无限制地让子agent fan out"; seven at once burned the weekly
  usage limit in two hours on 2026-10-02) plus short read-only reviewers; no agent spawns sub-agents; ask for short reports (≤ 15–20 lines);
  no idle polling loops (use a background command that exits on the condition, or a monitor).
- Every coding agent gets its **own git worktree** (`isolation: worktree`) and branch, a disjoint
  file area where possible, and a prompt that states: the goal, the evidence (paths to runs), the
  spec section, the rules (general code, docs in the same commit, lean tests, never push, never
  `git add -A`, the pre-commit commands), the validation to run (offline gate cases and rounds),
  and the report format.
- Continue an agent with its previous context (send it a message) rather than starting a new one
  when the next task is in the same area.
- **The lead owns main:** review every diff before merging; resolve conflicts yourself; keep main
  green (`mvn package` + shell test after each merge).
- **Review policy:** small/medium changes — the lead reviews. Large or high-risk batches (VM,
  replay/schedule, identity, soundness of COMPOSE/CONFIRM) — ONE independent review agent per
  batch, BEFORE merging, then a live round. Reviewers are read-only and cite file:line.
- **Merge gate:** the offline regression gate (`tools/regress/offline-ab.sh`, [OPERATIONS.md](OPERATIONS.md) §6) for every change
  to SEED/PLAN/EXPLORE/COMPOSE/CONFIRM; a live round for VM, runtime, identity or replay changes.
  Verdicts and moved roots must not change unless the change is meant to change them, and then the
  `.smt` chains are checked by hand.
- Campaigns run from **frozen snapshots** (`~/gc-run/p<N>`), never from the working tree. Scripts
  set their own environment (`tools/lib/gc-env.sh`, `onlift.sh`).

**The mechanics in Claude Code** (what the previous lead actually did)
- Start a coding agent with the Agent tool: `subagent_type: general-purpose`,
  `isolation: "worktree"`, `run_in_background: true`. A read-only reviewer or investigator needs no
  worktree. You are notified when an agent finishes; never predict its result before that.
- Continue a finished or running agent with `SendMessage` (its id); it keeps its context. Stop one
  with `TaskStop`.
- Watch rounds with a `Monitor` on `round-monitor.sh … | grep --line-buffered 'DONE '` (it expires
  after 30 min; re-arm it; a re-armed monitor re-reports finished cases). For a single wait, run a
  background Bash command that loops `until <condition>; do sleep 30; done` and exits.
- A typical cycle: a round finishes → read each failure yourself (summary, log, report, gaps: a few
  minutes) → one agent per distinct root cause with the evidence paths → review its diff → merge →
  new snapshot → next round, while other agents keep working on independent packages.
- Prompt skeleton for a coding agent: *context* (repo, main sha, what is on main that matters) →
  *problem with evidence* (run paths, error lines, row ids) → *task* (trace the code first; fix
  generally; what not to touch) → *rules* (worktree only, never push, never `git add -A`, commit
  trailer, `mvn -q -o package` + shell test via `onlift.sh` before each commit, docs + STATUS in the
  same commit, lean tests) → *validation* (exact `offline-ab.sh` command and cases; a live run on
  its own snapshot with its own round name when runtime/VM changes) → *report* (≤ 15 lines: commits,
  evidence, gate lines, what is left).
- Keep a short state note current for yourself (the 2026-10-03 lead used
  `~/.claude/projects/-u-vnr3ne-GraphChecker/memory/lead-session-<date>.md` (the 2026-10-04 lead: `lead-session-2026-10-04.md`), one dated paragraph per
  milestone), and keep [STATE.md](STATE.md) and [TODO.md](TODO.md) current: a docs commit after every merged round.

**How the 2026-10-02 night lead ran the agents** (eleven agents over the session, seven at once)
- **Investigators first, read-only, one per system.** To choose the checks, four general-purpose agents (no
  worktree, no build, no runs) each read one system's bug descriptions against its source and returned ONE
  compact table: per bug, present in our version (file:line of the fatal throw), real?, coordination?, the
  single counterfactual that flips a passing run and where, the best existing workloads, a fit rating, then
  their top picks. The lead then read the code of every pick itself before deciding; an investigator's
  table is evidence, not a decision.
- **One coding agent per work package, never two on one package:** `isolation: worktree`, `run_in_background`,
  a branch named in the brief, an explicit base ("from main c2c920098", or "main + merge X"), and for a new
  system or bug its OWN system tree (a new worktree of the system repo on a new `gc/<name>` branch under
  `/bigtemp/vnr3ne/wt/`, built with its own Maven repo `/bigtemp/vnr3ne/m2/<name>`), so no agent rebuilds a tree
  a round or another agent reads.
- **The brief** (each was ~40-60 lines): context and what to read first (README sections, design docs, the
  model adapter or commit to port), the bug or goal with file:line evidence the lead verified, the design to
  follow (the lead's, stated as rules, e.g. "the adapter registers each server as a node with the objects it
  runs work through; open the window once the cluster is up"), phases with a GATE where the agent stops and
  reports (e.g. HBase: feasibility on JDK 8 and the VM before any adapter), the rules (general code, no dead
  code, docs + STATUS in the same commit, lean tests, never push, never `git add -A`, commit identity and
  trailer, `mvn -q -o package` + shell test via `onlift.sh` before each commit), validation (the offline gate
  on the newest all-PASS round for engine changes; at most ONE live campaign at a time, from a frozen snapshot
  of the agent's own branch, in the agent's own `GC_OUT`, stopped before reporting), and a report of at most
  15-20 lines.
- **Scope changes mid-flight go by `SendMessage`** to the running agent (e.g. "drop check 3: its throw is the
  fault's echo"), never by a second agent.
- **The lead keeps for itself:** reading and verifying bugs, the design, merges and conflict resolution, live
  rounds of the eleven cases, `.smt` chain checks, the cleanup of artifacts, and memory/README.
- **Budget:** seven agents at once burned the account's weekly usage limit in about two hours (2026-10-02
  ~19:40-21:00), stopping all of them mid-edit. Run at most 3-4 coding agents at once, give each a package
  that can commit in small finished steps (commit after every working step, not at the end), and keep WIP
  small. When the limit hits, follow the last bullet of the lessons below (save WIP patches, reap runs).

**Lessons from 2026-10-02 (the last lead's day: 8 coding agents, 2 reviewers, rounds V4–V9)**
- **Tell every agent its base** explicitly ("from main X", or "on the V7 stack = main + dtx + …"):
  work that depends on an unmerged branch (DataTransfer identity, for instance) must sit on it, and
  the merge order then follows the dependency.
- **Agents' own live runs share the cluster with your rounds.** Several agents each running
  campaigns (plus your round) push every lift to its ledger ceiling, so heads wait for memory and
  times double. Ask agents for offline evidence first, at most one live run at a time, in their own
  `GC_OUT` (`/bigtemp/vnr3ne/gc-out/<branch>-*`), and to stop what they started before reporting.
  Judge a crowded round by verdicts and per-obligation replay times, not wall time.
- **Brief reviewers with the owner's principles** (over-approximate, confirm strictly; completeness
  first), so they rank findings the way the owner does. Both reviews this day found real blockers
  that live rounds had passed (a budget that would stop ad-hoc exploration after ~10 min; a
  CONFIRM substitution comparing no value).
- **A failure in a validation round is not automatically the branch's fault:** rerun the case on
  plain main (`M1` showed 11741 passes on main by the order it gets) before blaming or merging.
- **The account's usage limit can stop every agent at once,** mid-edit. Resume each with
  `SendMessage` ("continue where you were"); they keep their context.
- **When agents are stopped for good,** save any uncommitted diff as a patch
  (`/bigtemp/vnr3ne/handover/`), then reap their runs on every lift by a path only those runs carry
  (their worktree or `GC_OUT` directory), feeding the pattern through stdin (`ssh <lift> 'bash -s' <
  script`), never on your own command line ([OPERATIONS.md](OPERATIONS.md), traps), and remove ledger entries whose pid is gone
  (`$CAUSYNTH_HOST_LEDGER/explorations/`).

**How the 2026-10-03 lead ran the agents** (one lead, four coding agents, six reviewers; rounds V16-V25,
eleven merges into main, none reverted)
- **Four coding agents at once, each owning one area for the whole session:** A1 (STATE pairing for HDFS #15,
  then happens-before), A2 (Solr #04 and Solr replay fidelity), A5 (ZooKeeper #05, `pairing-on-main`, the
  ledger lease, the slicer's matched calls, WIRE-CODEC), A6 (VM: streams, model guards, read-out streaming, heap;
  then HBase). Continuing an agent in its area by `SendMessage` kept its context; new areas went to whoever freed
  up first. No agent spawned sub-agents (one reviewer did; tell reviewers "do NOT spawn sub-agents").
- **Design before code for anything that changes identity, the schedule or what is symbolic:** the agent reads
  the code and sends a ≤ 20-line design; the lead approves, adjusts (often "one mechanism, not two: reuse X"),
  or rejects; only then code. Agents also stop and ask when their own diagnosis turns out wrong (A5 did, twice:
  each time the corrected cause was different and the planned fix would have done nothing).
- **A pre-merge review agent for every soundness/schedule/VM batch** (vm-model-guards, slowdisk-dev,
  slice-matched-returns, solr-bug-reindex, hb-schedule + hb-sync): read-only, briefed with the owner's principles
  (completeness first, CONFIRM strict, one mechanism), ≤ 40 lines, blockers first, file:line and a concrete
  scenario each. Every one found real blockers that the offline gate and the live runs had passed (a vacuous
  INITIAL check, a CONFIRM rule looser than WIRE's, false orders that silently drop alternatives, declared target
  regions dropped by a root rule). The author fixes them all; the lead decides the disputed ones.
- **Merges in a dedicated worktree** `/bigtemp/vnr3ne/wt/main-pw`: per round a branch `main-<x>` from main, `git
  merge --no-ff` the change, resolve conflicts by hand (two implementations of one concept become one interface),
  `mvn -q -o package` + shell test via `onlift.sh`, commit, `tools/lib/worktree-add.sh ~/gc-run/p<N> <commit> --detach`, build it,
  `launch-round.sh` all regression cases, a `Monitor` on `round-monitor.sh`; on all-PASS fast-forward `main` to
  the candidate, then a README/STATUS docs commit for that round.
- **Canaries before a full round** for large changes (WIRE-CODEC: 11741 + 17897 first), always launched through
  `launch-round.sh` (all ten lifts).
- **Watch the agents' runs as well as your own:** read their logs when a stage is long; three of the session's
  biggest finds came from the lead checking a run that "was still going" (SB16's hung recording, SB11's memory
  overload, a canary on one host).

**Lessons from 2026-10-03**
- **Strict is not broad.** Tightening CONFIRM ("only a world that plants nothing is itself the run") forced
  replays for nine passing cases for no soundness gain; the reviewer caught it. Check which existing cases rely
  on a path before tightening it.
- **Narrowing roots needs the declared targets in view:** "region roots only at writers" would have dropped
  11741's target region and the clock regions.
- **Every false happens-before order silently drops real alternatives** (a completeness loss no gate shows):
  test each new edge kind against a batching or broadcast counterexample (a queue consumer flushing several
  clients' requests; a monitor with two notifiers).
- **One transport or queue thread may serve many nodes** (Hadoop IPC's `RpcRequestSender`): never refuse or key
  work by the thread's node.
- **Recordings run on stock HotSpot, replays on the VM:** check which JVM ran before blaming the image.
- **A host overload is first a ledger question:** the ramp-only charges let slow-growing Solr replays
  overcommit every host (fixed: leased charges).
- **A tree rebuild under someone's run corrupts their results silently** (A2 rebuilt a Solr tree under A6's
  replays): `pgrep` on all lifts before any tree build, every time.

**How the 2026-10-04 lead ran the agents** (the HDFS group; rounds HG1-HG5; about 25 merges into `system/hdfs`)
- **Rules file and briefs on disk.**
  - `/bigtemp/vnr3ne/analysis/study-2026-10-04/AGENT-RULES.md` holds the rules every coding agent
    gets: its own worktree and snapshot, its own `GC_OUT`, one live run at a time under the memory
    gate, a design of at most 20 lines first for identity, schedule, symbols or soundness, the
    deleted code listed in its report, no fallback.
  - Each work package has a brief file next to it (`brief-<name>.md`): the problem with evidence,
    the lead's decisions, the deliverable, the validation.
  - The agent prompt says: read the brief, AGENT-RULES.md, and the docs.
- **Integration branches per round.**
  - `hg4`, then `hg5`, in `/bigtemp/vnr3ne/wt/gc-hg4b`: the round's merged feature branches on top of
    `system/hdfs`, built and tested, a frozen snapshot `~/gc-run/hg<N>`, then a sweep of the 46
    (`tools/adhoc/sweep.sh`, 2 heads per host).
  - Feature branches touch the same docs rows, so `docs/STATUS.md` conflicts on almost every merge.
    Resolve them row by row with a three-way look at the merge base (keep each side's change to a
    row, merge both when both changed it). In code conflicts, call the merged API (e.g.
    `StaticScopeMap#fatalArm` plus `fatalDeciders`; `RootDemand.of` with both the writers' guards
    cone and the demanded doors).
- **Review agents found blockers every time.**
  - The decisive-verdicts batch needed two FIX FIRST rounds. The first: the export was the
    valuation-0 query, UNSAT rested on a capped enumeration, pins sat over moving values. The
    second: a cone exemption hid a lost binding, and CONFIRM refused way-guard witnesses as
    "refuted".
  - The VM container batch: list/set/deque iterators were admitted without a model.
- **Diagnosis agents for a slow or failed case** (read-only, at most 20 lines). The 11741 HG4 timeout
  turned out to be a remote-CONFIRM path bug, not an obligation explosion.
- **Probes before a round.** For a schedule change, the agent probes the affected cases' seed replays
  on its own snapshot, counting give-ups, to the target. Rounds DS5-DS8 showed that the keyed clock
  replay (C1) hurt the start-up family more than it helped, so C1 was parked.
- **When the owner stops the session:** SendMessage each agent "STOP NOW: stop your runs, commit your
  WIP, reply in at most 15 lines (branch, head, done / not done, next steps)". Stop the rounds with
  `stop-run.sh`. Then write the handover docs.

**Lessons from 2026-10-04**
- **A path a job stages to and the path its waiter reads must come from one place.** CONFIRM as a pool
  job staged sessions beside its worker while the remote wait looked under it: every remote
  confirmation was lost and no test covered it. Test the remote variant of every pool job.
- **The budget's reserve must cover every stage after the exploration** (COMPOSE, CONFIRM, EMIT,
  REPRODUCE). EMIT alone took up to 233 s.
- **Replaying a recorded clock in a window mixes two timelines.** State built from the live clock
  during start-up (heartbeat schedules) disagrees with replayed in-window time. Either both are
  replayed or neither.
- **A naming rule must be released on every path.** A request "in hand" after a door fault renamed
  every later thread start of that thread and broke a wire binding (bug2).
- **Watch a running round with a watcher that counts only finished rows.** A `summary.tsv` exists with
  its header from the start.
- **The owner reads progress as counts** (how many checks have a right `.smt`, how many known bugs
  pass, new bugs). Answer in those terms, in Chinese, briefly, before continuing.

**How the 2026-10-05 lead ran the agents** (one night, `system/hdfs` 43ba5d565 -> 2e89a9e69: ten merges, ~6,800 lines
deleted, rounds HG5A and HG7)
- **Four coding agents, each kept in one area across packages.** When an agent finished a package it got the next one
  in the same area by `SendMessage` (it keeps its context): COMPOSE/verdicts (decisive-verdicts -> closure E1 ->
  COMPOSE refactor and cost), identity (request-in-hand -> address-shared rule B -> planned shape -> anchored index),
  schedule (HG6 -> time model), driver/ledger (measured charges -> wire-half -> head reserve + WIRE-CODEC deletion ->
  SEED speed). Changes to one concept stay on one branch, so identity changes were serialized in one agent.
- **Read-only agents where they pay:** a dead-code audit (bytecode reachability + grep, a ranked deletion list), a
  diagnosis agent for the 11741 regression (one rerun with a debug print in its own snapshot: the real cause in 40 min,
  the lead's guess was wrong), and one review agent per soundness or schedule/identity batch before its merge.
- **Design gates.** Every identity, schedule, symbolic or soundness change sent a <= 20-line design first; the lead
  approved, narrowed ("one mechanism, not two": rule A was dropped because HG6's beginTick already covered it) or
  redirected (option A, a tree point, instead of an engine rule).
- **Briefs on disk** (`/bigtemp/vnr3ne/analysis/study-2026-10-04/brief-*.md`) with the evidence paths and the lead's
  decisions; short follow-ups by message.
- **The lead merged into `system/hdfs` directly** (worktree `/bigtemp/vnr3ne/wt/gc-hdfs`), each merge built and
  tested (mvn + the shell test via `onlift.sh`), conflicts resolved as the union of both sides' state; then told every
  agent whose branch sat on an older base to merge `system/hdfs` before validating.
- **A busy-file list** let the cleanup agent work beside three feature branches without conflicts (phase 1 = free files
  only; phase 2 after the merges).
- **The lead kept** the baseline round, reading every failure itself first (most causes were found in minutes from the
  formula, the gaps or the log), small general fixes (FREEZE's digest, array identities), the merges, the docs.

**Lessons from 2026-10-05**
- **A verdict is not real until checked**: how EXPLORE ended (FIXED_POINT / WITNESSED vs a budget cut), z3 on the
  exported file, moved roots (`tools/rounds/round-verify.sh`). HG4's "23 UNSAT" hid budget cuts and a silently wrong
  read; the decisive rules made them RUN_DEFECTs, so the count dropped before it rose.
- **Measure before designing**: replay peaks vs charges (one grep of the replay logs) made the measured-charges design
  obvious; an strace of one static pass found SEED's real cost (failed NFS stats), not the guess (contention).
- **A correct new detection can look like a regression**: vm-hg5's outside-mutation mark exposed 11741's unplanned
  key-update occurrence that the old VM missed silently; the fix belonged in admission, not in the VM or COMPOSE.
- **Reviews keep finding blockers**: decisive-verdicts (4: a skipped self-check, under-counted cuts, a second "moves"
  walk, silent path drops) and HG6 (draw keys moved by GROW). Never merge such a batch unreviewed.
- **Kill by pid, never by pattern**: an agent's pattern kill hit another agent's offline gate on lift11; the lead's
  `stop-run.sh` with a run's path in the same command line killed its own shell.
- **`onlift.sh` runs over ssh, which drops exported variables**: pass them on the remote command line (`onlift.sh ...
  env VAR=... cmd`), or a build may write `~/.m2`.
- **Agents' live runs and the lead's sweep share the ledger**; judge any run by stage times and queue waits.

**How the 2026-10-05/06 lead ran the agents** (`system/hdfs` 75dd26444 -> 176acc689 and the docs after: fourteen merges,
rounds HG8F, HG9, HG9B, HG9L, SW1, HG10V; four coding agents A1, A2, A4, D1 and four review agents)
- **Each coding agent kept one area across packages**, continued by `SendMessage`: A1 COMPOSE/claim (claim loop -> (b2)
  RestsOn: EXPLORE demands what COMPOSE keeps -> export weave + witness chain closure), A2 schedule/time (time model ->
  IPC hand-off naming, r6 trees), A4 scope/driver (clock placement -> bound mark -> guard decider -> codec capture),
  D1 EXPLORE/identity (prefix span -> frontier depth + owed-path bound -> solver fallback, rule 1).
- **Design gate, then sorted by the goal.** Every symbolic/identity/schedule change sent a <= 1-page design first. The lead
  asked each to sort its holes into (A) "the current `.smt` is wrong or incomplete" (fix now) and (B) "right, widening
  only makes more flippable" (after the 46); A4's scope batch 2 shrank to two (A) holes that way.
- **A review agent before every large merge** (time model, (b2), decider): read-only, briefed with the owner's
  principles and the exact focus questions (soundness, completeness, rules, tests), file:line findings with a concrete
  scenario. Every one found real issues the gates had passed: the time model's 120 s pre-window stand in every replay,
  (b2)'s two-hop handoff and session-wide over-demand, the decider's silently closed open arm (39). The author fixed them,
  the lead merged.
- **Small changes the lead reviewed and merged itself** (clock placement, claim-loop fixes, bound mark, confirm-first,
  shim stubs), each built and shell-tested via `onlift.sh` on the merged head; a combination of two large merges got a
  small live check (HG10V) before more merges.
- **The lead ran the rounds and the checking** (HG9 35 cases, HG9B named bugs, budget-cut reruns HG9L-*, the swap's SW1),
  verified every finished case with `round-verify.sh`, and sent each new failure class to the agent owning that area with
  the evidence paths (12's and 14's unbound handoffs to A1, 05/06/08/09's bound to D1).
- **Two agents' Hadoop hooks share one tree generation** (A2's IPC hand-off naming, A4's codec door calls on
  `gc/hdfs-study-r6` and `gc/hdfs-11741-r6`): the shim entry points the trees call were merged first as inert stubs, so
  any jar runs on r6, and the trees are built once with both.

**Lessons from 2026-10-05/06**
- **A "done" count must pass CHECKING.md §1.** The lead counted 07 and 14 done before round-verify read `cone.json`
  (UNBOUND), and 05/06/08/09 before the bound was visible. Add a column to the check, not a note to memory.
- **Under a full sweep, a case's budget is the cluster's, not the case's**: 20 concurrent heads cut six cases at 90
  min; rerun them at 3 h (`HG9L-*` job files), and give the final round 3 h from the start.
- **Agents' offline gates can jam a host**: dozens of `offline-ab.sh` waiters each refreshing the ledger over NFS put 254
  processes in D state on lift11. Gates go through `onlift.sh` off lift11, a few cases at a time.
- **Check every background wait for an end condition**: `pgrep -f` on a string the waiter itself contains never ends;
  a chain of waits on a wait's output never ends once the first's condition cannot happen. Stop stale ones (the lead
  stopped six) and tell the agent.
- **An agent's own scratch files live in the session's temp directory**: copy what a successor needs (patches,
  scripts) to `/bigtemp/vnr3ne/handover/<date>/` at the stop (D1's rule-1 prototype lived only there).
- **The order of merges follows the dependencies the agents name**: export weave before codec capture; time model
  before hand-off naming; shim stubs before any r6 build.

**Lessons from 2026-10-06 (the last HDFS session: agents T C R S, the two-branch end)**
- **An agent that stops before coding saves a wrong rule.** T was told to let a world's refutation stand against a
  later unfaithful replay of the same obligation id; it read the facts first and found the two asks were different
  worlds sharing one id, so the rule would have closed an arm over a world no replay answered. Brief agents to
  report the facts that contradict an order before carrying it out.
- **Time-box the tail.** With the owner waiting for the end, every agent got a deadline and an acceptance line ("at
  least one clean run on the final head, the variance named"); open questions past it went to TODO, not to more runs.
- **Per-case workarounds are agent work too** (owner: the last open cases by workarounds): R's 21 workaround was one
  tree hunk and two case files, no engine code, gated by one live run; C's 07 workaround one tree hunk plus a world
  depth. Ask for the smallest one first and the general design into TODO.
- **Two live runs per agent at most** (owner, RULES); a third case waits or replaces the least useful run.
- **A run on an old jar misleads**: C's CC7-11741 stalled on a defect fixed in the merged body but not in its branch;
  check a slow run's snapshot against HEAD before asking an agent to diagnose it (CHECKING trap 17).


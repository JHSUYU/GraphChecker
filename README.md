# GraphChecker

GraphChecker is an academic research tool in software engineering. It studies how open-source
distributed Java systems (HDFS, Solr) fail under fault, clock and ordering counterfactuals.

It starts from one recorded run of a system's own cluster test that does **not** fail, plus one
declared failure site (a `throw`, named by its class and source line). It then asks whether a
small change could have made that run fail at that site, and it answers with a witness. The
changes it considers are a transport fault, a skewed clock, a flipped configuration value, or a
different pairing of a message or of shared state.

A witness is a quantifier-free SMT formula (`candidate.smt2`), a claim naming what moved
(`claim.json`), and one replay confirming that the program agrees (`confirm.json`). Replays run
on a concolic OpenJDK 8 (Zero) that keeps a symbolic expression under every value. The formula
is composed from many focused replays, and the solver picks the nearest world. What the rows do
not state is refused by name, never defaulted.

**If you are taking over this project, read §0–§3 first, in order.** They say where the work
stands, which branches are in flight, what to do next, the owner's standing rules, how to run
agents in parallel, and how the servers and tools work. The capability inventory (done / partial
/ not done per requirement) is [docs/STATUS.md](docs/STATUS.md); the design of the code on
`main` is [docs/design/](docs/design/README.md).

---------------------------------------------------------------------------------------------------

## 0. Handover (state at 2026-10-02)

### 0.1 The goal

The owner's active goal, verbatim: «跑通solr这两个case的.smt。完成后。为了找到新bug。在hdfs和solr上都去做大规模的adhoc
check，并让我们的引擎给这样大规模的check提供更多的支持。worklaod都用已有的cluster based unit test»

1. **Phase 1:** a correct `.smt` (causal chain checked by hand against the system's code) for
   the nine HDFS cases and SOLR-18413 / SOLR-18406.
2. **Phase 2:** a finished large-scale ad-hoc sweep on HDFS and Solr with the systems' existing
   cluster tests as workloads, finding new bugs, on the two unified trees (§0.2), after the
   automation in §0.4 removed the hand-written pieces.

The owner wants outcomes, not intermediate report files. Requirements R1–R6:
`/bigtemp/vnr3ne/analysis/audit/COMMON.md`; `docs/STATUS.md` is organised by them.

### 0.2 Where things stand (2026-10-02)

- **Phase 1 is done**: all eleven cases PASS on main (the merge of the lock line `d65d31a31`), each `.smt`'s
  chain checked by hand — runs and mechanisms in `docs/STATUS.md` "Acceptance" (rounds `F1`, `F1b`, `N1`).
  VM `/bigtemp/vnr3ne/vm-w4h/j2sdk-image`. Most cases take 7–13 min, 11741 22 min, the Solr cases 19–28 min.
- **Trees**: `~/hadoop-hdfs-unified` (`gc/hdfs-unified`), `~/hadoop-hdfs-11741` (`gc/hdfs-11741`),
  `~/lucene-solr-unified` (`gc/solr-unified` `b41116b`: 18413's leader off the Overseer's node). Never edit or
  rebuild a tree a run reads; work on a new branch in a new worktree of it.
- **Phase 2** (large ad-hoc runs; finishing them is the goal, no new bug is an acceptable outcome — owner): 80
  checks ran (`a40s`, `a40h2`, `b20h`; triage with `tools/adhoc/triage.py <round>`), no confirmed witness.
  Picks: `/bigtemp/vnr3ne/analysis/adhoc-pick2-{hdfs,solr}.txt` (coverage-reached, a movable root in the static
  slice, coordination code). What stopped them is being fixed generally (§0.3).

### 0.3 Work in flight (branches, not on main)

| branch | content | state |
| --- | --- | --- |
| `schedule-stall-release` (+ tree `gc/solr-unified-sched`) | settle schedule slots a diverged replay proves will not come; a proxied Solr request is its own message | regressed 17967-pathA (CONFIRM) and 18413 in round `F2`; back to its author |
| `fix-unattested-hoff-arm` (+ tree `gc/hdfs-unified-dtx` in `/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx`) | DataTransfer ops are messages: op-header leaves pair with the sender's export; DataNode ops keep their tick identity; the DataTransfer doors | offline/hand-seed checked; needs a live round |
| (agent) random draws | record `ThreadLocalRandom`/`Random` draws and replay them (HDFS block placement made seed replays miss ad-hoc targets) | in progress, on top of `fix-unattested-hoff-arm` |
| `fix-replay-equivalent-context` | a root is admitted by its address alone (3 of 7 ad-hoc target misses fixed) | needs a live round |
| `worktree-agent-a49c8bf5715a00c40` | WIRE-CODEC W3/W6 + WP-D config roots (codec holes would also make 18413's handoff survive any re-parse) | deferred |

### 0.4 TODO, in order (one large change per live round; a change that regresses a passing case does not merge)

1. Random-draw replay → live round on the named cases + the HDFS picks; then `fix-unattested-hoff-arm` and
   `fix-replay-equivalent-context` the same way.
2. Fix `schedule-stall-release`'s regressions, then its live round, then the 20 Solr picks.
3. Run all 40 picks to a verdict each; triage, hand-check any CONFIRMED witness.
4. Then the deferred W6/WP-D line, one piece per round.

### 0.5 Designs and analyses (outside the repo, on `/bigtemp/vnr3ne`)

| path | what |
| --- | --- |
| `/bigtemp/vnr3ne/specs/WIRE-CODEC-proposal.md` | values cross processes at serialization boundaries as typed holes by key path; W0–W7; the "Designer decisions" blocks at the end are binding (1–14) |
| `/bigtemp/vnr3ne/specs/R1-ROOTS-proposal.md` | automatic roots: library door/config catalog, slice rules, config roots, relevance admission, root demand; binding decisions at the end |
| `/bigtemp/vnr3ne/specs/ADHOC-INFRA-proposal.md` | ad-hoc checks at scale: WP1 selection by slice, WP2 pre-screen, WP3 shared recording, WP4 line targets, WP5 operations |
| `/bigtemp/vnr3ne/specs/R3-REFCONT-proposal.md`, `R3-shapes.md` | shared state in one JVM: reference cells, containers, owner-indexed answers |
| `/bigtemp/vnr3ne/specs/C2.md`, `F14.md`, `DOCS.md` | the single binding rule JOIN→MINT→PIN; VM f14; docs policy |
| `/bigtemp/vnr3ne/analysis/audit/COMMON.md` | the owner's requirements R1–R6 (the yardstick) |
| `/bigtemp/vnr3ne/analysis/codemap-2026-09-30/` | code maps per package |

---------------------------------------------------------------------------------------------------

## 1. The owner's standing rules (long-term; they override defaults)

The owner is a PhD student doing academic research on open-source system stability. Reply to the
owner in **Chinese**. The design decisions are the lead's (the agent coordinating the work), made
after reading the code; implementers follow a written design.

**Engineering**
- **General fixes only.** No per-case code, no fixes derived from a case's expected verdict, no
  dead code, no fallback paths, no flags to keep an old path. Per-system code is allowed only as a
  small adapter or a declaration row, listed in STATUS "Per-system surface". Every stop/skip rule
  and every performance optimization is general.
- **Global view:** read all the code a concept touches (every stage) before changing it; fix the
  class of bug, not the instance. Docs may be stale — the code and the owner's current
  requirements are the reference.
- **Refactor bloat along the way** in the same commits as the goal work that touches it.
- **JVM-level relation preservation:** symbolic propagation is at the JVM level (shadows on slots,
  fields, objects), not KLEE's byte level. Every value moved outside interpreted bytecode is
  HOOKED, MODELED, or DETECTED-AND-PINNED by name — never lost silently. Shadows never belong to
  a JVM-shared identity (cached boxes, interned Strings, `Boolean.TRUE`).
- **No recorded-order pruning:** never drop candidate writers because they come after the read in
  the recording.
- **The question is one declared occurrence** `(r,c,i)` fixed at the seed; a campaign stops at its
  first witness when the case says so.
- **Lean tests:** table-driven, one test class per new class, delete tests of removed mechanisms.
- **Docs track the code:** docs describe HEAD only; update `docs/STATUS.md` and the design docs in
  the same commit as the change; delete what becomes outdated.
- **Time optimization never ends:** after every round, measure where each campaign's time went
  (`timeline.py`) and cut work that produced nothing, with a general rule, gated so verdicts do not
  move.

**Acceptance**
- **What a real PASS is:** the claim, polarityDecides, the mechanism's roots in
  `claim.movedRoots`, confirmed, cone gate — a PASS line or a finding kind alone is not acceptance.
- **Mechanism mandate:** 17899 bug1/2/3, 17897, 17967 A/B/C are MARKER_FLIPPED by an IPC door
  fault (either direction); 17960 by its config; 11741 by clocks (or a fault); the Solr cases by
  clocks (CLOCK_SKEW).
- **After every engine change, check the `.smt` causal chains** of the cases it can touch against
  the system code (e.g. 11741: `allKeys` ite/put/remove, keyId across the wire, the solver's
  choice).
- **Real false-positive examples only:** never construct false positives; FP-filter examples come
  from real runs.

**Git and safety**
- **Never push.** Never `git add -A`. Commit only when the change is built and tested.
- Before every commit: `mvn -q -o package` and `bash src/test/shell/run_engine_campaign_helpers_test.sh`
  (both via `onlift.sh`, §3).
- Commit messages end with `Co-Authored-By: <model> <noreply@anthropic.com>`. Commits in the
  Solr/HDFS trees use `git -c user.name="Zhenyu Li" -c user.email=zhl136@ucsd.edu`.
- Never edit the owner's dotfiles. Never rebuild a tree or edit a snapshot a campaign runs on.
  Never remove a `~/gc-run/p<N>` a running round uses: `tools/rounds/snapshot-gc.sh` removes one
  only when no lock and no process on any lift names it.
- Solr's test SecurityManager may be changed if it interferes (owner's permission); today it is
  off via `-Dtests.useSecurityManager=false`.

---------------------------------------------------------------------------------------------------

## 2. Working with agents in parallel (the owner's rules, long-term)

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
- About **6–7 agents at once**; no agent spawns sub-agents; ask for short reports (≤ 15–20 lines);
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
- **Merge gate:** the offline regression gate (`tools/regress/offline-ab.sh`, §3) for every change
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
- Keep a short state note current for yourself (the previous lead used
  `~/.claude/projects/-u-vnr3ne-GraphChecker/memory/acceptance-rounds-2026-09-30.md`), and keep
  README §0 current when you hand over.

---------------------------------------------------------------------------------------------------

## 3. Servers, storage, environment and tools

### 3.1 Hosts and storage

| what | where / how |
| --- | --- |
| hosts | `lift06`…`lift15` (ten), 48 cores and 30 GB each. All ten are used for every fan-out (obligations, rounds, sweeps, builds). `lift11` is the owner's interactive machine: it is a **worker but never a campaign head** (`launch-round.sh` enforces it). Never blow up a host's memory: every start goes through the host ledger (below). |
| home | `/u/vnr3ne` is NFS-shared by all lifts, **100 GB quota** (it has been full twice). Keep bulk data off it. |
| bulk storage | `/bigtemp/vnr3ne` (NFS pool, automounted on every lift, owner-approved): round outputs `gc-out/`, VM images `vm-*/`, specs, analyses, gate outputs `ab/`, helper scripts `bin/`, agent worktrees `wt/`. `test -w` does not trigger the automount; `ls` it first. |
| local scratch | `/localtmp/$USER` on each lift (replay working directories go to `/localtmp/$USER/graphchecker/`). |
| stock JDK 8 | `/usr/lib/jvm/java-8-openjdk-amd64`. **Trap:** the owner's dotfiles export `JAVA_HOME=java-11`, which lift11–15 lack, and `bash -c` under ssh re-reads `~/.bashrc`. Do not edit the dotfiles; use `onlift.sh`, which unsets `SSH_CLIENT` and sets Java 8. |
| z3 | `~/.local/bin/z3` (4.14.1) |
| concolic VM images | main's current VM: **`/bigtemp/vnr3ne/vm-w4e/j2sdk-image`** (f14 + R3 + r3-fix + WIRE-CODEC W1/W4 natives + the containers' iteration order). Others still kept: `vm-r3b` (before W4: main refuses it since W4's natives), `vm-r3c` (vm-r3b + the iteration order), `vm-w4d` (W4 without the iteration order). Pass an image as `CAUSYNTH_CUSTOM_JDK_HOME`, never as `JAVA_HOME`. A Java side that needs natives an image lacks refuses the replay by name (`ConcolicVmBroker#requireCurrentCapabilities`). |
| HDFS trees | `~/hadoop-hdfs-unified` (worktree of `~/hadoop`, branch `gc/hdfs-unified`, trunk 734dd8a67cd): ONE tree for the eight named cases (hdfs-17897, 17899-bug1/2/3, 17960, 17967-pathA/B/C) and the ad-hoc sweep -- one adapter, every workload, the known bugs' pre-fix code and target markers; its commit-by-commit inventory is `/bigtemp/vnr3ne/analysis/unify/hdfs-inventory.md`. hdfs-11741 keeps `~/hadoop-hdfs-11741` (`gc/hdfs-11741`); the older per-case trees `~/hadoop-hdfs-<case>` (`gc/<case>`) stay for the runs that used them |
| Solr trees | One Solr 8.11 tree, `~/lucene-solr-unified` (branch `gc/solr-unified`, a worktree of `~/lucene-solr-8_11`): the shared adapter, both cases' workloads and target markers, the two kept scaffold patches; solr-18406, solr-18413 and solr-adhoc all name it (inventory: `/bigtemp/vnr3ne/analysis/unify/solr-inventory.md`). The older per-case worktrees (`gc/solr`, `~/lucene-solr-18406`, `~/lucene-solr-18413`, `~/lucene-solr-8_11-adhoc`) serve only rounds started on them. Ant build; native Ant tests need `-Dtests.useSecurityManager=false`. `~/solr` is apache/solr main (blobless: never `git grep` a commit there). |
| owner's memory notes | `~/.claude/projects/-u-vnr3ne-GraphChecker/memory/` (one fact per file, index `MEMORY.md`) |

### 3.2 Helper commands (outside the repo)

```bash
/bigtemp/vnr3ne/bin/onlift.sh [-g <min-free-GB>] [-h <host>] <command...>
    # run a command in the current directory on the least-loaded lift (or <host>) with the Java 8 +
    # Maven toolchain; use it for mvn, the shell test, VM builds, offline stages, anything heavy.
    # `onlift.sh -h` with no host hangs; always give a host or omit -h.
/bigtemp/vnr3ne/bin/pick-lift.sh [min-free-GB]   # prints the best lift
```

### 3.3 Build, test, commit

```bash
cd ~/GraphChecker
/bigtemp/vnr3ne/bin/onlift.sh -g 10 bash -c 'mvn -q -o package && bash src/test/shell/run_engine_campaign_helpers_test.sh'
```

Keep `-o` (offline): `~/.m2` is shared over NFS. `mvn package` also builds the `hadoop-shim`
classifier jar from `src/shim/java`, which the HDFS trees call. A snapshot needs all three jars in
`target/` (`-jar-with-dependencies`, `-hadoop-shim`, plain).

VM: build with `third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_build_in_docker.sh`
(or the recipe under `/bigtemp/vnr3ne/vm-w1/work/`, see `docs/design/VM.md`), ~1 h for a full JDK,
via `onlift.sh -g 12`. Smoke tests: `scripts/causynth_smoke_test.sh` with `JDK_HOME` = the image.
Never overwrite an image a round uses; build a new directory.

### 3.4 Rounds (live campaigns)

```bash
git worktree add --detach ~/gc-run/p<N> <commit>
(cd ~/gc-run/p<N> && /bigtemp/vnr3ne/bin/onlift.sh -g 10 mvn -q -o package -DskipTests)
GC_OUT=/bigtemp/vnr3ne/gc-out CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-w4e/j2sdk-image \
  tools/rounds/launch-round.sh ~/gc-run/p<N> <round>              # all 11 cases, heads chosen by room
CASES="hdfs-17960 solr-18413" ... tools/rounds/launch-round.sh ... # a subset (or any case id)
DRY=1 ... tools/rounds/launch-round.sh ...                         # the heads it would choose
GC_OUT=/bigtemp/vnr3ne/gc-out tools/rounds/round-monitor.sh '<round>-*' | grep --line-buffered 'DONE '
GC_OUT=/bigtemp/vnr3ne/gc-out tools/rounds/stop-run.sh <round>-<case> ...
```

- Every tool takes `GC_OUT` from `tools/lib/gc-env.sh` (default `/bigtemp/vnr3ne/gc-out`).
- A launch must name its VM image (`CAUSYNTH_CUSTOM_JDK_HOME`; a sweep's `VM_IMAGE`): there is no
  default image.
- `launch-round.sh` chooses each case's head host at launch from the hosts' room in the ledger
  (`campaign_host_room`): the heaviest case first (its `engine_memory_mb`, `tools/lib/heads.sh`
  `case_engine_heap_mb`), each to the host with the most room among those heading the fewest
  cases, so no host heads two before every host heads one; `lift11` heads nothing. A head only drives its campaign: every
  engine JVM, the seed and CONFIRM replays and REPRODUCE's runs go wherever there is room, its own
  host first (PIPELINE §7.7).
- A round's cases explore uncapped (`stream_max_in_flight=0`): each keeps as many obligations in
  flight as the hosts admit, so one case alone may take the whole cluster. An ad-hoc sweep caps
  them so the cases it runs at once share it: `sweep.sh` gives every case
  `CAUSYNTH_STREAM_MAX_IN_FLIGHT` = the lifts' obligation slots for its `obligation_memory_mb`
  (`run_engine.sh` `campaign_pool_slots`: on each lift as many replays as fit under the 70 %
  ceiling at their charge, at most its cores; the ten lifts hold 30 of 6000 MB), and each capped
  exploration keeps its share in flight: those slots over the capped explorations running now
  (their entries in `$CAUSYNTH_HOST_LEDGER/explorations/`), at least one, read again at every start
  (`campaign_stream_has_slot`). Ten exploring cases keep 3 each; one left alone keeps all 30.
  A sweep's head is admitted (`fanout.sh` `NEED_MB`) for the room it reserves on its host, what
  its planner or composer starts at (`tools/lib/heads.sh` `case_head_reserve_mb`, 8 GB), not
  its engine heap: a40's Solr heads asked for 16 GB and waited while one case's 27-32 replays
  filled the lifts.
- A round name is written once (`accept-<round>-<case>` exists → refused). Names used so far:
  `v*`, `r1`–`r9`, `ra1`, `rb1`, `i1`–`i3`, `stream*`, `fast*`, `g1`, agents' `a37f*`, `ee*`, `agent-*`, `w4-*`.
- Typical wall time alone on the cluster: HDFS cases 15–45 min, solr-18406 ~25 min, solr-18413 ~50 min
  (its seed replay alone ~18 min).

### 3.5 The offline regression gate (merge gate)

```bash
AB_ACCEPT_ROOT=/bigtemp/vnr3ne/gc-out AB_OUT=/bigtemp/vnr3ne/ab/<name> [AB_STAGES="IMPORT EXPLORE.N COMPOSE"] \
  tools/regress/offline-ab.sh --round r8 --round r7 <baseline.jar> <candidate.jar> [case...]
```

Re-runs every stage that is a pure function of a recorded round (SEED.static, SEED.trace, PLAN,
EXPLORE.0, SOLVE.0, IMPORT, EXPLORE.N, COMPOSE, CONFIRM planning) with both jars and compares.
No replay: it cannot see VM, runtime or identity changes — those need a live round. Read the
header for `AB_HEAP_MB`, `AB_BASELINE_REPO` (when declarations differ between sides), `AB_HOSTS`.
Keep jars in `/bigtemp/vnr3ne/ab/jars/`.

### 3.6 Reading a campaign

`summary.tsv` (verdict row) → `logs/<case>.log` (`[campaign:error] stage=… reason=…`) →
`report/<case>/report.md` (blocking gaps, witness findings, causal cone) → `out/<case>/schedule/final/`
(`claim.json`, `candidate.smt2`, `candidate_composition_manifest.json`, `confirm.json`, `gaps.json`)
→ how EXPLORE ended `iteration-0000/exploration.json` → per planner round
`iteration-0000/obligations-<NNNN>/<id>/` (`obligation_query.smt2`, `obligation_result.jsonl`,
`replay.log`) → sessions `iteration-0000/sessions/<id>/`
(`targets.jsonl` has `reachedAnchor` and `observedFatal`). `experiments/accept/cone.py` and
`probe.sh` re-check a published formula. `tools/analysis/timeline.py` (on the early-exit branch)
breaks a campaign's time down by stage.

---------------------------------------------------------------------------------------------------

## The pipeline

One campaign per case, driven by `run_engine.sh`: one `campaign_<stage>` shell function per
stage, which calls Java mains in the jar.

```
SEED        static fatal slice + scope map (Soot), one recording on stock JDK 8
PLAN        the occurrences to replay, the declared target resolved, the roots to mint
INSTRUMENT  weave hooks into the scoped classes, verify the woven bytecode
REPLAY      seed replay on the concolic VM -> the seed session (one file per row kind)
IMPORT      row-contract gate over every session (contract/RowInvariants)
EXPLORE     one streaming pool: plan flip obligations in rounds (explore/ExploreMain), solve
            each, replay it focused on its world (runtime/FocusedReplay), land each session
            as it returns, grow the woven regions (GROW); end at the first witness COMPOSE
            accepts
COMPOSE     merge all sessions into one disjunction over the anchor, solve it per
            valuation with z3, decide the claim (compose/ComposeMain: Composer, ClaimPolicy)
SOLVE/DECIDE  check and print the solver verdict and the claim COMPOSE published
CONFIRM     re-run the witness world, check its edges (explore/ConfirmMain)
EMIT        final/result.json, gaps.json, run-manifest.json
REPRODUCE   after the verdict: run a confirmed witness natively, N runs at once over
            the lifts, the recording weave on the stock JDK planting only its fault
            markers, each ending at the fatal at its anchor (runtime/RecordingPlant)
```

The stages, their gates and the claim kinds are specified in
[docs/design/PIPELINE.md](docs/design/PIPELINE.md).

## Run one case

A case directory holds declarations only. `experiments/<system>/<case>/` contains:

- `case.sh`: the tree, the workload test, the target occurrence and the analysis scope;
- `workflow.properties`: budgets and inputs. `run_engine.sh` accepts only the keys it knows, so
  an unknown key is refused;
- `target.yaml`: `exception_target: <name> <binary class name> <source line> [<thrown type>]`.
  The engine finds the one `throw new` at that line of the class or of a class nested in it (a
  lambda body, an anonymous class) in the compiled classes; the tree is not rebuilt. The thrown
  type is needed only when the line holds two throws. A known bug's case keeps no `target.yaml`:
  its tree marks the bug's target throw with `@CausynthExceptionTarget("<case id>[,<case
  id>...]")` (the case id is `<case dir>-<case arg>`, e.g. `hdfs-17899-bug1`), and `run.sh`
  derives the spec from the marker (`tools/lib/annotated.py <system dir> <tree> <case id>`, into
  `$CAUSYNTH_OUTPUT_DIR/declared-target.yaml`). An ad-hoc sweep counts a confirmed finding at a
  marked throw as that known bug found again (`findings.py --annotated`, `nightly.sh`);
- optionally `communication-mappings.jsonl` (`WIRE_FLOW` rows; the fault doors are the engine's
  library catalog, `docs/design/SYMBOL-SCOPE.md` §4.2), `root-domains.jsonl` and
  `loop-bounds*.jsonl`.

Everything executable is in `experiments/lib/`; its README gives the workload rules. Per-system
parts are in `experiments/<system>/{system.sh,build.sh,classpath.py}`.

```bash
experiments/lib/run.sh experiments/hadoop/hdfs-17960 "" build      # build the tree, run the workload once
export CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-w4e/j2sdk-image
CASES=hdfs-17960 bash experiments/accept/accept.sh                  # campaign + probe + report
```

A case id names its experiment by its longest prefix, for example `hdfs-17899-bug1`,
`solr-18413`, `adhoc-<check>.<workload>` or `solr-adhoc-<check>.<workload>`.

`accept.sh` runs the campaign, a z3 probe and `report.py`. `experiments/accept/README.md` says
what PASS means. `report.py`'s table names the nine HDFS cases and the two Solr cases; a case it
does not name cannot pass. Before each case `accept.sh` waits for `MIN_FREE_GB` free where `OUT`
is written.

`tools/lib/gc-env.sh` states, once for every tool and for `run_engine.sh`, the output root
`GC_OUT` (default `/bigtemp/vnr3ne/gc-out`), the host ledger `CAUSYNTH_HOST_LEDGER` (default
`/bigtemp/vnr3ne/gc-out/hosts`, one for the cluster whatever `GC_OUT` a run writes) and the hosts
`LIFTS` (lift06–15).

Obligations of a campaign, and GROW's re-runs, fan out over the hosts in
`CAUSYNTH_CAMPAIGN_WORKER_HOSTS`, round-robin, as many on a host as its ledger admits, up to its
cores. A head's own steps go to its host when it has room, else to the pool's host with the most
room (`campaign_head_charged`, run there through `run_engine.sh --run-placed`). Every start on a
host is charged to the ledger first, at its measured need, for its ramp: an obligation or a re-run,
which is its replay (`obligation_memory_mb`, for 60 s), a host's solver of the exploration (its
heap, for 120 s; PIPELINE §7.5), a campaign head's engine JVM (its main's measured need, else
`engine_memory_mb`, for 120 s, and once more at `engine_memory_mb` if it runs out; PIPELINE §7.7),
its seed and CONFIRM replays (seven times the recording's measured peak when above
`obligation_memory_mb`, else that, for 300 s), REPRODUCE's runs (the recording's peak, for 60 s), and a `fanout.sh` job
(its `NEED_MB`, for 120 s). A start goes only when `MemAvailable` covers its need, every start
still in its ramp there and a reserve that keeps the host at most `CAUSYNTH_HOST_MAX_USED_PCT`
(70) percent full, and is released the moment it returns. A running workload JVM that outgrows its
charge is granted the excess, charged on the ledger, unless the host's real use (`MemTotal` less
`MemAvailable`) would pass that ceiling with it; only then is it ended (`campaign_watch_workload`,
`campaign_host_try_grow`): what the ledger promised other starts is no reason to end it. A head's "waiting for memory for a head step" line goes to stderr
(its stdout is often an artifact).

## Run an ad-hoc sweep

An ad-hoc check is a guarded `throw` that a system's existing cluster test reaches and passes.
A case is one check on one workload (`<check>.<workload>`), or a batch of checks on one workload
(`B<n>`, a row of `batches.tsv` with its target spec `targets/B<n>.yaml`, `batch.sh`). The
experiments are `experiments/hadoop/adhoc` and `experiments/solr/solr-adhoc`; each holds
`checks.tsv`, `batches.tsv`, `occurrences.tsv`, `targets/` and `tree` (the one tree it runs). A
check's slice starts from the classes its experiment's communication mappings name (`system.sh`'s
`system_mapping_scope`) and its own class, and grows the scope from there; the library doors'
classes join it once a class of that scope calls them. A sweep runs batches:
given `causynth_static_root` (`sweep.sh`'s `STATIC_ROOT`), a batch campaign takes each check's
slice from the build, records its workload once for all its checks, plans each check, replays
one seed per group of checks whose plans agree, and runs each check's campaign from EXPLORE on,
all at once, in `out/<case>/targets/<check>/` (PIPELINE §2b).

`tools/adhoc/nightly.sh <system>/<experiment> [date]` runs the whole chain below once per night
(one frozen, comparable sweep, never stopped for an engine fix) into
`$GC_OUT/nightly/<date>-<experiment>/`: it freezes the newest commit tagged `regress-pass-*` (an
annotated tag whose message holds a line `vm=<image>`, the VM the commit passed on; placed by
hand after an acceptance round: `git tag -a regress-pass-<date> -m vm=<image> <commit>`) as
`~/gc-run/n<date>-<experiment>`, locks it in `$GC_OUT/snapshots-in-use/`, writes `manifest.json`
(commit, jar, VM, tree, build key), runs steps 1–14 with the caches below, runs a case lost to the
infrastructure once more (DEAD, or STOPPED by a full disk or quota, ssh, or the case timeout),
and writes `triage.tsv`, `findings.tsv` and `report.md` (`funnel.py`: each step's count, and the
kept checks' outcomes beside the calibration tail's). `tools/rounds/snapshot-gc.sh <snapshot>...`
removes a snapshot only when no lock and no process on any lift names it (`tools/lib/alive.sh`).

The build key names what a static slice and a pre-screen recording depend on:
`tools/adhoc/buildkey.sh <experiment>` prints `<experiment>-<12 hex>`, a digest of the jar's
entries (stable across clean rebuilds of one commit), the tree's commit (a tree with uncommitted
tracked changes is refused) and the scope declarations (`system.sh`, `case.sh`,
`workflow.properties`, `communication-mappings.jsonl`, `loop-bounds.jsonl`). `slice.sh` and
`prescreen.sh` compute it: a new jar, tree or scope is a new key, under which every check is
sliced again, and the same build finds its slices and recordings again.

The steps, in order (`tools/adhoc/`; each script's header documents its arguments). Steps 1–4
are per tree (`nightly.sh` keeps them in `$GC_OUT/coverage/<experiment>-<tree commit>/`):

1. `workloads.py <system-dir> <repo>`: the system's cluster tests (`workloads.tsv`): every
   JUnit 4 or Jupiter `@Test` method, declared or inherited, that the engine's runner can call,
   of a test class that names the system's cluster class (`system_cluster_class`). HDFS: 4176
   tests; Solr: 606.
2. `sites.py <system-dir> <repo>`: every guarded `throw new` in the system's sources.
3. `coverage.sh`, fanned out by `fanout.sh`: one JaCoCo run per workload test, which writes
   `<w>.lines` and a `.node` marker and exits with the test's own status.
4. `reach.py <sites.jsonl> <coverage-dir>`: checks whose guard ran and whose throw did not.
5. `select.py <sweep-dir> <experiment> declare [tree]`: declare every reached check a sweep can
   run in `checks.tsv` (a new one as `<Class>-<throw line>`) and print one
   `<check>.<workload>` per check, its fastest usable workload.
6. `targets.py <experiment> <tree>`: write `targets/<check>.yaml`, each check's class and throw
   line. Nothing in the tree is edited or rebuilt.
7. `slice.sh <experiment> <cases-file>`: the engine's own static slice of each check
   (`run.sh … slice`, ~70–100 s, 3.2 GB) and its score (`score.py`), in
   `$GC_OUT/static/<key>/<check>/` (`key.json` there says what the key digests), fanned out over
   the lifts; a check the key has a score for is kept. A check is kept when a root (clock, fault
   door, READ placeholder, field another region stores, wire crossing) lies within 4 edges of its
   fatal operands.
8. `select.py <sweep-dir> <experiment> rank $GC_OUT/static/<key> <cases-file>`: `selected.jsonl`
   (kept checks, best score first, at most three per class, plus the calibration tail: every
   twentieth dropped check, 5 %, the same ones every night, which measures what the selection
   drops).
9. `cover.py <sweep-dir> <experiment> jobs [16] [2]`: `prescreen-jobs.tsv`, a greedy cover of the
   selected checks by the tests that reach them, at most 16 checks per recording, each recording
   named by its workload and a digest of its checks.
10. `prescreen.sh <experiment> <sweep-dir>/prescreen-jobs.tsv`: one recording per batch woven
    for every check of it (`$GC_OUT/prescreen/<key>/<batch>/runtime/record-summary.json`: each
    check's ACTIVATED or refusal; a batch the build recorded already is kept). Pairs not in the
    recording window are dropped here instead of dying at SEED (WP2 measured ~35 %, while a check
    whose region folds into another check's was still lost as `NOT_IN_WINDOW`; each check is
    now aggregated on its view of the merged skeletons).
11. `cover.py <sweep-dir> <experiment> cases $GC_OUT/prescreen/<key>`: `cases.txt`, one batch
    case per workload with the checks it activated (at most four).
12. `VM_IMAGE=<image> STATIC_ROOT=$GC_OUT/static/<key> sweep.sh <snapshot> <round>
    <sweep-dir>/cases.txt [heads-per-host]`: one campaign per batch over all ten lifts, `PRUNE=1`, 5400 s per case;
    restartable. The cases exploring at once share the lifts' obligation slots
    (`stream_max_in_flight`, §3.4). A batch records once, plans each check, and seed-replays each group of checks
    whose plans agree once (`out/<batch>/schedule/groups/`); each check explores on its own.
13. `triage.py <round> [gc-out]`: outcome class per case, and per check of a batch case
    (`<case>/<check>`): CONFIRMED, REFUTED, NO_ROOT, NO_WITNESS, STOPPED, DEAD, RUNNING,
    PENDING; `gc-out` defaults to `gc-env.sh`'s `GC_OUT`.
14. `findings.py <sweep-dir> [--ledger $GC_OUT/findings/ledger.jsonl] [--static $GC_OUT/static/<key>]`:
    one row per mechanism among the confirmed witnesses (`findings.tsv`), weighted by kind,
    mediation and (1 + the rate at which REPRODUCE reproduced it natively at its anchor); the
    ledger marks each new, known or dismissed.

## Outputs

`accept.sh` and the round and sweep tools write `$GC_OUT/accept-<suffix>/`:

| path | holds |
| --- | --- |
| `summary.tsv`, `logs/<case>.log`, `report/<case>/{report.md,row.tsv,status}` | the verdict row, the campaign log, the readable report |
| `out/<case>/` | SEED's static artifacts: `static_scope_map.jsonl`, `scope_frontier.jsonl`, `region_skeletons.jsonl.gz`, `candidate_dataflow_edges.jsonl.gz`, and the recording under `runtime/` |
| `out/<case>/schedule/stage_metrics.tsv` | time per stage |
| `out/<case>/schedule/iteration-0000/` | `execution_task_plan.jsonl`, `concolic_region_plan.jsonl`, `recorded_schedule.jsonl`, `sessions/<id>/`, `obligations-<NNNN>/` (per planner round: one worker directory per obligation), `obligation_results.jsonl`, `exploration.json`, `witness-attempts/` |
| `…/sessions/<id>/` | one replay's rows: `activations`, `decisions`, `reads`, `writes`, `exports`, `attaches`, `roots`, `targets`, `gaps`, `schedule` (`.jsonl`), `expressions.jsonl`, `manifest.json` |
| `out/<case>/schedule/final/` | `result.json`, `claim.json`, `gaps.json`, `candidate.smt2`, `candidate_composition_manifest.json`, `confirm.json`, `reproduce.json`, `run-manifest.json` |
| `out/<batch>/targets/<check>/` | a batch case's check: its frozen slice, its region plan (`runtime/`), `campaign.log`, and its campaign root `schedule/` laid out as above; the batch's one recording and `runtime/record-summary.json` are in `out/<batch>/` |

A flip query can be re-solved by hand with `z3 -smt2 obligation_query.smt2`.

## Repository map

```
run_engine.sh                     the campaign driver (every stage)
src/main/java/edu/uva/liftlab/graphchecker/
  causynth/    Soot pass: fatal slice, root catalog, door weave, weaving and its verification,
               region finalization, wire-flow catalog, declared-target line resolver
  plan/        static scope map, scope growth, task plan, declared sites, lineage scan,
               work-start and timed-wait shapes
  runtime/     recording and replay hooks, identity and attribution, schedule (ScheduleLog),
               mints, message and store doors (MessageDoors), focused replay, confirmation,
               VM broker
  explore/     corpus, closure, branches, frontier, flip queries, obligations, wave graph, ExploreMain,
               ConfirmMain
  compose/     Composer, families, SMT lowering, container codec, string identities, ClaimPolicy,
               ComposeMain
  contract/    row kinds, holes, wire declarations, identity types, gap registry, session layout,
               IMPORT gate, row pool
  smt/         expression IR, arms and families, z3 driver
  annotation/  Debug.makeSymbolicBoolean; @CausynthExceptionTarget (the trees' compile ABI only)
src/shim/java/                    the Hadoop shim (org.apache.hadoop.ipc.*) the HDFS trees call
src/test/                         unit tests; shell/run_engine_campaign_helpers_test.sh
third_party/OpenJDK-Concolic-Execution-Engine/   the concolic VM (hotspot/src/share/vm/concolic,
                                  interpreter/bytecodeInterpreter.cpp) and its smoke tests
experiments/lib/                  the one harness every case runs through
experiments/accept/               accept.sh, report.py, cone.py, probe.sh
experiments/hadoop/, experiments/solr/   per-system scripts, cases, ad-hoc experiments
tools/lib/                        gc-env.sh (GC_OUT, host ledger, LIFTS for every tool), alive.sh
                                  (which runs a process on any lift still names), heads.sh (a
                                  case's configuration, its head's weight and
                                  room, and which host heads it)
tools/rounds/                     launch, monitor and stop campaigns on the lifts; snapshot-gc.sh
tools/adhoc/                      ad-hoc check discovery, build key, slicing, selection, pre-screen,
                                  sweeps, the nightly, triage, findings
tools/regress/                    offline-ab.sh: the offline merge gate
tools/analysis/                   occurrences.py (a selector from a discovery log), timeline.py (where a
                                  campaign's wall time went), rootcov.py (roots and symbolic
                                  predicates per campaign)
docs/STATUS.md                    done / partial / not done, per requirement; open defects
docs/design/                      the design of main (index: docs/design/README.md)
```

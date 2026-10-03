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

## 0. Handover (state at 2026-10-02 evening; every agent stopped, nothing running)

### 0.1 The goal

The owner's active goal, verbatim: «跑通solr这两个case的.smt。完成后。为了找到新bug。在hdfs和solr上都去做大规模的adhoc
check，并让我们的引擎给这样大规模的check提供更多的支持。worklaod都用已有的cluster based unit test»

1. **Phase 1 (done):** a correct `.smt` (causal chain checked by hand against the system's code) for the nine
   HDFS cases and SOLR-18413 / SOLR-18406.
2. **Phase 2 (in progress):** ad-hoc checks on HDFS and Solr with the systems' own cluster tests as workloads, to
   find new bugs. The owner narrowed it to **20 hand-picked, bug-prone coordination checks per system** (not a
   1000-check sweep) and accepts **finishing with no new bug**: the deliverable is every pick run to a real
   verdict, each run taking tens of minutes, with the engine fixed generally wherever a pick is blocked.

The owner wants outcomes (correct `.smt`, finished checks), not intermediate report files. The requirements
R1–R6 are in `/bigtemp/vnr3ne/analysis/audit/COMMON.md`; `docs/STATUS.md` is organised by them and lists the
open defects.

### 0.2 Where things stand

- **main** = `2e387a7c0` (local; `origin/main` = `4027318f5`, push only when the owner asks). It holds the
  Phase 1 release plus `perf-slow-replays` and `fix-confirm-flakiness`, merged after round **`V8`** passed all
  eleven cases (snapshot `~/gc-run/p221`, tree = main's). Times: HDFS cases 5–11 min, 11741 27 min, solr-18406
  15 min, solr-18413 23 min. Mechanisms and moved roots: `docs/STATUS.md` "Acceptance" (unchanged since F1).
- **VM** `/bigtemp/vnr3ne/vm-w4h/j2sdk-image` for everything. Parked images: `vm-w4i` (`perf-vm-readout`),
  `vm-nr41` (`vm-ref-compare`); neither is reviewed, neither is used.
- **Trees** (never rebuild one a run or another agent reads; work on a new branch in a new worktree):
  - HDFS: `~/hadoop-hdfs-unified` (`gc/hdfs-unified`, pushed to the owner's fork `JHSUYU/hadoop`) for the eight
    HDFS cases and the HDFS checks; `~/hadoop-hdfs-11741` (`gc/hdfs-11741`, pushed) for 11741.
  - HDFS + DataTransfer adapter: `gc/hdfs-unified-dtx` `51f1e058380` in `/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx`
    (built with a private Maven repo `/bigtemp/vnr3ne/wt/dtx/m2`). Needed by `dtx-on-main` and every branch
    built on it. Not pushed.
  - Solr: the case files on main name `gc/solr-unified-storing` `663e0ef` in
    `/bigtemp/vnr3ne/wt/lucene-solr-storing` (`gc/solr-unified` `b41116b` + SolrZkClient's write brackets that
    `MessageDoors#storing` needs). Each Solr workload must have been built in that tree (`run.sh <case> ""
    build`), or `validate` fails at elapsed 0 ("missing test report"). solr-18406 and solr-18413 are built there.
    `~/lucene-solr-unified` (`b41116b`) is the older tree. The Solr trees' only remote is apache/lucene-solr:
    never push them.
- **Phase 2:** 80 checks ran before today's fixes (`a40s`, `a40h2`, `b20h`; `tools/adhoc/triage.py <round>`), no
  confirmed witness. Every blocker is classified in §0.5; most have a branch in §0.3.
- **Owner decisions of 2026-10-02** (also in §1):
  - The closure keeps every static writer of a demanded location. Over budget: recorded writers first, the
    rest cut by a named `PLAN_CLOSURE_CUT`.
  - The recording window is NOT opened before cluster start, for now. The DataNode registration order before
    the window stays a named divergence; the prototype is `/bigtemp/vnr3ne/wt/rdraw/startup-order-prototype.patch`.
  - COMPOSE/EXPLORE may over-approximate (CONFIRM filters false SATs); CONFIRM must stay strict; completeness
    outranks precision.
  - Pre-screening the picks (`prescreen.sh`, to drop picks whose target runs only before the window) was offered
    and not decided: keep the owner's picks unless the owner says otherwise.

### 0.3 Branches not on main (exact heads; all work is committed unless marked WIP)

| branch | head | base | content | state / next step |
| --- | --- | --- | --- | --- |
| `fix-adhoc-crashes` | `721b88f31` | old main | PLAN's demand walk crosses only edges of methods that ran in the occurrence, a store's holders, an atomic by its receiver (a40s-2 6076 → 786 occurrences, 18413 123 → 19); COMPOSE: PATH_SELF_CONTRADICTORY only when a path is unsat without its fatal arm; `String.trim` lowered | offline gate identical on the 11 `.smt`. **Next round**: snapshot `~/gc-run/p222` = main `2e387a7c0` + it, merged, NOT built yet |
| `dtx-on-main` | `e3b2efb1f` | `bc3670ac9` | DataTransfer ops are messages (op headers pair with the sender's export, a DataNode turn takes its op into its own context, `MessageDoors#received`); DataTransfer fault doors in both directions | rounds `V5`/`V6`/`V7`: ten cases PASS (HDFS cases pointed at the dtx tree); 11741 fails on the balancer race (`fix-11741-pairing`); merge together with it |
| `fix-11741-pairing` | `9fd01c95f` + **WIP** | the `V7` stack (`89dc29d50` = old main + dtx + perf + flakiness) | 11741's balancer may run the second move to dn1 one dispatcher iteration later (`Dispatcher.Source#dispatchBlocks`, ~1.1 s per turn, `maxNoMoveInterval` on its own clock); then a later handshake answers the declared occurrence by its question with another producer. Fixes: a slot stands on its session (GROW's swap withdraws its slots); an occurrence answered by its question opens its own slots; CONFIRM accepts the anchor's delivery from a producer of the same question | live `R5x5` PASS on the slow order. **Review blocked it**: #1 CONFIRM's substitution compares no value and no attempt/site index (must compare both, file a DIAGNOSTIC gap per substitution, only where the arm's session has ADDRESS_UNSTABLE); #2 an answered slot registered first makes the recorded-chain session BLOCKING (landing-order dependent: persist an `answered` bit or recompute it). #3 (weaker divergence detection) is optional under the over-approximation principle. The rework is half done: uncommitted in `.claude/worktrees/agent-a9f2c23f39c51f005`, saved as `/bigtemp/vnr3ne/handover/fix-11741-pairing-review-rework-wip.patch` |
| `fix-no-root` | `2e931192e` + **WIP** | the `V7` stack | NO_ROOT fixes: a disjunctive anchor decides at its last test; the slice follows an inherited method; reads of a container held in a final field (and through an accessor) are observed; a final container mutated outside a constructor is a CONTAINER cell; D0 per test; **Writers_W(ℓ)'s writer at version 0** (a location's INITIAL is a write row a read may be re-paired to; CONFIRM orders every writer after the read when INITIAL is chosen) | offline gate identical except 11741 COMPOSE (formula grows, claim same, 95 → 110 s) and 18413 CONFIRM (8 STATE edges from old rows). Needs a live round. **WIP**: happens-before edges for objects published through queues/executors/arrays (so version-0 arms stop proposing orders only CONFIRM refutes, e.g. a40h2-1's `BlockInfo.uc`), uncommitted in `.claude/worktrees/agent-a5fe89974b9d226ac`, saved as `/bigtemp/vnr3ne/handover/fix-no-root-hb-edges-wip.patch` |
| `fix-hdfs-seed-stalls` | `bfd7492bd` | the `V7` stack | one rule set for seed-replay stalls (a waiter passes what its own flow skipped; a cause settled on evidence gives up what only it would make; held waits let go 2 s into an idle stall; no planned guard), and a replay's DataNode turn is numbered by the DataTransfer op it took in. Supersedes `schedule-stall-release` and `schedule-stall-planned` (squashed in) | b20h-0 seed: ~137 stalls/2400+ s → 23–24 stalls/~560 s; 17897, 17899-bug3, 17967-pathA PASS on it. Solr stalls (late HTTP between concurrent Overseer tasks) not helped. Needs a live round |
| `replay-random-draws` | `d656860b2` | `dtx-on-main` | every `Random`/`ThreadLocalRandom`/`Collections.shuffle`/`Math.random`/`UUID` draw recorded and replayed by key; every class that draws is woven for draws, the workload's own test classes included | ready; needs a live round. DataNode registration order is the remaining divergence (owner: not now) |
| `fix-replay-equivalent-context` | `71fedd858` | `bc3670ac9` + `2758f815d` + the three pairing commits cherry-picked | a root is admitted by its address alone (a test thread's direct call into a NameNode/DataNode object no longer refused): b20h's FSEditLogLoader-1147/-1182 and BlockPoolTokenSecretManager-56 reach their targets | round `V4` regressed 11741 (the same pairing race). Rebase onto main after `fix-11741-pairing` lands; verify 11741 (twice) + the three checks + V4h-2 |
| `perf-expr-store` | `dd89bc65b` | `perf-slow-replays` (on main) | no whole-run map keeps a replay expression node alive (weak expansions and hashes) | committed but NOT verified (agent stopped mid-work). Verify: a40s-3/a40s-5 seed heap and time, hdfs-17897 and solr-18406 seed rows unchanged |
| `perf-vm-readout`, `vm-ref-compare` | `3cbea0bee`, `bba1ee25d` | — | VM changes: per-activation tracked-location read-out (image `vm-w4i`, fixed only a40s-3; risk: rows lost when the writing activation publishes nothing); a reference compared with an untracked object states identity (image `vm-nr41`, defect 41) | PARKED by the lead: small payoff now, each needs a VM review |
| `worktree-agent-a49c8bf5715a00c40` | `90ca7724e` | old | WIRE-CODEC W3/W6 + WP-D config roots | deferred |
| `schedule-stall-release`, `schedule-stall-planned`, `fix-unattested-hoff-arm`, `fix-hdfs-seed-stalls-pre-p219` | — | — | superseded (folded into `fix-hdfs-seed-stalls` / `dtx-on-main`) | delete when convenient |

### 0.4 TODO, in order

One large change per live round of the eleven cases; a change that turns a passing case into a failure does not
merge until fixed (§1). Snapshot recipe and round commands: §3.4 and §3.7.

1. **Round `V9`** on `~/gc-run/p222` (main + `fix-adhoc-crashes`): build it, run the 11 cases, hand-check the
   `.smt` chains, merge.
2. **Finish `fix-11741-pairing`**: apply the WIP patch, finish review #1 and #2, re-run its offline check on
   `V7`'s corpus (`/bigtemp/vnr3ne/gc-out/accept-V7-11741`) and the gate, then ONE live round of the eleven on
   main + `dtx-on-main` + `fix-11741-pairing` (HDFS cases on the dtx tree, §3.7); 11741 twice, since the race is
   order-dependent. Merge both. Then move the HDFS tree: fast-forward `gc/hdfs-unified` to `gc/hdfs-unified-dtx`
   and rebuild `~/hadoop-hdfs-unified` when nothing reads it, so the case files need no edits (and give 11741's
   tree the same two dtx adapter commits on a new branch, measured first).
3. Then, one round each and in this order: `fix-hdfs-seed-stalls`, `fix-no-root` (+ its WIP), `replay-random-draws`,
   `fix-replay-equivalent-context` (rebased), `perf-expr-store` (after its own verification).
4. **Run the 40 picks to a verdict each** from a snapshot of the resulting main: HDFS
   `/bigtemp/vnr3ne/analysis/adhoc-pick2-hdfs-cases.txt` (20), Solr the first 20 non-comment lines of
   `/bigtemp/vnr3ne/analysis/adhoc-pick2-solr.txt` (never run yet; build each Solr workload in the storing tree
   first). Commands: "Run an ad-hoc sweep" below and `tools/adhoc/sweep.sh`. At most ~6–8 heads at once. Triage
   with `tools/adhoc/triage.py`; hand-check any CONFIRMED witness against the code; a REFUTED claim is a real
   false-positive example (keep it).
5. Fix what the 40 still hit (§0.5), generally, one change per round. Then the deferred WIRE-CODEC W3/W6 and
   WP-D config line, one piece per round.

### 0.5 Open problems (what still blocks checks, by class)

| class | where it shows | state |
| --- | --- | --- |
| Seed replays that stall on their own recording (a clock decides heartbeat vs block report, held waits the recording never made, DataNode turns numbered by arrival) | b20h-0/-1/-2, a40h2-5/-17 | `fix-hdfs-seed-stalls` (HDFS); Solr's late HTTP between concurrent Overseer tasks and replication polls has no rule yet |
| Explore volume | b20h-0 ran 1112 obligations and hit 5400 s | partly `fix-adhoc-crashes`; measure after it |
| Replay heap | a40s-3/a40s-5 seed; a40s-17 obligations peak 10–20 GB | `perf-expr-store` (Java); a40s-17 needs a heap dump; the VM read-out is parked |
| NO_ROOT: value crosses a stream/message with no door | b20h-9/-17/-18, a40h2-14, a40s-18, a40s-19 (state JSON from ZooKeeper) | open (WIRE-CODEC line; DataTransfer done in `dtx-on-main`) |
| NO_ROOT: value crosses processes through a file | a40h2-13, V4h-0 (FSEditLogLoader: edit-log ops rebuilt from the shared edits dir) | open; needs file I/O as a source of symbolic values |
| NO_ROOT: config through a two-level boolean helper | a40h2-9 | open (WP-D) |
| NO_ROOT: enum constant compared by reference | a40h2-19 | `vm-ref-compare`, parked |
| Seed replay misses the declared target | a40h2-3/-6, a40s-11/-16; V4h-2 and a40h2-19 on the `V7` stack | `replay-random-draws`, `fix-replay-equivalent-context`; DataNode registration order before the window (owner: not now) |
| UNPRODUCIBLE_ANSWER (an IPC answer rests on a value the recording does not state) | FsDatasetImpl-1843 on `dtx-on-main` (V5h-3) | open, not yet traced |
| Version-0 arms propose orders only CONFIRM can refute | a40h2-1 | WIP in `fix-no-root` (happens-before through queues/arrays) |
| WIRE_FLOW staged leaves can ride a message that passed no door | none observed as a cause yet (11741 was the balancer race) | design change: bind leaves to their message object as codec holes are (WIRE-CODEC) |
| Correct verdicts, not defects | a40s-9 (NO_ROOT: nothing movable reaches the anchor); b20h-5, a40s-14 (no witness, formerly mislabeled); b20h-3 (target runs only before the window) | none (a40h2-1 was NO_ROOT on main; with `fix-no-root`'s version-0 writer it composes a candidate CONFIRM must judge) |

### 0.6 Designs and analyses (outside the repo, on `/bigtemp/vnr3ne`)

| path | what |
| --- | --- |
| `/bigtemp/vnr3ne/specs/WIRE-CODEC-proposal.md` | values cross processes at serialization boundaries as typed holes by key path; W0–W7; the "Designer decisions" blocks at the end are binding (1–14) |
| `/bigtemp/vnr3ne/specs/R1-ROOTS-proposal.md` | automatic roots: library door/config catalog, slice rules, config roots, relevance admission, root demand; binding decisions at the end |
| `/bigtemp/vnr3ne/specs/ADHOC-INFRA-proposal.md` | ad-hoc checks at scale: WP1 selection by slice, WP2 pre-screen, WP3 shared recording, WP4 line targets, WP5 operations |
| `/bigtemp/vnr3ne/specs/R3-REFCONT-proposal.md`, `R3-shapes.md` | shared state in one JVM: reference cells, containers, owner-indexed answers |
| `/bigtemp/vnr3ne/specs/C2.md`, `F14.md`, `DOCS.md` | the single binding rule JOIN→MINT→PIN; VM f14; docs policy |
| `/bigtemp/vnr3ne/analysis/audit/COMMON.md` | the owner's requirements R1–R6 (the yardstick) |
| `/bigtemp/vnr3ne/analysis/codemap-2026-09-30/` | code maps per package |
| `/bigtemp/vnr3ne/analysis/adhoc-picks-{hdfs,solr}-2026-10-01.md`, `adhoc-pick2-*.txt` | how the picks were chosen, and the pick lists |
| `/bigtemp/vnr3ne/handover/` | the two WIP patches of §0.3 |

---------------------------------------------------------------------------------------------------

## 1. The owner's standing rules (long-term; they override defaults)

The owner is a PhD student doing academic research on open-source system stability. Reply to the
owner in **Chinese**, answer a direct question first (before continuing the work), keep answers
short. The design decisions are the lead's (the agent coordinating the work), made after reading
the code; implementers follow a written design. Decisions that change what the owner asked for
(the pick lists, the recording window, what counts as a root) go to the owner with a
recommendation.

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
  move. A check should take tens of minutes; an occasional run past an hour is fine, but runs of
  hours usually mean a defect (a stall, a starved step, an exploding closure): find it.
- **The closure revolves around the declared target region `(r,c)`** (the seed graph too): prune
  branches that lost it; for HDFS only the target DataNode matters. Never encode a case's chain.
- **The closure keeps every static writer** of a demanded location; never drop writers the
  recording did not exercise (an untaken branch's write is what a flip enables). Over budget:
  recorded writers first, the rest cut by a named `PLAN_CLOSURE_CUT`.
- **Over-approximate, confirm strictly:** COMPOSE/EXPLORE may produce false SATs (CONFIRM refutes
  them, the model is excluded, the next claim follows); composer imprecision is a performance item,
  never a blocker. CONFIRM is the last filter and must stay strict (never loosen what it compares
  without an equal check; every substitution named). Completeness outranks precision: a guard
  that can make a real witness UNSAT is worse than a false positive.
- **Roots from general rules only;** a small per-system adapter is allowed and listed in STATUS
  "Per-system surface"; never a root chosen per case or by the expected mechanism.
- **Delete what automation replaces:** every automating merge deletes the old code, manual tools,
  hand rows and scripts it replaced.
- **Lock, then one change at a time:** keep the last all-passing main; integrate one large change
  per live round; stacking several big changes is what made rounds regress repeatedly
  (2026-10-01).

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
- **Push only when the owner asks** (each request covers that moment, not later commits). Never
  `git add -A`. Commit only when the change is built and tested.
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
  `~/.claude/projects/-u-vnr3ne-GraphChecker/memory/phase2-status-2026-10-02.md`), and keep
  README §0 current when you hand over.

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
  script`), never on your own command line (§3.8), and remove ledger entries whose pid is gone
  (`$CAUSYNTH_HOST_LEDGER/explorations/`).

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
| concolic VM images | main's current VM: **`/bigtemp/vnr3ne/vm-w4h/j2sdk-image`** (vm-w4e + the `frame::metadata_do` fix for interpreted frames + caches cleared when metadata is freed + demand-driven tracking). Parked, unreviewed: `vm-w4i` (per-activation tracked-location read-out, branch `perf-vm-readout`; a jar from that branch refuses vm-w4h by name), `vm-nr41` (reference-compare identity, branch `vm-ref-compare`). Older images (`vm-w4e`, `vm-w4d`, `vm-r3b`, `vm-r3c`) serve only old rounds. Pass an image as `CAUSYNTH_CUSTOM_JDK_HOME` (a sweep: `VM_IMAGE`), never as `JAVA_HOME`. A Java side that needs natives an image lacks refuses the replay by name (`ConcolicVmBroker#requireCurrentCapabilities`). |
| HDFS trees | `~/hadoop-hdfs-unified` (worktree of `~/hadoop`, branch `gc/hdfs-unified`, trunk 734dd8a67cd): ONE tree for the eight named cases (hdfs-17897, 17899-bug1/2/3, 17960, 17967-pathA/B/C) and the ad-hoc sweep -- one adapter, every workload, the known bugs' pre-fix code and target markers; its commit-by-commit inventory is `/bigtemp/vnr3ne/analysis/unify/hdfs-inventory.md`. hdfs-11741 keeps `~/hadoop-hdfs-11741` (`gc/hdfs-11741`); the older per-case trees `~/hadoop-hdfs-<case>` (`gc/<case>`) stay for the runs that used them |
| Solr trees | One Solr 8.11 tree line, `~/lucene-solr-unified` (branch `gc/solr-unified`, a worktree of `~/lucene-solr-8_11`): the shared adapter, both cases' workloads and target markers, the two kept scaffold patches (inventory: `/bigtemp/vnr3ne/analysis/unify/solr-inventory.md`); solr-18406, solr-18413 and solr-adhoc name its successor `gc/solr-unified-storing` (`/bigtemp/vnr3ne/wt/lucene-solr-storing`: the same plus SolrZkClient's `MessageDoors#storing` write brackets). The older per-case worktrees (`gc/solr`, `~/lucene-solr-18406`, `~/lucene-solr-18413`, `~/lucene-solr-8_11-adhoc`) serve only rounds started on them. Ant build; native Ant tests need `-Dtests.useSecurityManager=false`. `~/solr` is apache/solr main (blobless: never `git grep` a commit there). |
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
GC_OUT=/bigtemp/vnr3ne/gc-out CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-w4h/j2sdk-image \
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
  `v*`, `r1`–`r9`, `ra1`, `rb1`, `i1`–`i3`, `stream*`, `fast*`, `g1`, `F1`, `F1b`, `F2`, `K*`, `L*`, `N1`,
  `V1`–`V8`, `V4h`, `V5h`, `V7b`, `M1`, `CF1`, `STO1`, agents' `a37f*`, `ee*`, `agent-*`, `w4-*`, `R5x*`,
  `r6s*`, `R7*`, `nr*`. Use a fresh name (e.g. `V9`, `V10`, …).
- Typical wall time on main (round `V8`, cluster shared with a few agent runs): HDFS cases 5–11 min,
  11741 ~27 min, solr-18406 ~15 min, solr-18413 ~23 min. After the campaign, the acceptance report's
  `probe.sh` (z3 per alternative path, 600 s each) can add up to 30 min before the summary row is
  written; it is reported, not a gate.
- **How the last lead used the servers:** one round at a time, at most ~6–8 cases at once (batch 1
  = six cases, then the rest as cases finish); ad-hoc sweeps with 1 head per host
  (`sweep.sh … 1`); agents' verification runs in their own `GC_OUT`; every start through the ledger
  (≤ 70 % memory per lift); `lift11` (the owner's machine, where the lead session runs) works but
  never heads; builds with `onlift.sh -g 10`.

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
`probe.sh` re-check a published formula. `tools/analysis/timeline.py`
breaks a campaign's time down by stage.


### 3.7 A snapshot for a branch that needs another tree

There is no override for a case's tree: each `experiments/<system>/<case>/case.sh` names its `repo=` (and
`experiments/hadoop/adhoc/tree` the ad-hoc HDFS tree). To validate a branch that needs a different tree
(today: `dtx-on-main` and everything on it needs `/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx`), edit those lines in the
**snapshot only**, uncommitted, never on main:

```bash
git worktree add -q --detach ~/gc-run/p<N> <main>
cd ~/gc-run/p<N> && git merge --no-ff -q <branch> -m "Validation merge: <branch>"     # resolve docs conflicts by keeping both sides
sed -i 's#repo=/u/vnr3ne/hadoop-hdfs-unified$#repo=/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx#' \
  experiments/hadoop/hdfs-17967/case.sh experiments/hadoop/hdfs-17899/case.sh \
  experiments/hadoop/hdfs-17960/case.sh experiments/hadoop/hdfs-17897/case.sh
sed -i 's#^/u/vnr3ne/hadoop-hdfs-unified$#/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx#' experiments/hadoop/adhoc/tree
/bigtemp/vnr3ne/bin/onlift.sh -g 10 bash -c 'cd ~/gc-run/p<N> && mvn -q -o package && bash src/test/shell/run_engine_campaign_helpers_test.sh'
```

The `case.sh` files of 17899 and 17967 hold indented `repo=` lines (one per sub-case), hence no `^` there.
11741 keeps `~/hadoop-hdfs-11741`. A tree built for one branch must not be installed into the shared
`~/.m2` (use `MAVEN_REPO_LOCAL`, `experiments/hadoop/build.sh`), or it changes the jars every other tree's
build resolves. A Solr workload must be built in the Solr tree the case names before its first run:
`SKIP_GRAPHCHECKER_INSTALL=1 bash experiments/lib/run.sh experiments/solr/<case> "" build` from the snapshot.

### 3.8 Traps the last leads fell into

- **pkill can kill your own shell.** `pkill -f <pattern>` matches every process whose command line
  contains the pattern, including the shell that runs it, and a heredoc counts as part of that command
  line. The lead session runs on `lift11`, which is also a worker. Use `[x]`-style patterns, kill by pid,
  or send the script to `ssh <lift> 'bash -s'` from a file written earlier. `stop-run.sh` is safe.
- **A head's command line does not carry its output path** (`run_engine.sh --config …`): `pgrep -f
  accept-<round>-<case>` finds the workers, not the head, and says "dead" for a live run. Tell a live run by
  `ps -g $(cat accept-<round>-<case>/pgid)` on its head host.
- **A starved head step looks like a hang:** a step that needs more than the ledger can ever free on a busy
  lift waits silently (`waiting for memory for a head step … on any host`). Main now holds the best host for a
  waiting step and starts GROW's planner at 2 GB; if a log goes quiet for many minutes, read the step's own
  stderr (`obligations-<NNNN>/grow-stderr.log`).
- **Never rebuild a tree that someone reads.** Agents run checks on `~/hadoop-hdfs-unified` and the Solr
  trees too: check `pgrep -fc '[h]adoop-hdfs-unified'` (etc.) on every lift first; replays read the tree's
  `target/classes` directly.
- **Parallel coverage or test runs can corrupt a tree's `target/test-classes`** (a broken `ssl-client.xml`
  once failed every HDFS workload; the backup is in `/bigtemp/vnr3ne/analysis/corrupt-test-classes/`).
- **A monitor re-armed on `round-monitor.sh` re-reports every finished case;** filter out the ones you have.
- **One run is not a verdict on a flaky case.** 11741 (balancer dispatcher timing) and solr-18413 (ZooKeeper
  watch timing, Overseer queue) have real races; a CONFIRM refutation there can be the race, not the branch.
- **Composite changes hide their culprit.** When several branches are stacked in one snapshot and a case fails,
  run the case on plain main and on main + one branch before deciding.
- **The home quota is 100 GB** and has filled twice: round outputs, VM images and worktrees of other trees go
  to `/bigtemp/vnr3ne`. Remove old snapshots with `tools/rounds/snapshot-gc.sh` (it refuses one in use).

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
export CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-w4h/j2sdk-image
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

**The picks (Phase 2) are run directly, one campaign per check**, not through the nightly chain
below. Cases are `<check>.<workload>` ids (the pick lists of §0.4):

```bash
cd ~/gc-run/p<N>        # a built snapshot of main (for HDFS checks on another tree, §3.7)
GC_OUT=/bigtemp/vnr3ne/gc-out VM_IMAGE=/bigtemp/vnr3ne/vm-w4h/j2sdk-image setsid nohup \
  bash tools/adhoc/sweep.sh ~/gc-run/p<N> <round> <cases-file> 1 > /bigtemp/vnr3ne/gc-out/sweep-<round>.log 2>&1 < /dev/null &
GC_OUT=/bigtemp/vnr3ne/gc-out tools/rounds/round-monitor.sh '<round>-*' | grep --line-buffered 'DONE '
GC_OUT=/bigtemp/vnr3ne/gc-out python3 tools/adhoc/triage.py <round>     # class, stage, reason per check
```

Case `n` of the file writes `$GC_OUT/accept-<round>-<n>` (`sweep-<round>-cases.tsv` maps n to the id); each
case has `CASE_TIMEOUT_SECONDS` (5400 s by default); the sweep waits for head room by itself (a quiet log at
the start is the ledger, not a hang). Triage classes: CONFIRMED, REFUTED (a real false positive: keep it),
NO_WITNESS, NO_ROOT, STOPPED (stage + reason).

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
    (`<case>/<check>`): CONFIRMED, CONFIG_ONLY (confirmed, every moved root a configuration),
    REFUTED, NO_ROOT, NO_WITNESS, STOPPED, DEAD, RUNNING, PENDING; `gc-out` defaults to
    `gc-env.sh`'s `GC_OUT`.
14. `findings.py <sweep-dir> [--ledger $GC_OUT/findings/ledger.jsonl] [--static $GC_OUT/static/<key>]`:
    one row per mechanism among the confirmed witnesses (`findings.tsv`), weighted by kind,
    mediation and (1 + the rate at which REPRODUCE reproduced it natively at its anchor), the
    configuration-only ones last; the ledger marks each new, known or dismissed.

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

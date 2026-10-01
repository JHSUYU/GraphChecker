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

## 0. Handover (state at 2026-09-30 ~13:00 EDT, main = `f3b31968a`)

### 0.1 The goal

The owner's active goal, verbatim: «跑通solr这两个case的.smt。完成后。为了找到新bug。在hdfs和solr上都去做大规模的adhoc
check，并让我们的引擎给这样大规模的check提供更多的支持。worklaod都用已有的cluster based unit test»

1. **Phase 1:** a correct `.smt` for **SOLR-18413** and **SOLR-18406** (both CLOCK_SKEW), while
   the nine HDFS cases keep passing on the current VM.
2. **Phase 2:** large-scale ad-hoc checks on HDFS and Solr to find new bugs, with the systems'
   **existing cluster-based unit tests** as workloads (HDFS `MiniDFSCluster` tests, Solr
   `MiniSolrCloudCluster` / `SolrCloudTestCase` tests), and engine support for checks at that
   scale.

The owner's requirements R1–R6 that everything is measured against are in
`/bigtemp/vnr3ne/analysis/audit/COMMON.md`; `docs/STATUS.md` is organised by them.

### 0.2 Where each case stands

A **PASS** is `experiments/accept/report.py`'s verdict: SAT_CANDIDATE, no BLOCKING gap, the
case's expected mechanism, `polarityDecides`, a confirmation, and every moved root inside the
causal cone (`cone.py`). The owner additionally checks the `.smt` causal chain by hand against
the system's code (§1). All runs are under `/bigtemp/vnr3ne/gc-out/accept-<round>-<case>/`.

| case | best live run | verdict | mechanism / blocker |
| --- | --- | --- | --- |
| hdfs-17897 | `r7`, `rb1` | PASS | MARKER_FLIPPED, IPC request door `REGION.763d087e` |
| hdfs-17899-bug1 | `r7` | PASS | MARKER_FLIPPED, IPC request door (`in.305c06e3`) |
| hdfs-17899-bug2 | `r8` | PASS | MARKER_FLIPPED, IPC response door `REGION.9ffdee3d` |
| hdfs-17899-bug3 | `r7` | PASS | MARKER_FLIPPED, IPC request door (`in.305c06e3`; earlier rounds moved the response door) |
| hdfs-17960 | `r8`, `rb1` | PASS | MARKER_FLIPPED, `HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED=false` |
| hdfs-17967-pathA/B/C | `r7` | PASS | MARKER_FLIPPED, IPC request door |
| hdfs-11741 | `r8` | FAIL | CLOCK_SKEW found (NN + DN clocks, polarityDecides) but 22 BLOCKING gaps; all fixed on branch `agent-11741-regress` (§0.3) whose fresh-seed round `rb1` is running. Residual risk: 3 of 4 NN clocks move only through the `clock_order` constraint and may fail `cone.py` (the v93 failure mode). |
| **solr-18406** | `a37f4` (branch, not main) | **PASS** | CLOCK_SKEW, polarityDecides, one clock root `M_J_field_REGION.57488ec0…Long` moved, CONFIRMED ("every edge the model chose was taken, and the claim's anchor observed the fatal"), 7 declared roots in the cone. Code is on branch `worktree-agent-ae3796f20246f25c6` (§0.3), NOT merged. On main (`r7`, `rb1`) 18406 still fails: its one anchor path is UNSAT with every root free. |
| **solr-18413** | `r9` (main `a53174bf1`) | FAIL, last step | The `isExpired#u6` flip is SAT (Overseer `MigrateCmd` clock +262 s) and its replay REPRODUCES the bug ("Could not find collection : causynthMigrate-target") and is ADMITTED; the wave-0 IMPORT gate then stops on one BLOCKING row: invariant 9, the target row that observed the fatal states no `phiTerm` because the fatal condition (`targetColl == null`, `DistributedZkUpdateProcessor:932`) is concrete in the replay. A WIP fix is on branch `worktree-agent-a564ae2a2ad314535` (§0.3). |

The 18413 chain in Solr 8.11 (tree `~/lucene-solr-18413`): Overseer task `MigrateCmd.java:196-205`
`expireAt = RoutingRule.makeExpiryAt(timeout)` (`RoutingRule.java:60-62`, Overseer clock + 1 s) →
queue item (`ZkDistributedQueue.java:328`, store door `SolrZkClient.java:446`) → Overseer tick
`SliceMutator.addRoutingRule` (`SliceMutator.java:225`, `:238-257`) → `state.json` write
(`SolrZkClient.java:392`) → leader StateWatcher `ZkStateReader.java:1345-1385`,
`ClusterState.load` → `Slice.java:204-212` → `RoutingRule.java:48` `parseLong(expireAt)` → leader
`/update` `DistributedZkUpdateProcessor.processAdd` (`:233`, `:254-265`) → `getNodesByRoutingRules`
→ `:925 !rule.isExpired()` (leader clock, `RoutingRule.java:66`) → `:932` target lookup null →
`:934` throw. In the recording the rule is expired, so `:932-934` never run; the witness moves
the Overseer clock so the rule is still valid at the leader. The flip obligation's formula
already states the chain: `vH_overseer = clk_Overseer + 1000`, `vH_leader = vH_overseer` (ZK
handoff), `vH_leader >= clk_Leader + 60000`.

### 0.3 Branches and worktrees in flight (nothing here is on `main` unless it says so)

All agents were stopped at the handover. Uncommitted work was committed as `WIP (handover,
untested)` on its own branch. Worktrees under `.claude/worktrees/agent-*` are git worktrees of
this repo; `git worktree list` shows them all.

| branch (worktree) | head | content | state | next step |
| --- | --- | --- | --- | --- |
| `worktree-agent-ae3796f20246f25c6` | `ba1a3de59` | **SOLR-18406 fix**, 5 commits: `fef79768c` a long sum is a Long cell; `9cc025e68` a flip query binds only what its text names; `d573e4e72` a planted clock runs on from its plant; `6daf4e490` a confirmation plants a clock on the recording's timeline; `ba1a3de59` a claim's clock moves are its jumps. Rebased on a recent main. | live run `accept-a37f4-solr-18406` (snapshot `~/gc-run/a37p4` = the pre-rebase `bfb6be211`) **PASSES**; gates on the rebased head were running when stopped | 1) review the 5 commits (clock planting changes CONFIRM for every CLOCK case); 2) offline gate `--round r8 --round r7` on the HDFS cases (COMPOSE+CONFIRM identical) and on 18406; 3) merge; 4) re-run 18406 + 11741 live |
| `worktree-agent-a564ae2a2ad314535` | `6ba631b27` (WIP) | 18413: a fatal arm observed under a concrete condition states its phi (RowInvariants, JavaPrimitiveSmtSemantics, CONTRACT-SPEC) | **WIP, not built, not gated** | finish: the rule is "a concrete fatal condition publishes phi as the constant of the arm taken; the causal chain rests on the path condition reaching the anchor" — never a silent empty phi, never BLOCKING; re-run IMPORT..COMPOSE offline on `accept-r9-solr-18413` (expect CLOCK_SKEW with both clocks moved), gate HDFS, merge, run 18413 live |
| `agent-11741-regress` | `ffed14866` | 11741 regression fixes: `2b4bf4391` order by row seq not anchor chain (TOPOLOGY_DIVERGENCE); `62aa5d992` a pool task keeps the frames it was submitted under (OCCURRENCE_ADDRESS_SHARED; changes every pool-task address); `c76077d8b` an export stating no expression; `f0cb0686e` Independence demands only what lowering reads; `ee1b030ac` a valuation undecided whole is asked per path (and fixes a live main bug: `seedDisjunctUnsat` asserted every seed selector at once); `7b0f25f2d` test; `fab3758c8` probe per path. Merged with main `a53174bf1`. | reviewed "merge after fixes"; fixes (b),(c) done; fresh-seed round **`rb1` running** (snapshot `~/gc-run/p183`) | read `rb1`: so far 17897, 17960 PASS; **17967-pathC FAILS** (witness moved `HDFS.BLOCK_KEY.SERIAL_NO` instead of an IPC door fault — a regression vs main's r7); find why before merging |
| `worktree-agent-ab7747be564843aea` (R1-ROOTS) | `35c5eec90` | R1-ROOTS WP-C (fault doors from the engine library catalog `src/main/resources/.../library-catalog.jsonl`, DOOR rows gone from case mappings, `ScopeGrowth --doors`) + WP-S (exception-aware control dependence `FaultPropagation`, `.throws` guard cells, `LibraryReceivers`), merged with main `8820c3129` | live A/B round **`ra1`** (snapshot `~/gc-run/p182`): pathA/B/C, bug3 PASS; **17897 FAIL** (new BLOCKING PLAN OCCURRENCE_ADDRESS_SHARED on the new SASL door region, `ctx:Lost:UNKNOWN`); **17960 FAIL** (wave-1 planner OOM at 8 GB: the target region grew 12→32 methods into fsimage serialization); others running | fix both (the pool-task identity fix in `agent-11741-regress` may cure the shared address; the 17960 planner OOM needs a general memory or scope fix), re-run `ra1`, merge. W3 depends on it. |
| `worktree-agent-a2a3969b54657da82` (WIRE-CODEC W3) | `c9776df4b` | W3 static key-jump on top of R1-ROOTS: `242f12133` a read of a codec key demands every write of it; `812c6d339` offline gate reads the side's codec declarations; `c9776df4b` a codec port reads a message's fields only once Soot lists them | stopped mid-work (docs update); not gated | finish per spec §3 (schema 6 bump lands here, CODEC_PORT rows, demanded-port file for W4's `runtime/DemandedPorts`), gate SEED on 11 cases |
| `worktree-agent-aa7a714834869b4df` (WIRE-CODEC W1+W4) | `638509485` (WIP) | W1 VM natives `exportLeaf`/`mintLeaf` + W4 runtime (CodecWeave, CodecWalker, holes/templates, message binding, CSE6 envelope, HandoffMint), append-range VM fix; live 18413 evidence in `/bigtemp/vnr3ne/gc-out/w4-18413-1` | reviewed "merge after fixes"; the WIP commit holds fixes (a)–(d) half done, **not built** | finish review fixes: (a) template mismatch → named `CODEC_MISMATCH`, no pairing; (b) VM refuses minting on an object that already carries an expression and checks holders for JVM-wide identity, runtime mints on fresh String copies; (c) admission gate opens only for value operands (String/box/StringBuilder) and never while paused; (d) `envelopeBytes` required/default 4 KB for HTTP, bounding the whole header; + minors. Rebuild image to `/bigtemp/vnr3ne/vm-w4b` (a partial one may exist there — rebuild), smoke, merge main, then a live round on vm-w4b (the reviewer's list: 9 HDFS no codec rows 8/9 with matching obligation counts; one codec-declared HDFS run; one Solr run with 0 VALUE_MISMATCH) |
| `worktree-agent-ac487236f0fb1620e` | `093ae45b3` | time: `2736970e1` `tools/analysis/timeline.py` (where a campaign's wall time went); `a5ae0d849` a focused replay ends at the refusal that decides it and publishes no session; `bb1dd2e1e` a replay's end runs once; `0c7d19b99`, `093ae45b3` | live: `accept-ee-17899-bug1` PASS in 1031 s (r7: 2192 s), `accept-ee-17967-pathA` PASS in 1088 s (r7: 1622 s); verdict comparison with r7 was in progress | compare verdict/moved roots with r7, review (replay exit path is high-risk), merge |
| `worktree-agent-ab6c654a022ddde8f` | `afe4a2599` | WIRE-CODEC W1 alone | superseded by the W4 branch (which contains it) | delete after W4 merges |
| `r3-*`, `vm-f14`, `views-test`, `w4-p2`, other `worktree-agent-*` with `ahead=0` | — | already merged into main | — | safe to remove (`git worktree remove`, `git branch -d`) |

Snapshots (`~/gc-run/p<N>`, each a detached worktree with its own built jar): **p182 (ra1) and
p183 (rb1) are in use by running rounds — do not remove them.** p175–p181, `a37p1-4`, `ee1`,
`ee2` are free once you no longer need their runs.

### 0.4 Rounds still running on the lifts

`ra1` (R1-ROOTS A/B, all 11 cases, snapshot p182) and `rb1` (11741 branch, fresh seeds, all 11
cases, snapshot p183), both on VM `/bigtemp/vnr3ne/vm-r3b/j2sdk-image`. Watch and stop:

```bash
cd ~/GraphChecker
GC_OUT=/bigtemp/vnr3ne/gc-out tools/rounds/round-monitor.sh 'ra1-*' 'rb1-*' | grep --line-buffered 'DONE '
GC_OUT=/bigtemp/vnr3ne/gc-out tools/rounds/stop-run.sh ra1-11741 ...    # one or more <round>-<case>
for d in /bigtemp/vnr3ne/gc-out/accept-rb1-*; do tail -1 $d/summary.tsv | cut -f1,4,11,12; done
```

### 0.5 TODO, in dependency order (run every item with no open dependency IN PARALLEL, §2)

**Phase 1 — the two Solr `.smt` (critical path):**

1. **18406:** review + gate + merge `worktree-agent-ae3796f20246f25c6`; live-run 18406 and all
   CLOCK cases on main; hand-check its `.smt` chain against Solr (`IndexDeletionPolicyWrapper`
   `latestCommit`/`reserves`/`knownCommitPoints`, `ReplicationHandler` file list, the reservation
   expiry clock).
2. **18413:** finish the phi rule (branch `worktree-agent-a564ae2a2ad314535`), validate offline on
   `accept-r9-solr-18413`, merge, live-run; hand-check the chain in §0.2. Open defect 28 in
   STATUS (store-door race: `MessageDoors.stored` files what a write carried only after
   `outboundExchange` logged the SEND that releases the Overseer's tick) can leave the queue link
   unpaired in some seeds.
3. **HDFS 9/9:** decide `agent-11741-regress` from `rb1` (fix the pathC regression first); then
   check 11741's cone (the 3 NN clocks moved only by `clock_order`: either the claim reports only
   causally relevant moves or `cone.py` accepts order-forced moves — a design decision to write
   down, not a per-case patch).
4. After each merge that touches a case: re-run the round and **check every `.smt` causal chain**
   against the system code (§1 rule).

**Engine support for scale (Phase 2 prerequisites):**

5. **Time.** Merge the early-exit branch (`worktree-agent-ac487236f0fb1620e`). Then, with
   `timeline.py` after every round: decide an obligation NOT_ADMITTED before replaying it when its
   flip needs a value the replay cannot plant; pipeline waves instead of a barrier (a wave waits
   for all its replays; a Solr replay under Zero takes ~20 min; r5 18413 was 3 h 10 min in 6
   waves, and all 67 focused replays served obligations that ended NOT_ADMITTED).
6. **R1-ROOTS:** fix `ra1`'s two failures, merge. Then the rest of the R1-ROOTS spec
   (`/bigtemp/vnr3ne/specs/R1-ROOTS-proposal.md`): WP-D config roots, WP-E admission by relevance,
   WP-F1/F2 root demand.
7. **WIRE-CODEC** (`/bigtemp/vnr3ne/specs/WIRE-CODEC-proposal.md`; W0, W2, W5 are on main): W3
   (after R1-ROOTS), W4 review fixes, then **W6** (declarations `experiments/{hadoop,solr}/wire.jsonl`,
   tree adapters pass payloads: `SolrZkClient`, `CausynthHttp.respond`, Hadoop `Client`/`Server`
   via the shim; views for `ClusterState`, `ShardTerms`, `AutoScalingConfig`; a node alias for the
   Overseer's pre-tick decodes; delete all `WIRE_FLOW` rows, revert the HDFS `Integer.toString`
   patches and Solr `fdf91e8` + the per-branch `consumed` commits; §4.9 deletions), then **W7**
   validation (11 cases live + one sweep each system). Ad-hoc checks need this: no hand rows.
8. **ADHOC-INFRA** (`/bigtemp/vnr3ne/specs/ADHOC-INFRA-proposal.md`; WP4, WP5.A, WP1, WP5.C, WP2
   and WP5.B's build key, nightly and snapshot locks, and WP5.D phase 1 (REPRODUCE plants fault
   markers natively) are on main): WP5.B's `regress.sh` (the day's engine-fix regression list
   that places the `regress-pass-*` tag the nightly freezes; tagged by hand until then), WP5.D
   phase 2 (clock and config plants), and WP3's rest: a batch shares its checks' recording,
   aggregation and seed replay (PIPELINE §2b; checks whose plans agree share one seed), but checks
   that reach their own target at one occurrence still replay apart (a task with a list of target
   branches in the runtime, M1/M2), and each check's slice is its own Soot pass (WP3.1, one scene).
   The first nightly slices every declared check under the new build key.
9. **R3 leftovers** (`/bigtemp/vnr3ne/specs/R3-REFCONT-proposal.md`): WP3b/c (TreeMap,
   ConcurrentSkipList*, LinkedList, CopyOnWrite*, queues in the VM), WP7 (`cone.py` follows writer
   families), D3 (STATE arms from other sessions); the VM does not state a container query's
   answer (`ContainerSupport::query_state`).

**Phase 2 — the sweeps** (after 1–2): follow "Run an ad-hoc sweep" below on HDFS
(`~/hadoop-hdfs-17967-c`) and Solr (`~/lucene-solr-8_11-adhoc`), all ten lifts; triage with
`triage.py`, dedupe with `findings.py`; a finding is new only if CONFIRMED and not a known
mechanism (the two old token-expiry CLOCK_SKEWs were judged HDFS's clock-sync assumption).

Open defects with numbers are listed at the end of `docs/STATUS.md`.

### 0.6 Designs and analyses (outside the repo, on `/bigtemp/vnr3ne`)

| path | what |
| --- | --- |
| `/bigtemp/vnr3ne/specs/WIRE-CODEC-proposal.md` | values cross processes at serialization boundaries as typed holes by key path; W0–W7; **"Designer decisions" blocks at the end are binding** (1–13) |
| `/bigtemp/vnr3ne/specs/R1-ROOTS-proposal.md` | automatic roots: library door/config catalog, slice rules, config roots, relevance admission, root demand |
| `/bigtemp/vnr3ne/specs/ADHOC-INFRA-proposal.md` | ad-hoc checks at scale: WP1 selection by slice, WP2 pre-screen, WP3 shared recording, WP4 line targets, WP5 operations |
| `/bigtemp/vnr3ne/specs/R3-REFCONT-proposal.md`, `R3-shapes.md` | shared state in one JVM: reference cells, containers, owner-indexed answers |
| `/bigtemp/vnr3ne/specs/C2.md`, `F14.md`, `DOCS.md` | the single binding rule JOIN→MINT→PIN; VM f14; docs policy |
| `/bigtemp/vnr3ne/analysis/audit/COMMON.md` | the owner's requirements R1–R6 (the yardstick) |
| `/bigtemp/vnr3ne/analysis/audit/*.md` | code audits per area (vm, slice-scope, wire-identity, explore-compose, adhoc-scale, system-specific); may be older than main — the code wins |
| `/bigtemp/vnr3ne/analysis/review*/`, `/bigtemp/vnr3ne/ab/` | past review notes; offline A/B gate outputs |

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
| HDFS trees | `~/hadoop-hdfs-<case>` (worktrees of `~/hadoop`, branch `gc/<case>`); ad-hoc HDFS checks run on `~/hadoop-hdfs-17967-c` only |
| Solr trees | Solr 8.11 worktrees of `~/lucene-solr-8_11`: `gc/solr` (shared adapter), `~/lucene-solr-18406` (`gc/solr-18406`), `~/lucene-solr-18413` (`gc/solr-18413`), `~/lucene-solr-8_11-adhoc` (`gc/solr-adhoc`). Ant build; native Ant tests need `-Dtests.useSecurityManager=false`. `~/solr` is apache/solr main (blobless: never `git grep` a commit there). |
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
  tools/rounds/launch-round.sh ~/gc-run/p<N> <round>              # all 11 cases, heads placed per host
CASES="hdfs-17960 solr-18413" ... tools/rounds/launch-round.sh ... # a subset
GC_OUT=/bigtemp/vnr3ne/gc-out tools/rounds/round-monitor.sh '<round>-*' | grep --line-buffered 'DONE '
GC_OUT=/bigtemp/vnr3ne/gc-out tools/rounds/stop-run.sh <round>-<case> ...
```

- Every tool takes `GC_OUT` from `tools/lib/gc-env.sh` (default `/bigtemp/vnr3ne/gc-out`).
- A round name is written once (`accept-<round>-<case>` exists → refused). Names used so far:
  `v*`, `r1`–`r9`, `ra1`, `rb1`, agents' `a37f*`, `ee*`, `agent-*`, `w4-*`.
- Typical wall time: HDFS cases 16–50 min (11741 longest), Solr 40 min–3 h.

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
→ per wave `iteration-0000/obligations-<NNNN>/<id>/` (`obligation_query.smt2`,
`obligation_result.jsonl`, `replay.log`) → sessions `iteration-0000/sessions/<id>/`
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
EXPLORE     waves: plan flip obligations (explore/ExploreMain), solve each, replay it
            focused on its world (runtime/FocusedReplay), grow the woven regions (GROW)
COMPOSE     merge all sessions into one disjunction over the anchor, solve it per
            valuation with z3, decide the claim (compose/ComposeMain: Composer, ClaimPolicy)
SOLVE/DECIDE  check and print the solver verdict and the claim COMPOSE published
CONFIRM     re-run the witness world, check its edges (explore/ConfirmMain)
REPRODUCE   run a confirmed witness natively: the recording weave on the stock JDK,
            planting only its fault markers (runtime/RecordingPlant), N times
EMIT        final/result.json, gaps.json, run-manifest.json
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
  lambda body, an anonymous class) in the compiled classes; the tree carries no annotation and is
  not rebuilt. The thrown type is needed only when the line holds two throws;
- optionally `communication-mappings.jsonl` (`DOOR` and `WIRE_FLOW` rows; on the R1-ROOTS branch
  doors come from the engine's library catalog instead), `root-domains.jsonl` and
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

Obligations of a campaign fan out over the hosts in `CAUSYNTH_CAMPAIGN_WORKER_HOSTS`, the first
host rotated per wave. Every start on a host is charged to the ledger first: an obligation
(`obligation_memory_mb`, for 60 s), a campaign head's engine JVM (`engine_memory_mb`, else 8192, for
120 s), its seed and CONFIRM replays (`obligation_memory_mb`, for 300 s), and a `fanout.sh` job
(its `NEED_MB`, for 120 s). A start goes only when `MemAvailable` covers its need, every start
still in its ramp there and a reserve that keeps the host at most `CAUSYNTH_HOST_MAX_USED_PCT`
(70) percent full; a head's start is released when it returns.
A head's "waiting for memory" line goes to stderr (its stdout is often an artifact).

## Run an ad-hoc sweep

An ad-hoc check is a guarded `throw` that a system's existing cluster test reaches and passes.
A case is one check on one workload (`<check>.<workload>`), or a batch of checks on one workload
(`B<n>`, a row of `batches.tsv` with its target spec `targets/B<n>.yaml`, `batch.sh`). The
experiments are `experiments/hadoop/adhoc` and `experiments/solr/solr-adhoc`; each holds
`checks.tsv`, `batches.tsv`, `occurrences.tsv`, `targets/` and `tree` (the one tree it runs). A
check's slice starts from the classes its experiment's communication mappings name (`system.sh`'s
`system_mapping_scope`) and its own class, and grows the scope from there. A sweep runs batches:
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
12. `STATIC_ROOT=$GC_OUT/static/<key> sweep.sh <snapshot> <round> <sweep-dir>/cases.txt
    [heads-per-host]`: one campaign per batch over all ten lifts, `PRUNE=1`, 5400 s per case;
    restartable. A batch records once, plans each check, and seed-replays each group of checks
    whose plans agree once (`out/<batch>/schedule/groups/`); each check explores on its own.
13. `triage.py <round> [gc-out]`: outcome class per case, and per check of a batch case
    (`<case>/<check>`): CONFIRMED, REFUTED, NO_WITNESS, STOPPED, DEAD, RUNNING, PENDING; `gc-out`
    defaults to `gc-env.sh`'s `GC_OUT`.
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
| `out/<case>/schedule/iteration-0000/` | `execution_task_plan.jsonl`, `concolic_region_plan.jsonl`, `recorded_schedule.jsonl`, `sessions/<id>/`, `obligations-<NNNN>/` (per wave: one worker directory per obligation), `obligation_results.jsonl` |
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
  explore/     corpus, closure, frontier, flip queries, obligations, wave graph, ExploreMain,
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
                                  (which runs a process on any lift still names)
tools/rounds/                     launch, monitor and stop campaigns on the lifts; snapshot-gc.sh
tools/adhoc/                      ad-hoc check discovery, build key, slicing, selection, pre-screen,
                                  sweeps, the nightly, triage, findings
tools/regress/                    offline-ab.sh: the offline merge gate
tools/analysis/                   occurrences.py (a selector from a discovery log), timeline.py (where a
                                  campaign's wall time went), the pairing probe,
                                  batch_share.py (how much of a batch's per-target seed plans one
                                  replay could share)
docs/STATUS.md                    done / partial / not done, per requirement; open defects
docs/design/                      the design of main (index: docs/design/README.md)
```

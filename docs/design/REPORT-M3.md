# REPORT-M3 — EXPLORE on the Design 3 contract

Branch `refactor/d3-explore`, worktree `SPN/wt-d3-explore`, base `9b9961b0a`.
`refactor/d3-contract-pkg` @`0fb76bc23` merged (fast-forward, no merge commit).
**Tip `ddafa1407`** — "d3.explore: focused tasks, obligations with interaction
families, waves", over `5c6d23048` — "TEMPORARY placeholder:
d3.compose.SmtLowering (delete on the compose merge)".

Gates: `mvn -o -q -DskipTests compile` clean; `mvn -o test` **70 tests, 0
failures, 0 errors** (61 existing + 4 contract + 5 new; cap 80). Nothing
outside `d3/explore`, `d3/compose/SmtLowering.java` and the new test is
touched — no existing package has a dependency on this one yet.

## 1. Files (11 main + 1 placeholder + 1 test, 3 182 lines)

| file | lines | what it is |
|---|---|---|
| `d3/explore/FlipQuery.java` | 582 | one obligation's query: the four rules (root, clock, handoff family, state join) and the symbol fixed point |
| `d3/explore/Corpus.java` | 400 | the iteration's sessions, indexed the way identity works |
| `d3/explore/ExploreMain.java` | 277 | the CLI and the wave loop |
| `d3/explore/ObligationFactory.java` | 265 | per path, per decision: build, solve, become an obligation or a verdict |
| `d3/explore/ClosurePlanner.java` | 205 | the anchor's closure as a list of tasks |
| `d3/explore/SmtText.java` | 195 | tokens, renaming, literals, unique names |
| `d3/explore/Frontier.java` | 188 | the per-task fixed point; a wave is their union |
| `d3/explore/Z3Solver.java` | 180 | the process run and the model read-back |
| `d3/explore/ExploreCodec.java` | 170 | JSON for task / obligation / result / root domain |
| `d3/explore/SessionReader.java` | 101 | one session's rows, one file per kind |
| `d3/explore/ExploreIds.java` | 38 | sha16 for the ids the contract does not mint |
| **main total** | **2 601** | |
| `d3/compose/SmtLowering.java` | 146 | PLACEHOLDER, own commit, deleted by the compose merge |
| `src/test/.../D3ExploreTest.java` (5 @Test) | 435 | five synthetic corpora, solved by the campaign's z3 |

The explore side it replaces, for scale (deleted by step D, not by me):
`ConcolicPathFlipPlanner` 466 + `ConcolicPathFlipSolver` 186 +
`RegionPathWorklist` 1 162 + `BranchReplayContract` 975 + `HandoffFamilyRows`
557 + `ResolvedFlipQuery` 165 + `LinkedReplayBundle` 229 +
`PathReplayTaskFactory` 517 + `ReplayTaskSlice` 523 = **4 780**, plus the flip
half of `ConcolicConstraintSolver` (2 370 lines, shared with nothing else).
New: 2 601.

## 2. What the module does, in the order it does it

1. **`ClosurePlanner`** — from the corpus and the declared anchor: the anchor
   occurrence, the **producer** of every interaction its paths read
   (transitively: an export's own nested `v_H` has a producer, which is how a
   key id forwarded NN → balancer → DN ends at the mint and not at the first
   hop), the **writer** of every version its paths read, and the occurrences
   its node's state connects it to. One `Task` per closure element, each
   carrying its state-connected `factor`; a wire producer is never a factor —
   it is another node's activation, therefore its own task, explored on its
   own frontier and admitted on its own prefix. `--max-tasks` (64) truncates
   with a named gap rather than silently.
2. **`ObligationFactory`** — per admitted path of the focused occurrence
   (one path = that occurrence's decisions in one session), per decision whose
   predicate mentions a root, a `v_H` or a clock: the prefix decisions in the
   arms they took ∧ the complement of that decision. The query is solved with
   z3 through the shared lowering; the model becomes `rootAssignments` (keyed
   by root id, applied at the mints) and `answers` (keyed by attach endpoint
   id, applied at the attaches of the focused occurrence). A query the solver
   refuses, or answers UNSAT, is closed here and never issued, so a wave costs
   a replay only for a flip some world of the corpus supports.
3. **`FlipQuery`** — the four rules, and nothing else, decide what a symbol may
   be: a ROOT is one quantity across the corpus (free inside its declared
   domain, free over both values when it is a declared marker, PINNED when it
   has no domain — because the composer pins it there too and a flip that needs
   it to move could never become a finding); a CLOCK is per path, unbounded,
   `>= 0` only; a HANDOFF `v_H(I)` is bound by its family keyed by the
   INTERACTION (both endpoints) `⋁_q (π_q ∧ guard_q ∧ v_H = e_q)`, closed over
   the handoffs those arms name in turn to a fixed point, with `guard_q`
   stating only the roots this corpus **varied**; a STATE read joins the write
   version it observed, else its stated value, else the obligation is refused
   naming it (`UNSTATED_VALUE`). A control with no arm stays free and is listed
   `unproducible`; a nested handoff with no arm is pinned to the arrival the
   recording states. An arm from a producer that ran concretely is UNATTESTED
   and says so (`UNATTESTED_ARM`, R-I5).
4. **`Frontier`** — per task: issued, consumed, retired. `VALIDATED` puts the
   replay's session into the corpus, whose new path yields new obligations with
   new ids on the next wave (this is how a nested guard chain deepens one
   decision per wave); `UNSAT` closes; `NOT_ADMITTED` / `DIVERGED` are recorded
   and never retried with the same query. **Admission is per task**: a result
   is keyed by obligation, so one task's prefix mismatch can never reject
   another's — the linked-replay coupling is gone by construction.
5. **`ExploreMain`** — `--iteration --target-occurrence --root-domains
   --max-waves --out` (plus `--z3`, `--solver-timeout-ms`, `--max-tasks`,
   `--max-obligations-per-task`, `--solver-threads`). Writes `tasks.jsonl`,
   then per wave `obligations.jsonl` (what the runtime runs), `closed.jsonl`
   (what the solver closed), `gaps.jsonl`, `smt/<obligationId>.smt2` for every
   query **whatever its verdict**, and `explore_manifest.json` stating
   `PENDING_RESULTS` / `FIXED_POINT` / `MAX_WAVES`. It rebuilds its frontier
   from the wave files, so the engine can invoke it in a loop and each
   invocation consumes every wave whose `results.jsonl` exists before planning
   the next. One task's candidate flips are solved `--solver-threads` (4) at a
   time, in candidate order, so the wave file does not depend on the thread
   count.

## 3. What was kept from the old explore code

| kept | from |
|---|---|
| obligation = the path as its replay ran it ∧ the complement of one decision | `BranchReplayContract.requiredPathPredicates` |
| family = row selection: producer path's π, the valuation it ran under, `v_H = e_q`; refusals named, never silently dropped | `HandoffFamilyRows` (+ `ConcolicConstraintSolver.stateHandoffFamilies` / `armTerm` / `armsNotLoweredBecause`) |
| the nested-`v_H` closure to a fixed point, and a nested variable with no arm pinned to its recorded arrival | `HandoffFamilyRows` WIP `c99b77013` (HANDOVER-E1: the 120005 cause) |
| only roots the corpus **varied** are stated as arm guards; a clock never is | REPORT-PRODUCIBLE §2 |
| declared domains relative to the recording (`+0`/`+3` → `[119992, 119995]`) | REPORT-PRODUCIBLE §2, `PathMergeComposer` bounds |
| a root with no domain is pinned, here as in the composer | REPORT-PRODUCIBLE §7 |
| a declared marker free over both values; clocks unbounded with a `>= 0` floor | REPORT-ROOTENUM §2 |
| answers applied at the attach, values from the model | REPORT-ANSWER4 |
| the wave loop stops on a fixed point over obligation identity and verdicts, not on "the obligation I planned is done" | REPORT-DEPTH (b) |
| attested vs unattested arms | INTERACTION-ID R-I5 |
| the z3 process shape and "always write the .smt2, whatever the verdict" | `ConcolicConstraintSolver.run`, `ConcolicPathFlipSolver` |

**Deliberately not carried over**: companions / `LinkedReplayBundle` /
`ReplayTaskSlice` and slice-based admission (Phase 2 makes admission
per-region); request-family and handoff-phase keys (families are keyed by the
interaction); the Merkle compaction of worklist rows (expressions live once per
session in `expressions.json`, so a row references a ref instead of carrying a
DAG); `preferObservedReplayControls`' soft pins on every control (a solver
preference, not derivable from the design — with families every answer is
already one a producer makes).

## 4. Evidence

**Unit (5 @Test, z3 4.8.12, `Assume` on z3 being present).**

1. *depth*: a corpus whose recording took `¬a` yields exactly one obligation at
   `Guard#u8` with `CASE.MARKER := true`; feeding back a VALIDATED session that
   took `a` and then decided `Guard#u19` gives a wave-1 obligation at
   `Guard#u19` whose own model still carries `CASE.MARKER := true` and needs
   `CASE.COUNT > 5` — the earlier wave's answer is inside the later
   obligation's prefix, and no query is asked twice.
2. *family*: two recordings of one interaction (119992, 119995); a flip needing
   119995 is answered **119995**, `unproducible` empty. The negative control:
   the same corpus without the second recording, flipping to 7, is **UNSAT** and
   issues no replay — an answer out of the family is not available to the
   solver.
3. *unproducible*: an unpaired attach leaves the control free, the obligation
   lists its endpoint in `unproducible` and the run publishes an
   `UNPRODUCIBLE_ANSWER` gap naming the port.
4. *domains*: `M_SERIAL` recorded 7, no declared domain, flip needs `> 10` →
   **UNSAT**; the same root declared `+4 … +5` in `root-domains.jsonl` →
   satisfiable with `CASE.SERIAL ∈ {11, 12}`, and nothing outside.
5. *closure*: the writer of the version the anchor read is in the closure, as
   the anchor task's factor **and** as its own task; the producer of what that
   writer attached is its own task and is nobody's factor.

**CLI smoke** (`SPN/d-explore-m3/smoke`, a hand-written corpus in the
contract's file shape, not a test): two tasks (DN target, NN rotation), one
obligation, and the query below — the state join binds the read to the write's
expression, the family binds the handoff to the NN's exported serial, and the
declared relative domain resolves against the recording:

```
(assert (= vH_XCH_resp_block_key_id_1 st_allKeys_1))          ; the flipped arm
(assert (= vH_XCH_resp_block_key_id_1 r_HDFS_BLOCK_KEY_SERIAL_NO))  ; family
(assert (= st_allKeys_1 vH_XCH_resp_block_key_id_1))          ; state join
(assert (and (>= r_HDFS_BLOCK_KEY_SERIAL_NO 119992)
             (<= r_HDFS_BLOCK_KEY_SERIAL_NO 119995)))         ; +0..+3
```
Re-invoking with `results.jsonl` absent re-reports `PENDING_RESULTS` without
re-solving; answering `NOT_ADMITTED` closes that one query and the run reaches
`FIXED_POINT` with the NN task untouched.

**The M3 gate is not runnable yet.** BRIEF-M3 asks for 17897 and bug3 offline
on the M2 recordings; M2 has not re-recorded, and no corpus exists in the
contract's shape (today's corpora are the single-row
`concolic_region_results.jsonl` the runtime inventory describes). The module is
therefore exercised on synthetic corpora in the contract's shape only. What the
gate needs from M2, and nothing more: `activations.jsonl` with `focused`,
`decisions.jsonl` with SMT-LIB terms over the declared symbols,
`attaches.jsonl` with the paired producer endpoint, `exports.jsonl` with an
`expressionRef` into `expressions.json`, `roots.jsonl` with kind + resolved
domain, and `reads/writes.jsonl` with the observed version. The moment those
exist for 17897 and bug3, the gate is one `ExploreMain` invocation per anchor.

## 5. Deviations from the spec, each with its reason

1. **`d3.compose.SmtLowering` is a placeholder in its own commit `5c6d23048`.**
   `refactor/d3-compose` carries nothing but the contract merge, so there was
   nothing to merge. The three call sites are all in `FlipQuery`, all
   `session.lowering().lower(expressionRef)`; the integrator deletes the file
   with one `git rm` when the composer's lands. If its surface differs, the
   edit is `SessionReader.lowering()` plus those three calls.
2. **`d3.compose.CorpusIndex` does not exist**, so the module reads the rows
   itself (`SessionReader` + `Corpus`), which the mandate allows. If the
   composer later publishes an index, `Corpus` is the one class to fold into it.
3. **`π_q` for a family arm is the producer occurrence's whole recorded path in
   that session, not its prefix up to the export.** `DecisionRow` carries no
   session clock (the old rule was `clock < exportEventId`), and
   `ExportRow.handle` joins to nothing on a decision. This over-constrains an
   arm slightly — never the other way — and is restored by one ordering field
   on `DecisionRow`.
4. **Flips are cut from the focused occurrence's decisions only.** A task's
   factor replays with it, but `Obligation` names only `(siteId, ordinal)` and
   nothing that would say in which co-occurrence they are. No capability is
   lost: every state-connected member is itself a closure element and therefore
   its own task, where its decisions are the flipped ones.
5. **`π_q` keeps only producer decisions that mention a root or a handoff** (the
   old `mentionsRoot`, generalised). A producer decision over state reads alone
   would drag that session's joins into every arm.
6. **"Mentions a clock" is read from `DecisionRow.clockReadings`** as well as
   from a `CLOCK` root symbol in the term.
7. **A solver timeout has no `GapKind`.** It is published as
   `ADMISSION_GAP`/`DIAGNOSTIC` with detail `SOLVER_TIMEOUT …` and the query is
   not issued — the old "unexplored sibling, not a closed UNSAT" rule. If the
   contract gains a kind for it, it is one line.
8. **Sorts are inferred from recorded values** (`AttachRow.arrival`,
   `ReadRow.concreteValue`): `true`/`false` → `Bool`, else `Int`. Neither row
   carries a Java type; the old encoder's width conflicts came from trusting
   `javaType` over the declaration, so inferring from the value is the safer
   half of that lesson.
9. **A marker that is not `declared` is pinned** to its recorded value: "a root
   without a domain is pinned" applied to markers through `RootMintRow.declared`.
10. **An undeclared token in a prefix conjunct drops that conjunct** with a
    `DECLARATION_MISSING` diagnostic; in the **flipped** predicate it refuses
    the obligation (blocking). The flipped arm is the claim; the prefix is
    context. A term containing `(let …)` skips the undeclared-token check
    (renaming still happens), because its bound names are not free symbols.
11. **Clock roots never enter `rootAssignments`.** A replay does not set a
    clock; clock freedom is the composition's question.
12. **CLI flags beyond the mandate**: `--z3`, `--solver-timeout-ms`,
    `--max-tasks`, `--max-obligations-per-task`, `--solver-threads`. All have
    defaults; the mandated five are unchanged.
13. **`seedSessionId`** is the first session, in the layout's order, that
    activated the occurrence.
14. `ExploreMain` never exits non-zero for a recorded exploration outcome; the
    state is in the manifest (`PENDING_RESULTS` / `FIXED_POINT` / `MAX_WAVES`),
    so `run_engine` reads a value rather than an exit code.

## 6. For the integrator

* Merge order: this branch after `refactor/d3-compose`, then `git rm
  src/main/java/edu/uva/liftlab/graphchecker/d3/compose/SmtLowering.java`
  (commit `5c6d23048`'s whole content) and rebuild.
* Nothing in `concolic/` is edited, so step D's deletions do not conflict with
  this branch.
* `run_engine.sh` is not touched; the EXPLORE stage wiring is M5's.

---

## 7. Follow-up — contract v1.1, the composer's lowering, the M5 stage

**Tip `3a9fdb89d`** — "d3.explore on contract v1.1 and the M5 stage: plan a
wave, solve one obligation", over merges of `refactor/d3-contract-pkg`
@`6f741ef79` (v1.1) and staging `refactor/flatten-handoff-next` @`6d47ed98f`
(D + M5 + `d3.compose` @`317983a23`). `mvn -o test` **73 tests, 0 failures**
(cap 80); `mvn -o -q -DskipTests package` clean. Main is now 2 690 lines over
12 classes; the test is 517 lines, still 5 @Test.

### 7.1 The placeholder is gone

`d3.compose.SmtLowering` from M4 serves the three call sites verbatim —
`SmtLowering.of(ExpressionTable)` and `lower(ref) → Lowered{ok, text, refusal,
declarations}` — so the merge resolved the add/add conflict in the composer's
favour and **nothing of commit `5c6d23048` survives in the tree** (`grep
PLACEHOLDER` = 0). `SessionReader.lowering()` is the one place that constructs
it, exactly as before. No call site changed: the difference to report is that
there is none.

`d3/explore` imports nothing outside `d3.*` (checked), so D2's deletion of
`HandoffFamilyRows`, `BranchReplayContract`, `ConcolicPathFlip*` and
`ConcolicConstraintSolver` cannot reach it — the composer moved the lowering
core out of `concolic/` too, and `SmtLowering` no longer imports that package
either.

### 7.2 The three v1.1 follow-ups

| deviation (§5) | now |
|---|---|
| **2** `π_q` was the producer occurrence's whole recorded path | cut at the export: `decision.seq() >= export.seq()` is dropped. A decision the producer took after putting the value on the wire is no condition of that delivery. |
| **5** sorts inferred from the recorded value | `SmtText.sortOfJavaType(javaType)`: `Z/boolean → Bool`, `B C S I J` (and their names) `→ Int`, **anything else refuses the obligation** (`UNSTATED_VALUE`, blocking, naming the symbol and the descriptor) rather than being lowered as an integer. Roots keep the kind rule (`MARKER → Bool`), since `RootMintRow` carries no descriptor. |
| **4** a solver timeout had no gap kind | `GapKind.SOLVER_TIMEOUT`, diagnostic, with the budget in the detail; the verdict is `NOT_ADMITTED` (an unexplored sibling, never a closed UNSAT). |

The seq cut is asserted, not just implemented: the family test's rotated
session takes a decision `(> M_SERIAL 1000000)` **after** its export, with the
root pinned at 119995. Including it would make the arm unsatisfiable; the
obligation is SAT and answers 119995, so the cut is what the test measures.

### 7.3 Planning and solving are now two processes

M5 runs one JVM per wave and one worker per obligation, so the module split
along the same line:

* **`ExploreMain`** — one invocation is one wave. It reads every session the
  epoch has produced, rebuilds the frontier from the verdicts in `--results`,
  and writes the flips no wave has answered. It no longer solves anything and
  no longer loops.
* **`ObligationSolverMain`** (new, 188 lines) — one obligation by id out of the
  wave's file. It recovers the task from the corpus (`ClosurePlanner.taskOf`: a
  task id is its focused occurrence's id, so no second file can disagree),
  builds the query, solves it, and writes the verdict row, the completed
  obligation, the query and — only when satisfiable — the replay's task plan.
* **`ObligationFactory`** — `candidates(...)` (planning, no solver) and
  `solve(...)` (one query, one verdict). The in-process thread pool is gone:
  parallelism is the campaign's, one worker per obligation.
* **`Frontier`** — rebuilt from the recorded verdicts each wave; `NOT_ADMITTED`
  still closes one query and never another task's.

## 8. Mismatches with run_engine's EXPLORE stage, and what I did about them

Measured against `refactor/flatten-handoff-next` @`6d47ed98f`
(`campaign_explore`, `campaign_obligation_worker`), with both entry points run
under the stage's exact flags on a synthetic corpus
(`SPN/d-explore-m3/smoke`).

**Adapted on my side (no shell change):**

1. **`--sessions`, not `--iteration`.** Accepted; the iteration is its parent.
   `--iteration` still works for direct use.
2. **No `--target-occurrence` is passed.** The closure's roots are the
   `occurrenceId` of every row of `--task-plan`
   (`<iteration>/seed-replay/execution_task_plan.jsonl`), parsed in the v1
   spelling the plans are written in; `--target-occurrence` is still accepted
   and adds a root. A root no session activated is published as an
   `ADMISSION_GAP` naming it, because a closure that is empty because its root
   was never recorded must not read as a closure with nothing in it.
3. **`--results` is the accumulated verdict file**, not per-wave state: the
   frontier is rebuilt from it at every wave, which is also what makes the
   stage's own signature fixed point meaningful.
4. **One wave per invocation** (`--wave N`, `--output-dir <wave dir>`), files
   named as the stage reads them: `obligations.jsonl` in the wave directory.
5. **A closed frontier would have failed the stage.** `require_nonempty "wave
   obligations"` dies on an empty file, and the loop's `pending > 0` test is
   only reached after it. The wave now writes a single marker row
   `{"kind":"EXPLORE_FIXED_POINT","obligationId":"", …}`: `require_nonempty`
   passes, the stage's `[[ -n "${obligation_id}" ]] || continue` skips it,
   `pending` stays 0 and the loop breaks cleanly. Verified against the stage's
   own `jq`. (If you would rather the shell said this, the one-line form is
   `[[ -s "${obligations}" ]] || break`; the marker is compatible with both.)
6. **The worker is given no `--root-domains`.** Without the case's declaration
   every root with no runtime-published domain is pinned, and no rotation could
   ever be explored — the defect REPORT-PRODUCIBLE §7 is about, arriving by a
   different road. `ExploreMain` therefore writes `root-domains.jsonl` into the
   wave directory, and `ObligationSolverMain` defaults to the one beside its
   `--obligations` file. An explicit `--root-domains` still wins.
7. **`--clock-skew-ms` is accepted and not honoured.** A clock has no window in
   Design 3 — unbounded, `>= 0` floor only, per path — so there is nothing for
   a skew to do here. The composer still takes it for its own reasons.

**Still owed by the runtime side (M2), stated rather than guessed:**

8. **`execution_task_plan.jsonl` is written in the obligation's own shape**:
   one row with `taskId` (what `campaign_task_ids` reads), `obligationId`,
   `pathId`, `flip{siteId, ordinal, outcome}`, `rootAssignments`, `answers`,
   `unproducible`. Everything the replay must apply is in it under contract
   names, but the *field names the replay decodes* are M2's, not mine: if the
   focused-replay mode expects another spelling, that mapping is one method in
   `ObligationSolverMain.replayTask` and it should be written where the runtime
   states it, not guessed here.
9. **The verdict a worker writes is never `VALIDATED`** — the stage sets that
   itself after the replay lands, which is right: the solver cannot know that a
   replay ran. The worker writes `SAT_MODEL_READY`, `UNSAT` or `NOT_ADMITTED`,
   and the row carries `schemaVersion`/`kind` exactly as the stage's own
   failure path writes them.
10. **`ObligationResult.sessionId` is empty from the worker**, for the same
    reason; the stage fills it from the replay's session.

### 8.1 Contract v1.2 (`RootMintRow.seq`)

Tip **`ab9646dc4`** — "d3.explore: contract v1.2 RootMintRow seq", over the merge
of staging `34ccdc1a6`. `mvn -o test` 73 tests, 0 failures. One call site, the
test fixture: a root is minted at the next event of its session's own order,
before every decision that can mention it. The module reads no mint seq — a
root is one quantity of the corpus, and which event minted it is a fact about
the session, not about the variable — so nothing else moved.

**Gate, unchanged from §4:** the M3 gate on 17897 and bug3 still needs M2's
recordings in the contract's shape. Both entry points now run under the
stage's exact flags, so the gate is `campaign_explore` itself the moment those
sessions exist.

### 8.2 Readiness for identity v3 / contract v2.0 (survey, no code changed)

IDENTITY-V3 read at `SPN/d-design/IDENTITY-V3.md`. Measured against tip
`ab9646dc4`, `d3.explore` asks an address for three things only —
`occurrence().id()` (5 sites, all index keys), `focused().render()` (2, both
manifest text) and `node().render()` (2, the state-connected key) — so the
correspondence rule "same iff the ids are equal" is already the only rule the
module applies. The adaptation is therefore:

| site | change |
|---|---|
| `ExploreMain.anchors(...)` (2 calls to `OccurrenceAddress.parse`) | the ONLY non-mechanical one: a `--task-plan` `occurrenceId` in the v1 spelling becomes `parseSelector` + resolution against the seed session (region equal, Anchor context's `rpcSite` api equal when given, k-th match in seed order). A selector that resolves to nothing keeps its `ADMISSION_GAP` naming it; a selector that resolves to more than the k-th match is not an ambiguity, it is the k-th. |
| `FlipQuery` variable names (2 uses of `endpoint().ordinal()`) | a short digest of the `siteIndex`; names are cosmetic, the keys are `endpoint().id()`. |
| `Corpus.touching(...)` (`node().render()`) | unchanged — `NodeId` stays. |
| `D3ExploreTest` fixtures (7 `parse` + 6 `Endpoint.of`) | build addresses directly: `Root(CLIENT, 0)` / `Anchor(producerEndpointId, rpcSite)` contexts and explicit `ExecutionIndex` frames, plus `LocationId.allocated(...)` for the container. |
| the state join | unchanged: §5 pairs a writer and a reader endpoint by the version WITHIN a run, which is exactly what `Corpus.writeOf(sessionId, location, version)` does. Cross-run alignment by canonical endpoints is the composer's. |

Nothing in `ClosurePlanner`, `Frontier`, `ObligationFactory`,
`ObligationSolverMain` or `ExploreCodec` touches the shape of an address.

### 8.3 D2 + the M5 follow-ups — both workarounds retired

Tip **`8a8b7b8c8`** — "d3.explore: the empty wave is the stop, and the worker is
told the domains", over the merge of staging `0972ea9a7` (D2, −26,609 lines,
and the M5 follow-ups). `mvn -o test` **47 tests, 0 failures** (D2 deleted the
superseded concolic tests with their classes; d3 is 5 explore + 9 compose + 4
contract). §8 items 5 and 6 are now the shell's:

| was (my side) | is (stated by the stage) |
|---|---|
| a blank-id `EXPLORE_FIXED_POINT` marker row, so `require_nonempty` would pass | an EMPTY obligations file, which the stage breaks its loop on (`[[ -s ... ]] || break`) — the marker row and its reader are deleted |
| `root-domains.jsonl` written into every wave directory, the worker defaulting to it | the stage passes `--root-domains` to `ObligationSolverMain` — the sidecar write and the default are deleted, so one declaration is stated once and cannot go stale in a wave directory |

`--target-occurrence` is now passed to `ExploreMain`; it already merged a
declared anchor with the plan's own occurrences, so nothing moved there.
Verified on the smoke corpus under the stage's exact flags: a closed frontier
writes a 0-byte `obligations.jsonl` and the manifest still says `FIXED_POINT`.

### 8.4 Identity v3 (contract v2.0/v2.1) — done

Tip **`5ecf60789`**, over `270799c97` ("d3.explore on identity v3") and the
merge `c700b2f00` of staging `c360ae6e8` (contract v2.1 + the composer's v3
work). `mvn -o test` **48 tests, 0 failures**; 5 @Test in `D3ExploreTest`,
unchanged in number.

The survey in §8.2 held: the module needed three changes and no more, because
every other line already worked on ids and equality.

1. **Selectors are resolved, in one place.** `ExploreMain` parses a case's v1
   spelling with `parseSelector` and resolves it against the SEED session —
   node, region, the api when one is given, k-th match in that session's own
   activation order. The `--task-plan` occurrenceIds go through the same path,
   and one that is already a resolved id (it carries `/ctx:`) is parsed as an
   id rather than refused. A selector nothing matches is a BLOCKING
   `ADMISSION_GAP` naming it **and what that region ran as in the seed**,
   because the reason is nearly always a spelling the case and the deployment
   do not share.
2. **The api rule is the composer's verbatim** — last path segment, or exact,
   answering the contract with the selector's own spelling when the two name
   one api. One declaration must elect one occurrence in EXPLORE and in
   COMPOSE; two conventions would eventually elect two. (My first version
   offered the contract several candidate spellings; it is gone.)
3. **`Corpus.seedSessionId()`** reads the seed as the composer does: the
   session that focused nothing is the recording. A corpus of flips alone
   resolves against every session in order and says which in the refusal.
4. **The cross-check ruling is implemented** in `ClosurePlanner.producers`:
   the attach ROW stays the authority, and a disagreement with the consumer's
   `Anchor` context is a DIAGNOSTIC `TOPOLOGY_DIVERGENCE` naming both endpoint
   ids. `Root` and `Lost` contexts raise nothing. Test 5 asserts both
   directions — silent when they agree, named when they do not, with the
   closure still following the row.

Fixtures are v3 identities rather than parsed strings (a `KEY_MANAGER_TICK`
root for the rotation, a `DATA_XCEIVER` root for the fatal read, an `Anchor`
context for addKeys whose producer endpoint id IS the rotation's export, the
map owned by its allocation endpoint per Memory Indexing) and the seed session
focuses nothing, which is what makes it the seed. The staging merge conflicted
on `D3ExploreTest`, where the composer had given it the mechanical treatment;
resolved in favour of these identities, since the closure and cross-check cases
are about the Anchor context the mechanical version does not have.

**Coordinator ruling (2026-09-15), implemented in §8.4 item 4.**
`AttachRow.producer` stays the closure's authority — it is the pairing the run
recorded — and the consumer occurrence's `CausalContext.Anchor` is a
cross-check, not a second source. One place: `ClosurePlanner.producers(...)`,
where the attach is already in hand. When the attach's producer endpoint id and
the id inside the consumer's Anchor context differ, the closure still follows
the ROW, and a DIAGNOSTIC `TOPOLOGY_DIVERGENCE` gap names both
(`subject` = the consumer endpoint, `detail` = "recorded pairing <producer
endpoint id> vs causal anchor <anchor producer endpoint id>"): two statements
about one interaction that do not agree is exactly what a reader must be told,
and it is the runtime's bug to fix rather than this stage's to arbitrate. A
`Root` or `Lost` context raises nothing — there is no anchor to disagree with,
and an unpaired attach already publishes `LINEAGE_LOST`.

## 9. R-I6 slots — design, pending the single SessionReader

Read at INTERACTION-ID §6. Not implemented yet: the coordinator's ordering is
to adapt to the composer's consolidated `SessionReader` first, and at
`refactor/d3-compose` @`59fa99aa5` that consolidation has not landed (both
`d3/compose/SessionReader.java` and `d3/explore/SessionReader.java` are still
there). The plan, so the implementation is one pass when it does:

**Where it lives.** A new `SlotTable` in `d3.explore`, persisted as
`<iteration>/slots.jsonl` — one row per slot: interaction id, producer
endpoint, consumer endpoint, opened-by session, opened-at wave. `ExploreMain`
reconciles it at the start of every wave, before the closure is planned, since
a slot opened by the last wave's replays is what the next wave's tasks are cut
from. `ExploreCodec` gets the row's read/write pair (the contract states no
slot type; the coordinator gave the fields).

**The four cases, as R-I6 states them.**

| the replay states | the table does | what is published |
|---|---|---|
| an interaction whose consumer is a closure member, pair not in the table | OPENS a slot; the arm is its first | the slot row, `openedBy` = that session |
| the same pair again, any replay, any wave | falls into the slot; arms accumulate | nothing — this is the normal case |
| an interaction outside the closure | nothing | a DIAGNOSTIC gap, recorded and no more |
| a consumer endpoint already in a slot paired with a DIFFERENT producer endpoint, or a closure member whose `CausalContext` changed | neither grows nor fills — it contradicts | BLOCKING `TOPOLOGY_DIVERGENCE`; the campaign opens the epoch, this stage does not fork anything, and the old table stays |

**Two things worth stating before I write it.**

1. *The producer-as-task half already works.* `ClosurePlanner` walks
   `AttachRow.producer` for every attach on a closure member, so a
   newly-opened slot's producer is already listed as a task in the same wave
   it is discovered. The slot table makes that explicit, persistent and
   auditable across waves; it does not change which tasks exist.
2. *"A closure member whose CausalContext changed" needs a weaker key than the
   id*, because the context IS in the id — an occurrence with a changed
   context is a different id, so nothing would ever match. The detection is
   therefore: a replay occurrence equal to a closure member on (node, region,
   execution index) but carrying a different `CausalContext`. That is the
   contradiction the rule means, and it is the only reading under which the
   check can fire at all. Flagging it rather than deciding it silently.

The test folds into `D3ExploreTest` as one @Test with the three cases (open /
fill / replace), keeping the class at 5 by merging the closure case into it —
the closure case is about which occurrences a slot's producer becomes, which
is the same fixture.

## 10. Slots, HB-concurrent state joins, one arm builder — done

Tip **`71e9d8bb2`** (the pass is `ab9646dc4..71e9d8bb2`; its work landed in
four `wip:` commits between the staging merges it had to keep up with).
Staging merged at `8300e453c`. `mvn -o test` **56 tests, 0 failures**; 5
@Test in `D3ExploreTest`.

### 10.1 What the pass did

| asked | done |
|---|---|
| adopt the single `d3.contract.SessionReader` | `d3/explore/SessionReader.java` deleted; `Corpus` holds the contract's reader and one `SmtLowering.forSession` per session |
| adopt `d3.smt.Arms`, delete my arm/guard code | `Corpus implements Arms.Rows` (11 methods); `FlipQuery` builds wire families with `wireArms` and state alternatives with `stateArms`; my `StateEligibility` is deleted |
| anchors through `d3.plan.SelectorResolution` | delegated; what is left here is the refusal — an unresolved selector is a BLOCKING `ADMISSION_GAP` naming it and what the seed ran that region as |
| R-I6 slots | `SlotTable` writes `<iteration>/slots.jsonl` in the shape `d3.compose.SlotTable` reads; open / fill / outside / replace, reconciled per wave |
| R-I7.1 in `FlipQuery` | one Bool selector per eligible writer occurrence, exactly-one, every read of that location in the reading occurrence bound under the same selectors (the block rule); the eligible set published per read as a DIAGNOSTIC row |
| F1 | a declared domain resolves against the OBLIGATION's own session, explicitly |
| F2 | the closure follows only the interactions the admitted paths read, asked of the state-connected group; `--max-tasks` truncation is BLOCKING |
| test | the slot cases (open / fill / replace) fold into the closure test; still 5 @Test |

### 10.2 Two things the coordinator should rule on

1. **`DecisionRow.term` and `outcome` are read two ways.** `Arms.arm(...)`
   puts `decision.term()` into π verbatim, and the composer asserts π the same
   way; this stage's own prefix asserts `outcome ? term : (not term)` and its
   flip asserts the complement. Both cannot be right. If `term` is the
   predicate (which is what the contract comment and the presence of a
   separate `outcome` field say), then every arm's π currently loses the arm
   its producer took — a family arm that should hold under `¬p` holds under
   `p`. If `term` is published already in the taken polarity, then `outcome`
   is redundant and my prefix double-applies it. It is one line in each place
   once the runtime says which; M2 has not published a decision row yet, so
   nothing measures it today. **This is the one open soundness question in
   this package.**
2. **`Arms` does not expose the DIRECTION of a causal order.** `concurrent(…)`
   answers "neither before nor after", which is what eligibility needs, but a
   STATE replacement needs "the reader caused the writer" specifically.
   `SlotTable.caused(…)` walks the anchor chain locally for that one test,
   with a comment saying so; it belongs beside `Arms.ancestor` and should move
   there when that is exposed.

### 10.2.1 Both rulings adopted — tip `7fbb3f44b`

Staging `5e36713b2` merged. `mvn -o test` **57 tests, 0 failures**.

* **The decision polarity is one routine now.** `Arms.conjunct(decision)` is
  `outcome ? term : (not term)`, and `Arms.pathCondition(decisions, before)`
  builds a producer prefix with it, so a family arm's π and an obligation's
  prefix mean the same thing. The obligation's prefix calls it and renames the
  result — the polarity is the recording's, the names are this query's — and
  the flip is that conjunct's complement. §10.2 item 1 is closed by the rule
  moving into one place rather than by either side yielding; my reading was
  the one that survived, and the arms that were losing their producer's arm
  now carry it.
* **Causal direction is `Arms.ancestor(a, b, session)`** — same-thread seq
  inside one occurrence, the anchor chain across them, unknown false.
  `SlotTable`'s local walk is deleted and the STATE replacement test is
  literally the question it meant: did the READ happen before the write it
  claims to have observed. §10.2 item 2 closed.

### 10.2.2 Outside the closure (INTERACTION-ID §8) — tip `4830bf9c5`

`mvn -o test` 57 tests, 0 failures.

* **Case 1 already held.** The closure is recomputed from the anchor over ALL
  accumulated sessions at every wave: `ExploreMain` re-reads the corpus and
  calls `ClosurePlanner.plan` per invocation, and nothing is carried between
  waves that could keep a region out. A flipped path reaching a region inside
  the instrumented set but outside the previous closure enters by that
  recomputation — its interactions open slots, its producers become tasks in
  the same wave, same epoch. Confirmed, not changed.
* **Case 2 added.** An activation of a region no session of this epoch
  published a detailed row for is TOPOLOGY_DIVERGENCE (BLOCKING) with detail
  `retained set must grow: <regionId>`. No endpoint of such a region exists,
  so no interaction can name it and no slot can open — the skeleton cannot
  absorb it and the epoch has to be re-cut with it instrumented.
  **The membership test is the row's own statement** since contract v2.3:
  `activation.instrumented() == false`. It was an epoch-wide inference ("no
  session published a detailed row for that occurrence") for one round, which
  could not separate a region that was never retained from one that was
  instrumented and had nothing to say all epoch — the first must fork the
  epoch and the second must not. `Corpus.detailed(...)` is deleted with it.
* **Case 3 needs nothing**: a region outside the static candidate graph
  publishes no activation at all.

### 10.2.3 Merge hygiene

Tip **`f8f10fa12`**: staging `fbe49c109` merged, `mvn -o test` 57 tests, 0
failures, staging an ancestor of the tip so the integrator gets a trivial
merge.

`e5da1e942` did not land because this branch had taken contract v2.3 from
`refactor/d3-contract-pkg` directly (`9186dd849`, the contract agent's amended
javadoc-only rewrite) while staging carried the original `f5c29c7ab`: two
commits with the same content and different identities, which is a conflict in
`ActivationRow.java` and in every file that moved with it. Resolved by taking
staging's `ActivationRow` verbatim and keeping this package's fixture
identities (the `instrumented` / `lightweight` rows the §8 case needs).

**Rule adopted: contract changes reach this branch through staging only.** A
package branch can be amended; staging is what every other branch has already
merged, so taking a contract from anywhere else makes this branch the only one
holding that version of it.

### 10.2.4 Thread order and start/join — tip `fa49968dd`

Staging `a29e5c8df` merged (Arms reads v2.3's `threadKey` and `startedBy`;
attestation is `instrumented ∧ (seed ∨ focused)`; `Rows.activationOf` /
`seedSessionId` were added to this package's `Corpus` by the composer).
`mvn -o test` **58 tests, 0 failures**.

**No logic changed here, and that was the point of asking the question in one
place.** `SlotTable`'s STATE replacement test is `Arms.ancestor(read, write,
session)` and `ClosurePlanner`'s eligible writers are `Arms.concurrent(...)`,
so both now see two orderings more than they did before — same-thread order
across occurrences, and a thread's starter before it — without either call
site knowing about them.

One comment was deleted because it had become false: "two activations of one
session interleave, so seq orders events only inside one of them" was true
while the rows carried no thread, and two activations on ONE thread are
ordered by the session's counter now that `threadKey` says which those are.
The javadoc names the four orderings a contradiction can rest on and states
that this stage keeps no fifth opinion about happens-before.

### 10.3 Notes

* `SmtLowering.forSession(session)` lowers with `symbolsDeclareThemselves`,
  so a `SymbolExpression` reports itself in `declarations()` — the flip query
  depends on that to find the symbols it must rename. A lowering built with
  `new SmtLowering(declaredSymbols)` instead refuses an undeclared symbol as a
  propagation cut; the two entry points are not interchangeable, which is
  worth knowing before someone switches them.
* The CLI smoke corpus under `SPN/d-explore-m3/smoke` is v1-shaped and was not
  regenerated for identity v3; both entry points are exercised end to end by
  the test instead (`ExploreMain.plan` per wave, `ObligationSolverMain.solve`
  per obligation, verdicts appended between waves).

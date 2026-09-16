# Cleanup round 2 + identity + the four verifications (2026-09-15)

One paragraph per mandate, in the order they were dispatched. Source: memory
`graphchecker-refactor-goal.md` (entries 2026-09-15 ~15:35 CDT to 22:05 CDT),
`cleanup2-rulings.md`, `case-11741-notes.md`. Timestamp caveat: log entries labelled
"2026-09-15 23:00" through "2026-09-16 02:40" are ~5 h too late (CDT/UTC confusion);
everything below happened on 2026-09-15. Staging = `refactor/flatten-handoff-next`, tip
**2126e1e47**; `/opt/GraphChecker` main is still **3d9355745** (nothing has landed on main).

Line count over the day: src/main 79,863 (before cleanup round 1) -> 73,457 (round 1,
a5ea1f2cf) -> 74,147 (morning, after closure v2 / P2h / VM glue) -> 68,836 (P-B, 9d2761c17)
-> **70,226** at 2126e1e47 (G7/G8/G9/C11-plan/W17960 added identity and gate code). 47 @Test.

**M4n / M4o — `refactor/one-notion-compose` (M4n bae7fa20c, M4o tip 7c1002066), merged into
staging 150efe5a1 and b36a855da.** Owner order "先把这些都删干净，只保留对我们有用的": one
implementation per notion on the compose/explore/smt side. M4n deleted `compose/CorpusIndex`
and `compose/SlotTable` (the explore ones are the only ones) and folded six duplicated SMT
helpers into one each. M4o made one z3 driver (a z3 `(error …)` becomes NOT_ADMITTED, never
UNSAT), one `contract/RootDomain` reader, one `exactlyOne` (`Arms`), one tokenizer
(`SmtLowering.names/rename`), one `primitiveDescriptor`/`normalize`, and deleted
`compose/JsonText` in favour of `smt/JsonFields`. Left for R2 (runtime-owned files): ArtifactIO
vs CanonicalJson sha256, a third `primitiveDescriptor` at CRR:5069, tolerant CLI aliases, two
name sanitizers, `legalSymbols` as a third tokenizer. Report `$MY/m4o/REPORT-M4O.md`.

**R1 — `refactor/runtime-cleanup2` (@645785bd5), merged -> staging 2fe8af5e5 (src/main 72,115).**
Runtime half of the cleanup-2 rulings (Q1/Q4/Q8 + envelope): the legacy
`CONCOLIC_REGION_RESULT` envelope is gone (rows are the only channel; an unanswered task is a
GapRow `TASK_UNANSWERED`), the second flip mechanism (plan-row `modelAssignments` /
`guardedReadAssignments` / ModelAssignment family / accessor call context) is gone — the focus
row is the one flip mechanism — `Verdict.DIVERGED`'s runtime producer and the `causynth.task`
FocusedReplay bundle are gone (divergence is EXPLORE's), and the VM demands
`armShared*`/`sharedFieldVersions` were dropped. R1 named its own losses for R2
(`configuredSourcePhaseGaps` unpublished; CLOCK-root focus assignment has no offset mechanism,
which 11741/17897 need; `FocusedReplay.observeInteraction` write-only; tolerated-mode replay has
no evidence gate). **R1's one regression**: it deleted the reflective JUnit-5 (jupiter) runner
path on a false "set by nothing" claim about `causynth.junit.ignore.timeout`, which every
`experiments/hadoop/*/execute.sh:40` passes — see R3.

**G2–G6 — `refactor/seed-identity` (G2 31ba47daf, G3 608c6ec18, G5 6a11648be, G6 ed42815bd),
merged -> staging 50561fc77 (src/main 72,413).** Four rounds to close the identity input table;
this is the sequence that produced the pass-equality rule in
`memory/identity-v3-execution-index.md`. G2: ONE address function `Identity.occurrence` for the
recorder and the replay (OccurrenceMinterV2, drift admission and the duplicate-activation abort
deleted, −590/+491) — but the recorder never minted Interactions/Endpoint, so target tasks were
skipped. G3: one Endpoint computation `Identity.endpointAt`; 159/826 recording addresses then
collided, because the recording opened a region frame at every skeleton root while the replay
opened one only at campaign tasks, and there was no siteIndex for the k-th send at a site.
G4/G5: lite region frames at all 80 skeleton roots (run_engine key
`causynth_region_skeletons`), siteIndex = k-th event at (occurrence, site) for sends and for
reads/writes, and every replay-only frame (accessor call context, loop-root, `State.loops`)
deleted; SEED gate met (826/823) but the replay leaked frames on recursive re-entry of a root
method. G6: the region ENTRY trio is woven once per skeleton root with a per-frame local token
(recursion-safe), plan-row hooks no longer touch the index stack, and `FRAME_UNBALANCED` became
a BLOCKING gap at activation close.

**P-A — `refactor/plan-cleanup2` (@1a2149f67), merged -> staging 7afdb14fd (src/main 70,145;
−2,002 lines; 47 @Test).** Stage A of the PLAN-side rulings: `GapLedger` deleted (rows carry
`GapKind` + `cls`; the 75 PLAN gap rows became DIAGNOSTIC, gapCount 74 -> 0), `ClockRootPhysics`
deleted (a cell declares `"clock": true` in symbolic-inputs.jsonl; 11741/17897/17899 configs
edited), `BranchWitness` reduced to φ, the `SharedExpressionTable` artifact half and the
ACTIVE_OBSERVED chain deleted, `MAX_LOOP_BODY_ITERATIONS=8` replaced by the declared key
`causynth_loop_default_bound`, unknown workflow keys refused, plus a long list of no-reader
members/artifacts. After it, src/main contains 0 `org.apache.hadoop` literals.

**P-B — `refactor/plan-cleanup3`, merged -> staging 9d2761c17 (src/main 68,836, the day's
low-water mark).** Stage B: ONE guard authority (`static_scope_map` /
`SiteControlDependence`, guards carry the required outcome for the TARGET_SITE, giving φ's
polarity), INSTRUMENT weaves every branch of the instrumented methods from the Soot bodies
instead of the plan's `branches[]`, the declared target per case is required
(TargetRank/edgeBindings/EdgeBindingCatalog deleted), and the offline path-planning cluster went
(ControlDependenceEdgeSupport, SeedBackwardStaticAnalyzer S9, finalizer C11, ConcolicScheduler
S8/S9/S16, the S10–S12 refusal taxonomy). **Partial on item 5**: `RuntimeRefinedGraphBuilder`
survives because `regionIds` (edgesByRegion scoping) and `runtimeAccessorBindings` (accessor
ports are 17960's only symbol) still depend on it -> the follow-up is **P-C** (ports static at
site level, occurrence binding from rows). Two latent bugs fell out: `--retain-regions`
parseArgs (every epoch after the first died) and `static_scope_map` missing from the seed cache
key (a cache HIT ran EXPLORE with an empty map).

**R2 — `refactor/runtime-cleanup3` (wt-r2), merged -> staging 0a51b56da (src/main 69,928).**
The items cleanup-2 deferred behind R1/G3: clock skew is applied at the manual mint
(`materializePrimitiveValue`), since a declared clock cell mints there; a refused mint is
BLOCKING; `primitiveDescriptor`'s one home is `JavaPrimitiveSmtSemantics`; Role became the
declared transport (`Root:IPC_HANDLER` -> `Root:HADOOP_IPC`, `Root:DATA_XCEIVER` ->
`Root:HDFS_SASL` in rendered addresses — the six declared target selectors are v1 selectors
without roles, so they did not change).

**G7 — `fix/region-entry-weave` (wt-g7), merged -> staging 8563092dc (src/main 69,155).**
From **verification #1** on 9d2761c17, which failed at REPLAY in 330 s with a JVM `VerifyError`
in the woven `FSNamesystem.allowSnapshot` @142 `lload_2` "Local index 2 is invalid": G6's region
entry token (a long local) is read in the woven catch-all whose trap range starts at bci 0,
before the store, so the handler's stackmap lacks the local. G7 opens the catch-all after its
prologue, applies the rule to every woven construct, validates every woven Soot body at weave
time, and adds a fail-closed `VerifyWovenClasses` gate in INSTRUMENT (15 of 18 campaign classes
were unverifiable on 9d2761c17). Note carried forward: `hdfs-17899` analysed by hand outside its
campaign dies in `WireFlowCatalog.fromConfiguration` ("capture method did not resolve:
PBHelperClient.convert(DataEncryptionKey)") on 9d2761c17 too — check when 17899 runs.

**R3 — `fix/one-test-runner` (@3a47c212c, wt-r3), merged -> staging 8a4f1809c.** From the 11741
seed on 8563092dc, which died at the workload launch with `ClassNotFoundException
org.junit.runner.Request`: all six workloads are JUnit 5 (jupiter) and R1 had deleted the only
runner that could run them (11741's classpath has JUnit 5.13.3 only; 17960's has junit-4 too,
which is why verification #2 still ran — JUnit 4's timeout runner happened to drive the jupiter
class). R3 restores ONE reflective runner over both vocabularies, deletes the JUnit 4 engine
path and the two `-Dcausynth.junit.*` switches from the four `execute.sh`, and makes the replay
state its exit instead of waiting for its threads. This produced the review rule now in
`subagent-rules-of-engagement.md`: a "no reader" claim is accepted only with the grep, and the
grep must cover `run_engine.sh`, all of `experiments/**`, `src/test/**`, and the hadoop trees'
`src`.

**G8 — `fix/endpoint-anchor` (@9357fb0ac, wt-g8), merged -> staging 4ed6bcd75.** From
**verification #2** on 8563092dc, which failed at REPLAY with 14 `TASK_UNANSWERED`
`OCCURRENCE_ANCHOR_UNMATCHED` where planned and ran differed ONLY in the causal anchor digest
(`Anchor:81d0aa0d…` vs `5cd4981c…` @HADOOP_IPC/checkpoint-namespace), index identical. The
differing input was the siteIndex k, counted **per thread**: a retried send during the NN
restart consumed a k and shifted every later anchor. G8 counts an event's k within the
occurrence's own events (dropped at close), states the producer endpoint components in EXCHANGE
rows and in planned-vs-ran refusals, uses the same counter for a region entry, emits one plan
row per occurrence, and makes residual shared addresses BLOCKING. The same class covered 11741's
PLAN failure (10 of 63 region-plan rows shared an id: `retrieveDataEncryptionKey` twice on each
of dn0/dn1, two activations under one SASL anchor whose distinct enclosing invocations are
untraced).

**G9 — `fix/work-starts-global` (@4448ac0ee, wt-g9), merged -> staging d551e81fc.** From 11741's
remaining 10 collisions: two balancer pool threads sending under one occurrence with no start
frame, because `Dispatcher.moveExecutor` submits outside the traced closure and PLAN wove 0
work-start sites. G9 weaves `START_WORK` at every thread-start/submit/fork site of the whole
application scope in **both** passes (`plan/WorkStartSites` is the one list; 11741 = 3 sites
including `Dispatcher.dispatchBlockMoves#u68`, 17960 = 15), counts starts with the one
occurrence×site counter, and has the recorder claim a task's start frame like the replay. It
also made the concolic pass write the whole case scope (18 -> 99 classes; 12 skeleton region
entries had been silently dropped).

**W17960 — `fix/refusal-names-the-frame` (@600990c9b; engine commits 87a201508 + 96bc26d6e),
merged -> staging 7d18b9f2a.** From **verification #3** on 4ed6bcd75: the first end-to-end run
on the cleaned tree (REPLAY -> IMPORT -> EXPLORE -> COMPOSE -> SOLVE -> DECIDE -> EMIT, 495 s)
but claim UNSAT_CLOSED / NO_SUPPORTED_WITNESS, 13 `TASK_UNANSWERED` at a uniform −1 shift of
`applyEditLogOp@k`, and a `DECLARATION_MISSING` BLOCKING that refused the second MARKER root.
G9's addendum verdict called it workload nondeterminism; that was **corrected**: the −1 shift is
an engine defect of G6's pairing class — the replay popped the identity REGION stack at three
places (`closeRegionEntry` paired; `popActiveRegion` CRR:4495 and the `else if
(identityRegionEntered)` path :726 unpaired) and `regionExit` wipes the closed occurrence's
per-site counters, so `applyEditLogOp` restarted at k=0 mid-loop (first entry stranded, rest
shifted −1) and `loadEditRecords` fell to the role occurrence (the LINEAGE_LOST row). The
frame-depth check could not see it: region stack ≠ frame stack. W17960 landed one push / one pop,
put the region-depth check under `FRAME_UNBALANCED`, and made a planned-vs-ran refusal name the
differing component first. The 17960 workload determinism edits
(`$SPN/d-runtime/workload/hdfs-17960-deterministic-edits.diff`, tree rebuilt in 4m30s, test
passes) were kept as case prep — see `memory/case-prep-determinism.md`.

**C11-prep — /opt/hadoop-hdfs-11741 workload edits (no engine branch), done 18:03 CDT.** Diff
`$SPN/d-runtime/workload/hdfs-11741-bpserviceactor.diff`, 3 files: DataNode
`causynthSourceAnchor` accessors; `TestCausynthExpiredBalancerKey` sets it after
`registerSource` and before `startRecording`; `BPServiceActor.offerService`/lifeline turns
become `endInbound -> beginTick -> beginRequest(anchor,"offer-service") … endRequest ->
endTick`; `CommandProcessingThread` carries the enqueuing turn's scope via `captureScope` /
`enterCarriedScope`. Reason (from G3): the DNs' BPServiceActor heartbeat threads start before
`startRecording` and none of their methods is traced, so their activations were addressed
`workload/unregistered#epoch0` and dn0/dn1 collided. The tree was rebuilt with the staging jar
(295 s, workload test passes); the trace now shows
`hdfs-11741/dn0|dn1#epoch0/request/offer-service#k` per turn and every heartbeat exchange
carries the DN source key. Remaining hole, left deliberately: `processQueueMessages()`
error/bad-block RPCs are outside the tick.

**C11-plan — `fix/declared-input-regions` (@cf8db5753), merged -> staging ba81b890a (src/main
~70.0K).** From the 11741 seed on d551e81fc, where PLAN refused with "symbolic input selection
names a static site no planned region covers: `<BlockTokenSecretManager: void
removeExpiredKeys()>`". Ruling: a declared symbolic input's method is a region root **by
declaration** at all four P1 points (static slice, skeleton weave, runtime selection, plan
closure); `plan/DeclaredSymbolicInputs` is the one reader, with refusals
DECLARED_INPUT_UNRESOLVED / OUTSIDE_STATIC_SLICE / NEVER_ACTIVATED / NOT_PLANNED. PLAN owns no
slice any more: `RuntimeWorkflowDiscovery.topologyScope`'s backward walk over observed edges is
deleted and every READY planned occurrence is a seed task, target first (11741 57 -> 65 tasks
including 6 `removeExpiredKeys`; 17960 45 = 45).

**Verification #4 on 7d18b9f2a — hdfs-17960 PASS.** `hdfs-17960: PASS`, claim SAT_CANDIDATE,
findingKind MARKER_FLIPPED at valuation 1 (`HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED=false`),
polarityDecides, FINAL_READY, 0 blockers, 5 gaps, 880 s. Seed: 90 activations / 66 writes / 39
reads / 2 roots / 2 targets; wave 0 = 4 obligations, wave 1 = fixed point; IMPORT gate reported
16 LINEAGE_LOST as diagnostic. Chain, from the artifact commit 2126e1e47: ordered=false ->
unordered `deleteSnapshot#u7` -> the snapshot list keeps 1 element while numSnapshots =
0+1+1−1−1 = 0 -> the serializer writes 1 and reads 0 -> `1 != numSnapshots` fatal at
`serializeSnapshotSection#u61`; the ordered arm (list 2, counter 2) is contradictory; z3 flipped
sat, recorded unsat. Corpus `$MY/final-7d18b9f2a`, log `$MY/verify-7d18b9f2a.log`.

**F17960 — `fix/one-symbol-per-source` (wt-f17960, IN FLIGHT, no commits yet).** The six
follow-ups the artifact review named in 2126e1e47's `gaps.json`: (1) the configured-source phase
catalog's size/ordinal limit — one root symbol per declared source, every read binds to it
(DECLARATION_MISSING ×2 on `isSnapshotDeletionOrdered#u1` occurrence 2); (2)
`OCCURRENCE_ADDRESS_SHARED` rows state `cls`: BLOCKING iff the region is a closure member
(static_scope_map site or target region), else DIAGNOSTIC (the InitQuotaTask ForkJoin triple has
an unweavable JDK fork site); (3) drop dead declarations (`unsupported__`, cut-session reads);
(4) the `PROPAGATION_CUT` `UndeclaredFreeSymbol` on the second `#u7` flip path, where a session's
path rests on another occurrence's input symbol; (5) 42 LINEAGE_LOST rows (Lost:UNKNOWN,
activation −1) toward the 0-Lost gate; (6) `probe_final.sh` reads `manifest.booleanRoots`, which
no longer exists (hence `buggy=NO_ROOT other=NO_ROOT` in the summary) — a harness field rename.

**C11-replay — `fix/11741-replay-hang` (wt-c11r, IN FLIGHT, no commits yet).** The 11741 seed on
7d18b9f2a (lane `$MY/lane11741d`) got further than ever: SEED aggregated (65 plans, 0 duplicate
ids), PLAN with declared roots as regions passed and INSTRUMENT passed (72 bodies, verifier 0
rejections, guard table installed 5/7) — first time for both. Then the concolic seed REPLAY
**hung for 51 min**: the cluster came up with 2 DNs, then only `Problem connecting to server
localhost:36449` ×1517 from the DN heartbeat threads; a `kill -3` dump showed main parked in
`Client.call` -> `getDatanodeReport` (the NN RPC was never answered). The same workload finishes
in the recording pass and on the plain build. This is the first exercise of the wire path
(communication-mappings) since the cleanup. The lane was killed by pgid; the mandate may rerun
the replay with a timeout and dumps.

---

**Continued in `REPORT-2026-09-16-VERIFICATION.md`** (2026-09-15 17:35 → 2026-09-16 06:50 CDT): the
seven verification rounds and what each caught, the hdfs-17960 CLEAN PASS on 6f6f88ec6
(verification #7, artifacts at staging 089a36aad), the per-case harness gate, HDFS-11741 from
workload prep through campaign #2 to the open X15, the named residue, and the corpora kept.

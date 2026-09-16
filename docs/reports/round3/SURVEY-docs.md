# Documentation survey — cleanup round 3

Tree surveyed: worktree `r3/DOC1` @ `48dece245`; every "no longer exists" claim was grepped
at the **current staging tip** `refactor/flatten-handoff-next` @ `6754d3951` over `src/main`,
`run_engine.sh`, `experiments/**`. Counts are `grep -rn -F` hits there. No doc was edited.

## The whole doc set

| File | lines | Verdict |
| --- | --- | --- |
| `README.md` | 223 | REWRITE (superseded by `$MY/readme-draft/README.md`; 5 stale sections) |
| `docs/CONCOLIC_INTEGRATION.md` | 815 | REWRITE — ~40% DELETE (whole "Reading the formula", blocker table, gap-ledger sections) |
| `experiments/hadoop/hdfs-11741/README.md` | 78 | REWRITE (GuardedRead paragraph; scratchpad lane names) |
| `experiments/hadoop/hdfs-17897/README.md` | 99 | REWRITE ("Clock window" section DELETE; GuardedRead/closure-wide paragraph) |
| `experiments/hadoop/hdfs-17899/README.md` | 77 | REWRITE (closure-wide merging + GuardedRead paragraph) |
| `experiments/hadoop/hdfs-17960/README.md` | 115 | REWRITE (2 dead classes/artifacts, 1 false z3 claim) |
| `third_party/OpenJDK-Concolic-Execution-Engine/README.md`, `README`, `README-builds.html`, and `{corba,hotspot,jaxp,jaxws,jdk,langtools,nashorn}/README` | vendored | KEEP — upstream OpenJDK text plus the VM build/smoke instructions the root README and the draft both link to. Not ours to rewrite. |

No other `*.md` exists outside `src/test/resources` and `.git`; `docs/` holds exactly one file.

## Nouns that no longer exist at the staging tip

0 hits in `src/main` + `run_engine.sh` + `experiments/**`: `GapLedger`, `gap_ledger.json`,
`RefinedFlowIndex`, `EdgeBindingCatalog`, `ModelAssignment`, `GuardedReadAssignment`,
`CONCOLIC_REGION_RESULT`, `consumerOccurrenceIds`, `causynth.trace.max.events`,
`target cutoff`, `z3-result.json`, `fatalStateSelection`, `mechanismNecessity`,
`existentialRootProbe`, `RootValuationSolver`, `witnessMechanisms`, `existentialWitness`,
`pinnedCaseSelectors`, `skewMillis`, `evidenceOnly`, `CANDIDATE_WITH_GAPS`,
`failClosedMarkersLifted`, `BooleanReachConditionExtractor`,
`DEGENERATE_UNCONSTRAINED_ROOT_SPACE`, `guardedReadModel`, `symbolicPropagationGaps`,
`fatalSite`, `merged_boundary__`, `rf_value__`, `fatal_path`, `recordedRootValues`,
`wallClock`, `ClockRootPhysics`, `region_path_manifest`, `region_path_worklist`, `RegionPathWorklist`,
`replay_task_slice`, `ReplayTaskSlice`, `keptOccurrenceCount`, `symbolic_root_policy`, `DeadCaseLemmas`, `--dead-case-rlimit`, `wireFlowBindings`,
`guarded_read_order__`, `GUARDED_READ_ORDER_UNKNOWN`, `caseSelectorPartitions`,
`request_fault_control__`, `structural_ref`, `untrackedElementWitnesses`,
`CONSUMER_BOUNDARY_FAMILY_CYCLE`, `boundaryDepth`, `PATH_FLIP_SOLVER_TIMEOUT`, and all eleven
blocker codes of `docs/CONCOLIC_INTEGRATION.md`'s table (`COMPOSER_NOT_FINAL_READY`,
`COMPOSITION_GAPS_UNRESOLVED`, `DECLARED_WIRE_FLOWS_UNREALIZED`,
`UNDETERMINED_INITIAL_STATE`, `FAULT_MARKER_NOT_DETERMINING`,
`TARGET_UNCONSTRAINED_BY_ROOTS`, `WITNESS_UNINFORMATIVE`, `SOLVER_UNDECIDED_VALUATIONS`,
`UNSAT_CLOSURE_INCOMPLETE`, `NO_EXACT_REACHABILITY`, `COMPOSED_BODY_UNSATISFIABLE`).

Still alive, so NOT stale: `carrier` (173), `refined graph` / `RuntimeRefinedGraphBuilder`
(11/9), `refined_dataflow_edges` (run_engine.sh:363), `GuardedRead` (3, comments only),
`AssocState` (20), `IndexedState` (17), `ContainerSmtCodec` (70), `ConcolicScheduler` (19),
`--closure-mode` (4), `attachCommunicationLeaf` (5), `admissionBasis` (6),
`SHARED_LOCATION_DEMAND_V1` (2), `campaign_stop_after` (6), `region_path_max_waves` (4),
`solver_timeout_ms` (8), `frozen-inputs` (2), clock floor `>= 0` (FlipQuery.java:41,
Composer.java:1866), and the whole claim/finding vocabulary the harness gates on
(`findingKind`, `polarityDecides`, `valuationOrdinal`, `movedRoots`, `witnessFindings`,
`gapCount` — run_engine.sh:2600-2658). `edgeBindings` survives only as javadoc prose in
`plan/RuntimeWorkflowDiscovery.java:40,50`; no row publishes it.

## Per file

### `README.md` — REWRITE
Stale sections: (1) the Toolchain block's plan line; (2) `schedule_max_jobs`;
(3) the `region_path_max_waves` paragraph's fixed-point evidence; (4) the
`solver_timeout_ms` gap code; (5) the Results artifact list.
> line 19: "-> immutable linked region-path plan"
> line 103: "members of one linked replay bundle always run in one JVM, so this bounds
> concurrent bundles, not concurrent regions."
Linked replay is retired: `runtime/FocusedReplay.java:28` — "This is what replaces linked
replay." Line 109 cites `region_path_manifest.json` `state=CLOSED` (0 hits); line 98 cites
`PATH_FLIP_SOLVER_TIMEOUT` (0 hits; the surviving codes are `REGION_PATH_CLOSURE_NO_PROGRESS`
and `REGION_PATH_WAVE_BUDGET_REACHED`, 1 hit each). Line 183 lists `gap_ledger.json` as a
published artifact; EMIT's required set is `candidate.smt2 candidate_composition_manifest.json
gaps.json result.json` (run_engine.sh:2382-2383) and `claim.json` beside them
(`compose/ComposeMain.java:113`) — the list names a file nothing writes and omits the one
the draft calls a deliverable. Accurate and worth keeping: the two-pass tracing paragraph
(run_engine.sh:682-712), `campaign_stop_after`, the package list.

### `docs/CONCOLIC_INTEGRATION.md` — REWRITE, most of three sections DELETE
DELETE: "Reading the formula" (lines 622-670) — every artifact it documents is gone.
> line 655: "**`fatalStateSelection`.** The arms of the fatal predicate's own guarded read,
> with the one the model chose marked. The `fatal_path` assertion names one
> `merged_boundary__` constant..."
DELETE: the ClaimPolicy CLI snippet (line 677) — the class is
`compose/ClaimPolicy.java`, not `...concolic.ClaimPolicy`, and it has no `main`.
DELETE: the 11-row blocker table (lines 683-696) and "The gap ledger" (lines 715-775).
> line 719: "Every gap code the pipeline can publish is registered in one place,
> `contract/GapLedger.java`, with an explicit class"
The registry is now `contract/GapKind.java` (218 hits), which carries BLOCKING/DIAGNOSTIC per
kind in javadoc; no `gap_ledger.json` is published (line 734 says it is).
REWRITE: "The replay task set" (lines 264-320, `ReplayTaskSlice`/`replay_task_slice.jsonl`
gone), "Replay waves" tail (lines 483-493, worklist/manifest files gone), the `Result contract`
row list (line 500, `edgeBindings`), "Dead case arms" (line 548), "Wire flows" (line 610),
the `guarded_read_order__` paragraph (line 407), and line 87's linked-replay bundle.
KEEP: the declaration-file table, `symbolic-inputs.jsonl` semantics, the container lowering
paragraph, `--closure-mode`, and the `workflow.properties` knob list.

### `experiments/hadoop/hdfs-17960/README.md` — REWRITE
> line 82: "`BooleanReachConditionExtractor` still reports
> `DEGENERATE_UNCONSTRAINED_ROOT_SPACE`, with both valuations SAT"
> line 115: "A plain `z3 schedule/final/candidate.smt2` returns `sat`."
Both classes/codes: 0 hits. The plain-z3 claim is false as written — the composer writes its
own `(assert (! (= <root> …) :named valuation__…))` pins into the published file
(`compose/Composer.java:2071`), so a plain run answers about one valuation; the scratchpad
probe records 17960's plain run as `unsat` for exactly this reason
(`$SPO/final/probe_final.sh` header). Line 114's "structured Z3 result" file is gone.
Line 60's "refined graph" is fine (still built).

### `experiments/hadoop/hdfs-17899/README.md` — REWRITE
> line 10: "Closure-wide symbolic merging combines those cases, and each selected shared read
> retains a complete bounded GuardedRead snapshot of the writer expressions available to the
> SMT choice."
`closure-wide` survives only as one run_engine.sh:1984 comment about EXPLORE waves;
`GuardedRead` only in three finalizer comments. The published mechanism is ReadRow/WriteRow
version joins plus the composer's family arms. The rest of the file (roots, cut ports,
`target_occurrence` in `case.sh`, the per-case table) checks out.

### `experiments/hadoop/hdfs-17897/README.md` — REWRITE, "Clock window" DELETE
> line 77: "900 000 ms admits all three with room, and it is still a *skew*"
The section documents a declared clock window and a default width; `ClockRootPhysics` and every
window/`WINDOW_BOUNDARY` noun are 0 hits, and the file's own line 62-64 already states the
surviving rule (floor `>= 0`, no window) — but cites `explore.FlipQuery` line 362, which is now
an unbound-symbol refusal; the floor is at `FlipQuery.java:41` / `Composer.java:1866`.
Line 24's "closure-wide waves ... bounded GuardedRead snapshot": same stale pair as 17899.

### `experiments/hadoop/hdfs-11741/README.md` — REWRITE
> line 38: "Consumer anchors retain each receive boundary, and selected shared reads retain
> bounded GuardedRead snapshots of their writer expressions."
> line 46: "lane11741h observed four — `balance-block#1` and `#2`, on dn0 and on dn1"
Same GuardedRead wording; and a checked-in doc citing a scratchpad campaign lane by name.
Everything else (the two root authorities, `SERIAL_NO`/`EXPIRY_DATE` hooks, the clock root,
declared cut ports, the `root-domains.jsonl` section) matches the tip.

## Claims that contradict the new README draft (`$MY/readme-draft/README.md`)

1. `README.md:19,103` and `docs:87` keep linked replay as the replay unit; draft §2 retires it
   by name ("*Linked replay.* An earlier design…") in favour of focused replays.
2. `README.md:183` publishes `gap_ledger.json` and never mentions `claim.json`; draft §6 names
   `claim.json` as an epoch deliverable (and `ComposeMain.java:113` writes it).
3. `docs` 683-696 makes acceptance a table of 11 named blockers; draft §2/§5 makes every
   refusal a `GapRow` of a closed kind classed BLOCKING/DIAGNOSTIC — the tip agrees with
   the draft (`contract/GapKind.java`).
4. `docs` 622-670 describes a separate solver stage publishing valuations, mechanism necessity
   and fatal-state selection; draft §5 has one claim policy naming the narrowest mechanism,
   gated on `polarityDecides`.
5. `hdfs-17960/README.md:82,115` says both valuations are SAT and plain z3 answers sat; draft
   §7 states valuation 0 unsat / valuation 1 sat, `polarityDecides true`, 0 blocking gaps.
6. `hdfs-17897/README.md:60-80` declares a clock window; draft §5 says a clock has "a floor of
   zero and no window".
7. `README.md` Toolchain (two traces + refinement, lines 14-20) vs draft §3, whose stage table
   has one `SEED` recording and a `PLAN` producing `static_scope_map.jsonl`; both the two-pass
   trace (run_engine.sh:682-712) and `RuntimeRefinedGraphBuilder` still exist at the tip, so
   the *draft* is the side that under-describes the engine here.
8. Draft §6 carries an open TODO — "the acceptance harness … is not in the repository; name its
   in-tree home here." Part B of this mandate lands it at `experiments/hadoop/accept/`.

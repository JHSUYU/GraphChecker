# Wave 3 plan — one symbol per occurrence; the VM's expression is the authority

Decision (Zhenyu, 2026-08-25): *"多个 occurrence，我们都当成 symbolized variable。
如果这个变量你读的时候，VM 里有符号表达式你就直接用；没有的话，那就当成一个新的
符号变量。真实代价（fail-open）我愿意接受。并行加速仍然要保留。"*

This is README "Symbolic propagation is the authority" taken literally, and
it removes the offline prediction layer that grew to reconcile plan-time
guesses with what the VM already records at replay.

## The rule, as three contracts

### C1 — Mint: every entry of a declared mint site mints a fresh symbol
- Input stays: `symbolic-inputs.jsonl` declares **fields** (e.g.
  `<DelegationKey: int keyId>`, `<DelegationKey: long expiryDate>`) per region.
  It no longer declares selectors, owners, `requiredBySourceIds`, or
  occurrence choice.
- At runtime, `symbolizeConfiguredSourceField(sourceId, owner, field)`:
  if `owner == null` → no-op (nothing to mint, not a gap); else ask the VM to
  symbolize the field on that owner, **always**, with a fresh symbol named
  `sym__<sourceId>__<occurrenceId>__<ordinal>` where `ordinal` is the
  per-(activation, site) entry count. No selection, no "selected phase",
  no `SELECTED_SOURCE_WITHOUT_OWNER`, no one-producer-per-phase admission.
- **Verified 2026-08-25: the VM overwrites.** `FieldSymbolizer::do_field_helper`
  (`hotspot/src/share/vm/concolic/fieldTraverser.cpp:179,205,227,257`) calls
  `sym_inst->set_sym_exp(fd->offset(), new FieldSymbolExp(...))`
  unconditionally, and both `SymObj::init_sym_exp` and `set_sym_exp` are
  `_exps[offset] = exp` (`reference/symbolicObject.cpp:21-33`). The per-field
  getter is `SymObj::get(int offset)` (NULL when absent), on the subclass
  only. The rule "a propagated expression wins over a fresh symbol" is a VM
  invariant, so the guard goes in the VM, not Java:
  1. add `virtual bool has_sym_exp(int field_offset)` to `SymInstance`
     (`reference/symbolicInstance.hpp`), implemented in `SymObj`
     (`_exps.find(offset) != end`), `SymPrimitive`, `SymString`;
  2. in `do_field_helper`, before each of the four `set_sym_exp` sites:
     `if (sym_inst->has_sym_exp(fd->offset())) { /* propagated wins */ return false; }`
     and do NOT record a fresh path-condition symbol for that field;
  3. rebuild the VM (`make images`; remove both
     `build/<conf>/hotspot/linux_amd64_zero` and `hotspot/_hotspot.timestamp`
     first, see [[concolic-vm-build]]) and run the 26 smokes
     (`scripts/causynth_smoke_test.sh`) plus one new smoke:
     symbolize a field, propagate it into a second object's field via
     assignment, symbolize that second field — the expression must be the
     first symbol, not a new one.
  No `-XX:` flags exist for this; it is unconditional.

### C2 — Read: propagated expression if present, else a new free symbol
- Any selected read site (existing hooks: materialize*/symbolize*,
  container reads via `materializeAssociativeRead`, RPC attach) asks the VM
  for the value's expression.
  - present → use it (this is what happens today for handoff-attached
    values);
  - absent → mint `free__<site>__<occurrenceId>__<ordinal>` and record it in
    the ledger as `FREE_SYMBOL` with the site, occurrence, ordinal, and the
    reason "no recorded lineage".
- `allKeys.get(K)` with K symbolic is a symbolic associative read;
  `ContainerSmtCodec.AssocState` already lowers it. The DataNode-side
  `selectedIntValue` hook and `causynthHdfs11741SelectedKey` become
  unnecessary: the expiry hook mints on the owner it is called with, and the
  owner's identity is carried by the map read's expression.

### C3 — Compose from recorded lineage; name what is free
- The composer consumes: the VM handoff ledger (`VALUE_HANDOFF` rows with
  `exportEventId`/`attachEventId`/`expression`), per-case symbolized-input
  rows, container transitions, path conditions, order — **exactly the rows
  the raw result already carries**. It no longer looks up "the producer
  case" for a handoff (`exactHandoffProducerCase` goes), nor binds selectors
  (`emitConfiguredSourceSelector` family goes): a receiver expression already
  *is* the sender expression.
- `candidate_composition_manifest.json` gains one array,
  `freeSymbols: [{symbol, site, occurrenceId, ordinal, javaType}]`, listing
  every symbol minted under C2. `result.json` carries `freeSymbolCount`.
  A witness is reported with that list; the README acceptance text for
  HDFS-11741 says the witness "assumes these unconstrained".
- The three README-mandated model values for HDFS-11741 (K, NN expiry, DN
  expiry) are found by **sourceId**, not by selected phase: the model must
  contain at least one `sym__HDFS11741.NAMENODE.CURRENT_KEY_ID__*` etc., and
  the K that reaches the target operand must be a propagated one (its
  lineage crosses the getBlockKeys / heartbeat / SASL handoffs) — that is
  the README's "one symbolic K lineage" check, now read off the ledger.

## What gets deleted (with the wave-1/2 inventories' numbers)

| layer | delete | ≈ lines |
|---|---|---|
| ConcolicScheduler | `SymbolicInputSelection` entirely: annotateSources, outputPublications/latestPublication/phaseBeforeOutput/phaseRotatedBeforeOutput, bindSourceSelectors (two-pass), arrivedVersions/inputVersions/carriedBySend/rotatesBefore/readPrecedesEveryMint/unselectUnbindableReads, resolveSourcePhaseOwnership + SourcePhaseClaim, validateSourceCoverage/validateSourcePhaseSelections, SourceFlowTask/SourceVersion/SourceArrival, OutputVersionBoundary/memberBoundaries, the `symbolicInputSelection` task policy | 2,600 |
| contract | `ConfiguredSourceSelectorContract` (selectors, evidence, `requiredBySourceIds`), `SymbolicSourceEvidence` rows keyed by selected phase, `ConfiguredSourcePhaseContract` **CONSUME** phases and `selectedConfiguredSourcePhases` (PUBLISH sites stay as the *catalog of mint sites*, without selection), `ExecutionTask.validateConfiguredSourceBindings`, `OutputClosureContract.VERSION_BOUNDARIES` + codec special cases | 500 |
| RuntimeRegionPlanner | `coarseOccurrenceOutputVersions` ledger (keep the anchor member; versions are symbols now), `configuredSourcePhases` selection plumbing | 200 |
| ConcolicRegionRuntime | `Configuration.indexConfiguredSourceSelectors`, `sourceAliasesForSelector`, `rotatesOwnSource`, `PlannedSourceAlias`, `publishedSourceSelector`, `stageSourceSelectorValue`, `selectedConfiguredSourceIntValue`, `claim/record/releaseSymbolicSource` ownership, `observeConfiguredSourcePhase` ordinal matching against a *selected* catalog (keep the per-site ordinal counter), `SELECTED_SOURCE_WITHOUT_OWNER`, the selector `*ForTests` seams and their tests, `commitMap/FieldVersions` | 1,000 |
| ConcolicSmtComposer | `exactHandoffProducerCase`, `mergeVmHandoffs`/`mergeConfiguredSourceSelectors` pairing, `emitConfiguredSourceSelector` family, the four binding arms' selector branches; `RecordedSessionModel` selector naming (`scopedSelectorName`, readChoices tied to selectors) | 600 |
| StaticSymbolicSourceDiscovery | `selectorHook` / `selectorSourceId` / CONSUME phase minting; keep the `symbolize` PUBLISH site discovery | 60 |
| Hadoop (`~/dev/hadoop`) | `CausynthSymbolicSource.selectedIntValue`, `BlockTokenSecretManager.causynthHdfs11741SelectedKey`, the `symbolizeCausynthHdfs11741*Expiry` wrappers' selection; the expiry hooks mint on every key they are handed (`updateKeys`/`addKeys` iterate `allKeys` and mint each member's expiry — every occurrence is a symbol) | −120, +40 |
| experiments/hdfs/hdfs-11741 | `symbolic-inputs.jsonl` rows become field-only (drop `configuredSourceSelectorDeclarations`); `Hdfs11741SymbolicInputConfigurationTest` rewritten | — |
| **total** | | **≈ −5,000 direct**, plus what decode-once / one-planner then unlock |

Then the rest of the README wave-3 list (decode once; one session model; one
planner layer with the once-only-root fix as a per-iteration root; one
instrumentation pass; one owner per check; derived fields off the wire).

## Sequencing (each step is one gate; the matrix is the gate; HDFS-11741 last)

1. **Runtime + Hadoop mint/read (C1, C2)** — one executor pair (GraphChecker
   runtime lane; Hadoop lane). Gate: matrix 20/20 with the variable set
   changing in a KNOWN way: RPC_COMPARE rows already mint one symbol per
   field per occurrence, so the expected diff is **none** for the matrix;
   the `freeSymbols` array must be **empty** on all 20 rows (every value the
   matrix reads is propagated). That emptiness is the proof C2 does not
   fire where lineage exists.
2. **Composer from lineage (C3)** — smt lane. Gate: matrix 20/20, model
   counts identical to `matrix-20260825T152212Z` on all 20 rows, `freeSymbols`
   empty, `candidate.smt2` diff limited to the removed selector assertions.
3. **Delete the prediction layer** — scheduler/contract/planner lanes.
   Gate: matrix 20/20; `execution_task_plan.jsonl` loses the
   `symbolicSourceFields`/`configuredSourceSelectors`/selected-phase members;
   PLAN time on the matrix rows should drop measurably.
4. **HDFS-11741 end to end** — the README acceptance commands on a fresh
   campaign root; the once-only-root re-root
   (`BPServiceActor.offerService()` → per-iteration boundary) is done in the
   planner as part of step 3 or here. Expect `freeSymbols` non-empty here;
   each entry is a coverage finding, reported, not fixed silently.

## What must survive (checked by the gate, listed so no executor "simplifies" it)
- declared fields as the only manual input; `CausynthSymbolicSource.symbolize`
  hook name and (sourceId, owner, fieldSignature) literal shape (static
  discovery depends on it);
- the VM broker/ledger/handoff (`VALUE_HANDOFF` with exact event ids),
  `ContainerSmtCodec`, the 32 VM entry points, the Hook names;
- eight-worker replay, target-first scheduling, immutable iteration lineage,
  deterministic merge (README "What must be retained");
- the README acceptance fields and `z3-result.json` model shape; the three
  HDFS-11741 model values by sourceId.

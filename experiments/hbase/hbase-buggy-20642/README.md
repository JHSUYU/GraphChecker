# HBASE-20642 put back (hbase-buggy-20642, point hbase-adhoc-04)

## The bug

[HBASE-20642](https://issues.apache.org/jira/browse/HBASE-20642) (fix 72784c2d83, 2018): clients did not reuse one
nonce across the attempts of a DDL operation. HBaseAdmin's `MasterCallable.rpcCall` built the request with
`ng.newNonce()` on every attempt, so an attempt retried after its reply was lost (or after a master failover) carried a
nonce the master had never registered: `ProcedureExecutor.registerNonce` found no procedure for it and the master ran
the operation a second time. For a disable, the second `DisableTableProcedure`'s constructor runs
`preflightChecks(env, true)` and finds the table DISABLING or DISABLED: `TableNotEnabledException`, and the client's
`disableTable` fails although the table was disabled. The fix made the nonce a field of the callable, one per operation.

Point hbase-adhoc-04 (`docs/checks/HBASE.md`, `../hbase-adhoc/checks.tsv`) is that throw:
`AbstractStateMachineTableProcedure.preflightChecks`'s `!ts.isEnabledOrEnabling()` -> `TableNotEnabledException` (:163).

## What was put back, on graphchecker/hbase-bug-20642

The fork's branch is `graphchecker/hbase-checks` (b5d5cc6a20, the tree every HBase ad hoc check runs) plus two commits:

- **The bug, by hand** (8e27245059): `HBaseAdmin` is gone from today's tree. `RawAsyncHBaseAdmin.disableTable` built its
  request once and `procedureCall`'s action resent that request on every attempt of the
  `AsyncMasterRequestRpcRetryingCaller`: one nonce per operation by construction. Its caller's action now builds the
  `DisableTableRequest`, and so draws `ng.newNonce()`, per attempt, the rest of `procedureCall`'s body
  (`waitProcedureResult`, the procedure consumer) unchanged. Only `disableTable`, the operation this case drives; every
  other DDL keeps one nonce per operation. The master side (`HMaster.disableTable`'s `NonceProcedureRunnable`, the
  nonce dedup) is untouched: it is what the bug escapes.
- **The workload and the target** (1ba966bb6c): `TestCausynthDisableRetryNonce`, and `hbase-buggy-20642` added to
  hbase-adhoc-04's marker on :163.

## The workload

`org.apache.hadoop.hbase.master.procedure.TestCausynthDisableRetryNonce#disableTwoTables`: a one-region-server
automatic cluster; two tables of one family created, then each disabled once through `UTIL.getAdmin()`. It passes
natively (2.2 s): no attempt is retried, so each disable runs one procedure and its preflight finds its table ENABLED.

Why not an existing test: the study's (TestRegionMove#testDisableAndMove) disables one table once, so the recording has
one preflight occurrence of the disable's shape, and the retry is an occurrence the recording never opened (below).
TestAdmin3#testEnableDisableAddColumnDeleteColumn disables one table twice but on a three-server cluster with column
family additions and deletions (region reopens) between: the same declared shape with far heavier replays.

Why two disables: a world where the first disable's reply is lost has the client retry it; with the bug the retry's
handler constructs a second `DisableTableProcedure` for the first table. That handler's activation is an occurrence of
the preflight region under a DisableTable request from the test, the shape of the declared occurrence (the second
disable's preflight), at an address the recording never opened; by IDENTITY §9's order rule it answers the earliest
planned task of its shape not yet run, the declared one. Its preflight reads the first table's state: DISABLING or
DISABLED once the first procedure has set it, so :163 throws in the declared occurrence. With the fix the retry
carries the first attempt's nonce, the master returns the first procedure's id without constructing a procedure, and no
preflight runs.

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("hbase-adhoc-04,hbase-buggy-20642")` on preflightChecks' `throw new TableNotEnabledException` (AbstractStateMachineTableProcedure:163) |
| the occurrence | `target_occurrence` in `case.sh` | `auto0/master0#epoch0/region/REGION.98cba534-...#2`: the second activation of the preflight region on master0, the second disable's (the first is the first disable's; creates run no preflight) |
| scope | `case.sh` | hbase-adhoc-04's: AbstractStateMachineTableProcedure, TableStateManager |
| fault transports | `../system.sh` | `HBASE_RPC` (the HBase default): the client's DisableTable reply is a door |
| world depth | `case.sh` | `CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=1`: the lost reply, and the retry's preflight read ordered after the first procedure's DISABLING write if a replay's retry comes first |
| heap | `workflow.properties` | `engine_memory_mb` 24576 (CloudLab's cases use 65536 on 376 GB nodes; these nodes have 251 GB and five agents share the ledger) |
| mechanism | `experiments/accept/report.py` | `hbase-buggy-20642`: MARKER_FLIPPED by an HBASE_RPC fault |

The run's budget is `../hbase-buggy-cases.tsv`'s.

## Result: SAT confirmed in the VM; natively the bug fires 10/10 at :163, but not at the declared address

**Verdict.** SAT confirmed in the VM: the lost reply to the first DisableTable makes the client retry with a new
nonce, and the retry's DisableTableProcedure throws at the point's own throw (:163). Natively the planted lost reply
gives the same throw in 10 of 10 runs, with 0 of 10 in the controls. REPRODUCE's exact-anchor check still counts 0 of
10 "at the anchor": the throw happens in the retry's handler, which only the VM answers to the declared occurrence by
its shape (IDENTITY §9). A native counterpart of that rule (455a6dd66) was rejected by the independent review and
reverted (017dcf890), so by CHECKING's bar (native REPRODUCE k/N at the anchor) the SAT is not accepted.

**HB20642a**, the engine as published (stopped, `accept-HB20642aSTOP-baseline-hbase-buggy-20642`): the plan held the
test turn's 19 REQUEST doors and no reply reader, and round 0 asked 38 REQUEST flips and 0 RESPONSE flips. A REQUEST
fault keeps the first DisableTable from the master, so the retry runs one procedure and the bug is not reached.
Engine support 948e4779f (lead-approved and reviewed) admits the reply legs of the demanded message's doors as control
producers: 19 `finishCall` occurrences planned, and 57 RESPONSE flips in round 0
(`/bulk/analysis/buggy-detect-2026-10-26/HBASE-20642-notes.md`).

**HB20642c** (snapshot `/bulk/gc-run/hbase-b20642-3` = f82385bcc on 948e4779f, tree set `/bulk/trees/hbb20642` =
1ba966bb6c; `/bulk/gc-out/hbase-buggy/20642/accept-HB20642cSTOP-claim1-hbase-buggy-20642`; its claim 1 is in
`final/unreproduced/0000`):
- **Claim 1:** `SAT_CANDIDATE` `MARKER_FLIPPED`, `polarityDecides` true. The one moved root is
  `REGION.678dfe9c...in.f9d4e5a9` = true: the fault marker of `RpcConnection.finishCall` in client0's occurrence
  anchored on the master's reply (endpoint 1ed2bbc8a1b3d6c9) to the first DisableTable (c3a356c8). The legend has 13
  leaves over 14 paths, all of them RESPONSE-door markers of the test's replies.
- **The witness session** 1ec4e01bc9896ff9-fdd8f867:
  - the schedule has DisableTable SEND c3a356c8 (seq 387), then a second DisableTable SEND 3bb35a7d (seq 458), the
    retry;
  - the preflight under 3bb35a7d answered the declared address (`ADDRESS_UNSTABLE`: "under a chain of its shape whose
    counts differ from the recording's, and answers it");
  - its target row observed the fatal, while the first disable's preflight (c3a356c8) was healthy.
- **The chain, on the bug tree:**
  1. RawAsyncHBaseAdmin.disableTable's per-attempt action builds a DisableTableRequest with a fresh `ng.newNonce()`.
  2. The master's `NonceProcedureRunnable` finds no procedure for that nonce (ProcedureExecutor.registerNonce).
  3. `new DisableTableProcedure(...)` (HMaster:2931) runs `preflightChecks(env, true)` (DisableTableProcedure:78).
  4. The first procedure has set the table DISABLING/DISABLED, so `!ts.isEnabledOrEnabling()` holds and
     AbstractStateMachineTableProcedure:163 throws `TableNotEnabledException(causynth_disable_first)`.
- **CONFIRM:** realized. The witness session is itself the run: "it took every edge the model chose ..., ran every
  moved root at the model's value, and observed the fatal at the anchor".
- **REPRODUCE** (`final/unreproduced/0000/reproduce.json`): planted 10, fatal 10, atAnchor 0; control fatal 0 of 10.
  Each planted run's stdout shows `TableNotEnabledException: causynth_disable_first at
  ...AbstractStateMachineTableProcedure.preflightChecks(AbstractStateMachineTableProcedure.java:163)`, at the retry's
  own occurrence address (Anchor:3bb35a7d...), not the declared one.
- The campaign then composed claim 2 (the same lost reply and a second one); it was stopped there (lead's call).

**HB20642d** (snapshot hbase-b20642-4, with 455a6dd66, the rejected native rule): its native runs bound the same retry
address by shape in 10 of 10 (atAnchorByShape 10, control 0), then the campaign died on 455a6dd66's plant.log jq
(fixed in 243d826a6, then everything reverted). This is evidence of what the native runs did, from code that is no
longer on the branch.

**What it says about the fix:** with HBASE-20642's fix the retry carries the first attempt's nonce, the master returns
the first procedure's id without constructing a procedure, and no preflight runs: the same world throws nothing.

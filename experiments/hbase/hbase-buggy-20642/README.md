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

## Result: SAT, PASS: confirmed in the VM, reproduced natively 10/10 at the anchor (control 0/10)

**Verdict.** SAT: the reply to the first DisableTable is lost, the client retries with a new nonce, and the retry's
DisableTableProcedure throws at the point's own throw (:163). CONFIRM realized it in the VM. Native REPRODUCE counts
10 of 10 planted runs at the anchor and 0 of 10 controls, and report.py gives PASS (HB20642e, below). The retry's
handler answers the declared occurrence by its shape (IDENTITY §9) in the VM and natively alike. It does so through
the one implementation of §9's order rule (`runtime/AnswerOrder`, GC 93a168e87) that `ConcolicTaskPlan#select`
and `RecordingPlant#opened` both call.

**No workload gives the retry the declared address.** The retry's preflight differs from the declared one only in
its anchor, the client's DisableTable SEND endpoint. That endpoint's occurrence index is the request's start chain.
Every first attempt stands at `Root:CLIENT/test#1 | addListener#u3:AsyncMasterRequestRpcRetryingCaller.doCall@k/...`,
where k counts the test's DDL operations (create 0, create 1, disable 2, disable 3). The retry stands under the first
attempt's callback and the retry timer:
`HMaster$lambda_run_0.run@0/addListener#u3:doCall@2/accept@0/addListener#u3:lambda$doCall$5@0/accept@0/tryScheduleRetry#u23@0/run(Timeout)@0/addListener#u3:doCall@0/...`.
HBase does not count sends per verb (the Hadoop IPC request level does), so the retry cannot be made "the Nth send".
Only a recording that itself retried a DisableTable at that position could open the address. A fault-free recording
has no failed attempt: a natural failure after the procedure is built fires the bug natively, and one before it makes
the witness need a second moved root (`/bulk/analysis/buggy-detect-2026-10-26/HBASE-20642-notes.md`, H2).

**HB20642e** (snapshot `/bulk/gc-run/hbase-b20642-5` = 93a168e87, tree set `/bulk/trees/hbb20642` = 1ba966bb6c;
`/bulk/gc-out/hbase-buggy/20642/accept-HB20642e-hbase-buggy-20642`, 866 s, head node1):
- **Claim** (valuation 1): `SAT_CANDIDATE` `MARKER_FLIPPED`, `polarityDecides` true. The one moved root is
  `REGION.678dfe9c...in.bb037ad5` = true: a fault marker of `RpcConnection.finishCall` (#u39) in client0's occurrence
  a5fe07ecef0b627e, which reads the master's reply (endpoint 1ed2bbc8a1b3d6c9) to the first DisableTable
  (c3a356c8). This is the same reply reader as HB20642c's claim 1, at another marker unit of the RESPONSE door. The
  legend (`tools/analysis/smt-legend.py`) has 8 leaves, all RESPONSE-door markers of `finishCall`.
- **CONFIRM:** realized. The witness session fec145b736276486-2804f1c3 is itself the run. Its preflight under the
  retry's anchor answered the declared address by shape (`ADDRESS_UNSTABLE`: "the planned occurrence ran at
  ...Anchor:3bb35a7d...") and observed the fatal.
- **REPRODUCE** (`final/reproduce.json`, counted by 93a168e87, where atAnchor and reproduced still included a
  fatal in the shape-bound activation): planted 10, fatal 10, atAnchor 10, answeredByShape 10, reproduced 10;
  control fatal 0, atAnchor 0, answeredByShape 0 (of 10). The counts were later split (see "Exact and
  by-shape counts" below). Each run's trace has exactly one activation at the anchor's address, and it is the
  shape-bound one, so the fatal is by shape in all 10. Each planted run's trace has
  - `PLANT_APPLIED` (the lost reply),
  - then `PLANT_ANSWERED` (the planned `...Anchor:eb4017bed67364cb...`, plannedId e5af9d703477be2b, which the run
    computed at `...Anchor:3bb35a7d1bfd5a5e...`),
  - then `PLANT_FATAL` at the anchor, with `TableNotEnabledException: causynth_disable_first` at
    AbstractStateMachineTableProcedure.java:163 in its log.
  `plant.log` names each of the 10 runs `ADDRESS_UNSTABLE`.
- **report.py:** PASS (`summary.tsv`: `MARKER_FLIPPED ... reproduced 10/10 natively`).
- **The chain, on the bug tree:**
  1. RawAsyncHBaseAdmin.disableTable's per-attempt action builds a DisableTableRequest with a fresh `ng.newNonce()`.
  2. The master's `NonceProcedureRunnable` finds no procedure for that nonce (ProcedureExecutor.registerNonce).
  3. `new DisableTableProcedure(...)` (HMaster:2931) runs `preflightChecks(env, true)` (DisableTableProcedure:78).
  4. The first procedure has set the table DISABLING/DISABLED, so `!ts.isEnabledOrEnabling()` holds and
     AbstractStateMachineTableProcedure:163 throws `TableNotEnabledException(causynth_disable_first)`.

**Exact and by-shape counts (the review of 93a168e87; the lead's decision).** Which native activation answers
the anchor by shape is decided by that run's arrival order. So for a shape-answered run, REPRODUCE is no longer an
independent exact-identity check: it checks that the planted world threw in the activation §9 binds to the
anchor, not that it threw at the recorded address. REPRODUCE therefore keeps the two apart:
- `PLANT_FATAL` states `byShape`: whether its enclosing anchor activation is the one bound by shape.
- `atAnchor`, `reproduced` and the "reproduced in N of M" line stay exact-only.
- `answeredByShape` and `reproducedByShape` count the by-shape fatals and reproductions, the control's too.
- The lead reports both numbers for this case to the owner, who decides whether the by-shape count is accepted.
- HB20642e's PLANT_FATAL rows predate the `byShape` field, so its counts cannot be recomputed with the new jq;
  HB20642f gives them under the split rule.

**The engine support for the native answer (93a168e87).** `runtime/AnswerOrder` holds the select loop (own address
first; otherwise the earliest open task by recorded root call whose shape the context has) and `answeredHere` (an
address the recording opened, a context a task of the group plans the region in, a folded entry). CONFIRM's
behaviour is unchanged: AnswerOrderTest checks the loop against a verbatim copy of the parent's on 20000 random
tables. ConfirmMain recomputed on HB20642c and HB15039b with the parent and the new build gives identical CONFIRM
tasks, ORDER edges, decisions and plant rows, apart from the TARGET rows' new plan facts. ConfirmMain writes the
anchor's root hook group onto the plant's TARGET rows. `RecordingPlant#opened` answers each entry of that region and
root method as a replay would, and the occurrence answering the anchor takes the planned address (`Identity#answer`).
A loop-body anchor, an anchor with no shape, and a group whose roots are selected by argument types stay exact-only,
and plant.log says which. Independent review: pending at the time of writing (the run counts only if it passes
unchanged).

**HB20642a**, the engine as published (stopped, `accept-HB20642aSTOP-baseline-hbase-buggy-20642`): the plan held the
test turn's 19 REQUEST doors and no reply reader, and round 0 asked 38 REQUEST flips and 0 RESPONSE flips. A REQUEST
fault keeps the first DisableTable from the master, so the retry runs one procedure and the bug is not reached.
Engine support 948e4779f (lead-approved and reviewed) admits the reply legs of the demanded message's doors as control
producers: 19 `finishCall` occurrences planned, and 57 RESPONSE flips in round 0
(`/bulk/analysis/buggy-detect-2026-10-26/HBASE-20642-notes.md`).

Earlier runs:

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

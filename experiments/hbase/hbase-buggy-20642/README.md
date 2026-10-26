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

## Result

(pending)

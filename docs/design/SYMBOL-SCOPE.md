# Symbol scope: what is symbolic, derived from the fatal slice (2026-09-26)

Owner's direction (2026-09-26): the symbolic variables are chosen too narrowly.  From
the fatal condition, take the operands of the branch that decides it; the backward
data-flow analysis from those operands covers many variables, and the variables they
are control dependent on -- in other regions too -- can all be symbolic.  Symbols
propagate as usual; a downstream symbol that receives an upstream value is not free,
it is bound by symbolic propagation, composition and merge.  Automate it.

This document states the rule and maps it onto the mechanisms that already exist
(LEAN-DESIGN §1, DESIGN4 §2, GreyGraph §3.1).  It changes WHICH values are symbols,
not how a symbol is bound or validated.

## 1. The rule

A value is symbolic iff it lies in the fatal slice `S` and either comes from the
environment or enters an occurrence from another occurrence.  Nothing else is a new
symbol: everything downstream of a symbol is symbolic by propagation (the VM's
shadows), and a value that already carries an expression is never minted again.

| where the value is born | what it becomes | bound by |
|---|---|---|
| **F1** environment: a clock read, a fault door, (later) a restart or a delivery delay | ROOT | free inside its domain -- the only free symbols |
| **F2** a read of a shared location `ℓ` (field, static, container entry, atomic) that another occurrence writes | TRACKED READ | the version it observed, plus every attested writer occurrence HB-concurrent with it in the same session (`Writers_W(ℓ)`, rule 3: a writer's writes move as a block) |
| **F3** a message leaf that crosses a process | WIRE ATTACH | the producer's export (message families) |
| **F4** a return or a parameter crossing into code outside the analysis scope | grow the scope (§2) so the value propagates; if the producer stays out of reach | PINNED to the recorded value |
| a read of `ℓ` no occurrence of the recording wrote (state from before the window) | PINNED | the recorded value |

Never free: a symbol with no producer is pinned, not released.  A free leaf is a
witness the engine invented (the v9 lesson; a planted field value would "reproduce"
any failure).  CONFIRM plants ROOTS only; a tracked read or an attach is realized by
its producer running in the replay, or not at all.

## 2. The slice `S`, and its scope

`S` is the backward slice of the operands of the target's deciding branch(es):
data flow through locals, arguments and returns; the jumping step from a field read
to every type-compatible write of the field (GreyGraph §3.1.1); message leaves back to
their senders (F3); and CONTROL DEPENDENCE: a demanded definition demands the branches
deciding it (`SeedBackwardStaticAnalyzer#demandControllingGuards`), in whatever method
and region the definition is -- so the guards under which a writer in another region
stores `ℓ` are in `S`, and their operands in turn obey §1.

Today `S` stops at the case's declared class scope (`case.sh` `scope`), e.g. adhoc
sender-gs stops at `BlockSender.<init>`'s parameter and at `getReplica`'s return.  The
scope becomes a fixpoint: start from the target's class; add every class holding a
writer of a demanded field, a caller passing a demanded argument, or a sender of a
demanded leaf; stop at the modules (common, hdfs-client, hdfs) or a class budget.  A
case's scope list becomes a hint, not the boundary.

## 3. Control flow across regions

A writer occurrence's decision prefix is already part of every path that joins to it
(Composer P3, `closureConditions`).  What makes it matter is F2: a store in another
region is a version -- published and joinable -- when its value is symbolic OR when it
is a concrete store under a guard the replay decided symbolically (the VM's guarded
stores, `GuardedStoreSites`, VM24).  The guarded-store table is derived from `S` (every
method of `S` that stores a tracked location, with its guard sites), not from a
declared cell list.  So a value is world-dependent through the writer's control flow,
and exploration can flip the writer's guard to change what the reader sees.

## 4. Binding and validation (unchanged; now exercised)

* COMPOSE: a tracked read's alternatives are STATE families (one selector per writer
  occurrence and session); attaches are message families; eligibility per session.
* DECIDE: a witness is claimed only under a mechanism the recording decides --
  a moved root, a clock, or a single replaced pairing whose pin refutes it
  (STATE_PAIRING_FLIPPED / MESSAGE_PAIRING_FLIPPED).  Pairings only another run's
  delivery makes fatal name no mechanism (adhoc token-nokey).
* CONFIRM: holds the model's reads-from as ORDER rows (the writer's activation exits
  before the reader's enters, competitor writers outside).  An alternative writer the
  schedule cannot put before the reader stalls the gate: `CONFIRM_MISMATCH`, the
  claim unconfirmed.  This is the shared-field false positive the owner expects: with
  F2 wide, STATE_PAIRING candidates appear, and the unrealizable ones stop here.

## 5. Bounds

Only locations of `S`, and only those read by an occurrence other than their writer;
alternatives only HB-concurrent and attested writers; the closure's version chains
(P3c) stay as they are.  Costs to measure per case: tracked locations, guarded store
methods, STATE families and their arms, formula size, replay slowdown.

## 6. Automation, in order

1. **F2 from `S`**: the scope map classifies every read of a location stored in
   another region as tracked; the guarded-store table and the observed write sites
   come from it; the unwoven-accessor READ placeholder becomes the special case where
   the VM cannot version the read itself.
2. **Scope growth** (§2): the fixpoint replaces the declared class list.
3. **Wire pairing** (F3): protobuf `Builder.setF` / `getF` pairs per message type,
   direction from the RPC interface's request/response types, IPC and DataTransfer
   carriers; a hand-written WIRE_FLOW stays only where no rule derives it.
4. **Workloads**: existing MiniDFSCluster tests, ranked by how many checks they reach
   INSIDE the recording window (coverage split at `startRecording`), for bug finding
   with the fault doors.

Each step is validated on the nine cases (9/9, causal chains per `chaincheck.py`) and
on the ad-hoc cases, counting what §5 lists and what CONFIRM rejects.

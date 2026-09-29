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

The case's declared class scope (`case.sh` `scope`) is where `S` starts, not where it
ends: e.g. adhoc sender-gs stopped at `getReplica`'s return.  SEED grows the scope to a
fixpoint (`run_engine.sh campaign_analyze_grown_scope`):

1. The static pass publishes `scope_frontier.jsonl` (`plan.ScopeFrontier`), each row
   with its distance to the throw's guards over `S`'s edges (the thrown value's own
   construction, its message, is not the fatal condition; a cell the throw does not
   depend on, a declared wire flow's or fault's own seed, is no part of `S`):
   * `CALLEE`: a callee whose return `S` demands but whose body is not analysed (its
     class is out of scope, or it is abstract with no implementation in scope);
   * `FIELD`: a field `S` reads or stores;
   * `FORMAL`: a method whose primitive or string formal `S` demands only through a
     field -- a writer's value (`Block.setGenerationStamp(long)`), whose callers are
     writers too;
2. `plan.ScopeGrowth` resolves the rows nearest first over the lineage roots (the
   modules common, hdfs-client, hdfs):
   * a callee of a type of the roots: the class whose body it runs, or for an
     abstract one the class each implementation inherits it from, unless that body
     only returns constants;
   * a field: its owner and, unless it is private or final, every class storing it;
     a static final field is a constant, no state;
   * a formal: every class calling the method.
   It copies each class into `<output>/scope-classes/` and lists it with its row in
   `GROWN`, until `causynth_scope_growth_budget` classes are grown (default 24).
3. The static pass reruns with that directory as a further process directory
   (`causynth.process.dirs`), and so does every later pass: one application scope.
   It stops when a round changes nothing.

What never grows the scope:
* The target's own callers: they would move the region root, and with it the
  identity of the occurrence under test (DataXceiver's `run()` swallowed the anchored
  SASL occurrence).  A formal the throw depends on without a field in between stays
  pinned (F4).
* A platform type (the VM models `java.*`), a protobuf message, or a formal of object
  type: payloads (F3), or objects whose own state is a frontier row of its own.
* A clock callee, which is a root already (F1).

Growth still changes the region structure of the declared scope: new state makes more
of its methods state-writer roots, and at run time a new root can enclose the target
through frames the static call graph never sees (a JDK SASL callback).  v60: with
`Configuration` grown, `getEncryptedStreams` became a root and enclosed the SASL
handler holding 11741's target, so 8 of the 9 declared target occurrences were no
longer observed.  A static guard (no new root in the declared scope) could not name
the grown class responsible -- demand spreads over the whole slice -- and was dropped.
So a target occurrence is declared against a grown scope or not at all: the nine
regression cases, declared before growth, run with `causynth_scope_growth_budget=0`;
cases discovered with growth (the cluster-test workloads) keep it.  Growth is
deterministic, so their declarations stay valid.

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
  before the reader's enters, competitor writers outside).  Eligibility (`Arms#concurrent`)
  over-approximates: two NameNode occurrences a client thread caused one after the
  other (addBlock, then complete) are not causal-anchor ancestors of each other --
  the client's wait for the first response is in no row -- so a read may be given
  the earlier call's write as an alternative the program order forbids.  An alternative writer the
  schedule cannot put before the reader stalls the gate: `CONFIRM_MISMATCH`, the
  claim unconfirmed.  This is the shared-field false positive the owner expects: with
  F2 wide, STATE_PAIRING candidates appear, and the unrealizable ones stop here.

## 5. Bounds

Only locations of `S`, and only those read by an occurrence other than their writer;
alternatives only HB-concurrent and attested writers; the closure's version chains
(P3c) stay as they are.  Costs to measure per case: tracked locations, guarded store
methods, STATE families and their arms, formula size, replay slowdown.

## 6. Automation, in order

1. **F2 from `S`**: the scope map classifies as tracked every read of an integral (boolean to long)
   instance field `S` also stores, when a branch decides on the value within a few
   flows, before any store and on this side of the wire (`StaticScopeMap#READ_SITE`);
   every store of it is an observed write site, and a region reading it records its
   branches from entry.  A read that only feeds data is not tracked: in v59
   `tokenLifetime` and `serialNo`, read on the NameNode only to build a token, carried
   symbols into the token's bytes and its HMAC (17899-bug3's seed expressions grew from
   0.9 MB to 27 MB, the orchestrator ran out of heap) and bound nothing.  Nor is a read
   whose value a receiver decides on (F3 carries it): in v61/v62 `DataEncryptionKey.keyId`,
   read into the SASL user name that the DataNode checks, went through DIGEST-MD5 into
   the session cipher, and bug3's fault-world expressions reached 33 MB of CBC writes.  A static final field is a
   constant, no shared state (`SymbolicRegionPlanner#failureRelevantState`).
   Integral fields only (boolean, byte, char, short, int, long; until 2026-09-29 int and
   long, which left SOLR-18406's commit-point `deleted` flag unversioned): the VM's
   `observeExactPrimitiveField` versions no other type.  A container, a reference or a string -- where most of HDFS's
   shared state lives (a key map, a lease holder) -- is versioned only once a
   symbolic value is stored into it; observing one from its first concrete store
   needs a VM hook of its own (the container log's INITIAL version exists).
   The VM starts a field's log at the observation (INITIAL, the value from before
   the window), so the concrete store it precedes is a WRITE and a later getfield
   resolves over the log; until 578bd7e2f the observation only set the shadow and no
   observed concrete store left a version.
   Open: a store is observed only inside a running task, so a read of a location no
   task wrote yet files no ReadRow, the closure demands no writer, and the writer
   never becomes a task (visible-gs: the DataXceiver stores the replica's GS, the
   IPC handler reads it, neither joins).  §3.1's writer index closes this loop: the
   recording hooks the candidate read and write sites of the tracked fields by
   concrete object, `Writers_W(l)` is built from it, and PLAN makes the writers of
   every location a target-relevant occurrence read into tasks.
2. **Scope growth** (§2): the declared class list is the fixpoint's start.
3. **Wire pairing** (F3): protobuf `Builder.setF` / `getF` pairs per message type,
   direction from the RPC interface's request/response types, IPC and DataTransfer
   carriers; a hand-written WIRE_FLOW stays only where no rule derives it.
4. **Workloads**: existing MiniDFSCluster tests, ranked by how many checks they reach
   INSIDE the recording window (coverage split at `startRecording`), for bug finding
   with the fault doors.

Each step is validated on the nine cases (9/9, causal chains per `chaincheck.py`) and
on the ad-hoc cases, counting what §5 lists and what CONFIRM rejects.

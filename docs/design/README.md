# docs/design

The design of GraphChecker as the code on `main` implements it. Each document describes the
present only; what is done, partial or missing is in [../STATUS.md](../STATUS.md), and dated
experiment records are in [../reports/](../reports/). Where a document and the code disagree,
the code is right and the document is fixed.

| document | what it covers |
| --- | --- |
| [PIPELINE.md](PIPELINE.md) | The campaign, stage by stage: SEED, PLAN, INSTRUMENT, REPLAY, IMPORT, EXPLORE, COMPOSE, DECIDE, CONFIRM and EMIT, as `run_engine.sh` and the Java stages run them. |
| [SYMBOL-SCOPE.md](SYMBOL-SCOPE.md) | Which values become symbolic, and why. |
| [IDENTITY.md](IDENTITY.md) | How an event is named the same way in every run. |
| [CONTRACT-SPEC.md](CONTRACT-SPEC.md) | The rows a replay publishes and the rules they obey. |
| [VM.md](VM.md) | The concolic JVM (OpenJDK 8 Zero) under `third_party/OpenJDK-Concolic-Execution-Engine`. |

**PIPELINE.md.** For each stage: its inputs and outputs, its gates, and its refusals. It covers
the claim kinds `ClaimPolicy` publishes, how `polarityDecides` is decided, what CONFIRM replays
and holds, and what the acceptance harness (`experiments/accept`) requires on top of the claim.

**SYMBOL-SCOPE.md.** The heuristic fatal slice (`causynth/SeedBackwardStaticAnalyzer`) and the
static scope map built from it (`plan/StaticScopeMap`). The roots the engine mints: clocks by
category (`causynth/RootCatalog`), fault markers at woven doors (`causynth/DoorWeave`), and READ
placeholders. The shared state that is tracked and can be re-paired. Wire ports, both declared
`WIRE_FLOW` rows and ports derived from protobuf. How scope growth works
(`plan/ScopeFrontier`, `plan/ScopeGrowth`).

**IDENTITY.md.** The occurrence address `(r, c, i)`: region, causal context (Anchor, Root or
Lost) and execution index, and the scope-base rule. Endpoints and interaction ids, which pair a
send with its receipt. Node attribution (`runtime/Attribution`) and the thread and queue
lineage. The typed fault doors. The schedule: the `ScheduleEvent` kinds, and how
`runtime/ScheduleLog` records and enforces the order.

**CONTRACT-SPEC.md.** The session directory (`contract/SessionDir`): one file per row kind,
`expressions.jsonl` and `schedule.jsonl`. The row shapes, which `contract/RowCodec` encodes and
decodes. The IMPORT invariants checked by `contract/RowInvariants`. The gap registry
(`contract/GapKind`, `GapClass`).

**VM.md.** Covers:

- what the interpreter propagates: operand, local and heap shadows, calls and reflection;
- the library models (String, boxing, the modeled `java.util` containers, atomics);
- per-location version logs for shared state (`sharedFieldVersions`), with INITIAL and UNOBSERVED
  versions;
- the natives and shapes the VM publishes to Java (`runtime/ConcolicVmBroker`);
- export and attach of values;
- the known limits: where a value moves without a hooked bytecode.

**Reports.** `docs/reports/` holds dated experiment reports. They record what a run showed on
the day it ran. They are not a description of the current code.

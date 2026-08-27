# GraphChecker

> GraphChecker is an academic software-engineering and program-analysis
> project. It analyzes authorized, local, open-source workloads. HDFS key state
> is modeled only as abstract distributed coordination state; the project does
> not recover credentials or secret bytes.

## Milestone and current status

The current milestone is deliberately concrete:

```text
checkout: the Hadoop checkout carrying the Causynth commits
          (project_repo / CAUSYNTH_REPO; not /opt/hadoop, which has none)
workload: TestBalancerWithEncryptedTransfer#testEncryptedBalancer1
target:   HDFS-11741 / BlockTokenSecretManager.allKeys.get(keyId) == null
output:   a fresh generated candidate.smt2 and a captured Z3 result
```

The implementation must stay general. HDFS-specific endpoint recognition and
workload setup belong in the Hadoop adapter and `experiments/hdfs/hdfs-11741`;
the static analyzer, VM, relation model, scheduler, and Composer must not
contain an HDFS key-state formula.

As of 2026-08-24, there is **no accepted HDFS-11741 SMT artifact**. Existing
`candidate.smt2` files and old segment-era campaign directories predate the
current design or have unresolved lineage/coverage gaps. They are diagnostic
history and must never be resumed or imported into a fresh campaign.

The latest relevant evidence is narrower than a successful campaign:

- `campaign-run4` planned 103 legacy segment rows over 10 region templates and
  79 unique occurrence ids, but the selected target was not reached and no
  accepted composition/SMT/Z3 result was published;
- `campaign-run5` completed only its seed and legacy region-plan generation;
- fresh VM SASL attach evidence, the complete NN-to-Balancer cache relation,
  the later NN-to-DN heartbeat state without `K`, and the exact target map read
  are still missing from one frozen generation;
- the experiment now owns `loop-bounds.jsonl`, and `workflow.properties`
  routes it through the immutable campaign manifest; and
- the segment/re-pair/import-release/success-attestation and causal-graph
  parity-gate implementations have been deleted. Production searches in the
  P0 section below are currently zero-hit and must stay that way.

Recent source changes are newer than these artifacts. Do not use artifact
presence, a JUnit pass, or an old `sat` result as evidence that these gaps are
closed.

The Hadoop test class is runtime workload code only. It remains on the runtime
classpath for its manually added context, NameNode/DataNode initialization,
and workload APIs, but no test class enters Soot application scope, static
facts, communication discovery, or concolic instrumentation. No other Hadoop
unit test is relevant to this milestone.

## Takeover checkpoint: the 40-case RPC matrix

The small RPC workload and the HDFS-11741 workload serve different purposes.
The RPC workload is a bounded integration matrix for manually declared
sources, real MiniDFSCluster RPC, VM expression handoff, guarded producer
relations, case merging, and final Z3 output. HDFS-11741 is the milestone that
must connect several real HDFS state and communication transitions. Passing
the matrix is a regression prerequisite; it is not evidence that HDFS-11741
has been completed.

The checkpoint contains the original 20 producer pairs plus 20 deeper
DataNode-side pairs.  The second group adds nested control flow, De Morgan
forms, adjacent Java-width boundaries, cross-field affine relations, signed
and unsigned shifts, symbolic shift distances, bitwise complement, and local
boolean intermediates.  The checkpoint spans two repositories:

| Repository | Role |
|---|---|
| this GraphChecker checkout | static selection, instrumentation, concolic replay, case import, composition, solver reporting, experiment scripts |
| the Hadoop checkout named by `project_repo` | the two test RPCs, five manually declared DataNode source fields, MiniDFSCluster workload, HDFS-11741 source/target hooks, Hadoop IPC-header carrier, and encrypted-SASL carrier |

Neither is `/opt/GraphChecker` or `/opt/hadoop`: the first is an unrelated
project and the second is a stale Hadoop checkout with none of the Causynth
commits, so a run pointed at it compiles, passes, and answers about different
source.

### Fixed MiniDFSCluster RPC workload

The only matrix workload is:

```text
org.apache.hadoop.hdfs.TestCausynthRpcHeaderPropagation
  #nameNodeComparesValuesReadOnceFromTwoDataNodes
```

It starts one NameNode and two DataNodes. Cluster startup invokes
`NameNode.compareCausynthDataNodeValues` exactly once. The NameNode performs
two different RPC operations:

```text
DN0.getCausynthValueA() -> firstValue
DN1.getCausynthValueB() -> secondValue

if (firstValue > secondValue) {
  throw @CausynthExceptionTarget("causynth-rpc-compare") IOException;
}
```

Each DataNode declares the same five eligible fields manually. Runtime source
identity (`cluster0/dn0` versus `cluster0/dn1`), the RPC operation, and the
selected occurrence distinguish their uses; source names do not hard-code a
DataNode as “A” or “B”.

| Source ID | Java field | Type | Concrete default |
|---|---|---|---:|
| `RPC_COMPARE.A` | `DataNode.causynthRpcA` | `int` | `0` |
| `RPC_COMPARE.B` | `DataNode.causynthRpcB` | `boolean` | `false` |
| `RPC_COMPARE.C` | `DataNode.causynthRpcC` | `long` | `0` |
| `RPC_COMPARE.D` | `DataNode.causynthRpcD` | `int` | `0` |
| `RPC_COMPARE.E` | `DataNode.causynthRpcE` | `boolean` | `false` |

Declaring five eligible fields does not make all five symbolic in every task.
The selected producer output slice chooses only fields that can affect that
operation's return expression. Unused declarations stay concrete. Once a
source is selected, its exact declaration call, source phase, owner,
occurrence, Java field type, model write-back, and RPC handoff remain
fail-closed.

`DataNode.CAUSYNTH_RPC_SCENARIO` is intentionally a compile-time selector.
Changing it and incrementally recompiling leaves only one producer pair in the
analyzed call graph. It is experiment configuration, not a symbolic input.

### Scenario definitions and recorded results

All rows below were run as independent eight-worker fresh campaigns. The
selected run for each row published `FINAL_READY`, `SAT_CANDIDATE`,
`REACHABLE`, and zero final gaps. `candidate sha` is the first twelve
hexadecimal characters of that run's `candidate.smt2` SHA-256; it prevents an
old or duplicate directory from being mistaken for the selected evidence.

| # | Producer relation stress | Z3 models | fastest recorded SAT | candidate sha |
|---:|---|---:|---:|---|
| 1 | `int < MAX`, signed increment, and negative-`long` branch | 1 | 66 ms | `fe06267daff3` |
| 2 | exact `Integer.MIN_VALUE/MAX_VALUE` disjunctions | 1 | 91 ms | `b7bcaef456f1` |
| 3 | arithmetic relation guarded by `int && boolean` | 2 | 68 ms | `8f14b9e75950` |
| 4 | negation and `||`, with a different B-side relation | 4 | 118 ms | `8cdb922d9e8c` |
| 5 | two compound disjunctive producer cases | 2 | 59 ms | `23ab5134fa5b` |
| 6 | nested `||` groups under `&&` on both producers | 2 | 101 ms | `86deb5a4daec` |
| 7 | three-way conjunction and cross-field comparisons | 4 | 108 ms | `e6025430f69f` |
| 8 | boolean disjunction, equality, inequality, and negation | 10 | 170 ms | `3dd2b9864c43` |
| 9 | arithmetic guard sums plus `Integer.MAX_VALUE` arm | 1 | 102 ms | `6941c64b40ff` |
| 10 | three-level short-circuit condition with nested `||` | 2 (was 4 before EVENT-1; see below) | 86 ms | `d84793dc2dbf` |
| 11 | a `long` range strictly above `Integer.MAX_VALUE` | 1 | 72 ms | `7da8ec6a4186` |
| 12 | exact `Long.MIN/MAX` and `Integer.MIN/MAX` cases | 1 | 65 ms | `f4c68e0ab952` |
| 13 | mixed relational alternatives using all scalar types | 4 | 86 ms | `ca8b6ce771e5` |
| 14 | parity/bitwise predicates combined with booleans | 3 | 132 ms | `effed4ce5eda` |
| 15 | Java `int` overflow, including `MAX + 1 == MIN` | 1 | 97 ms | `9d463dbdf7c8` |
| 16 | Java `long` overflow, including `MAX + 1 == MIN` | 1 | 98 ms | `d858c5812c2f` |
| 17 | nested short-circuit alternatives on both producers | 15 | 167 ms | `d29d20923047` |
| 18 | three conjunct groups and a nested disjunctive B guard | 1 | 167 ms | `5b01fdf097a6` |
| 19 | multi-case `if / else-if / else` producer relations | 2 | 99 ms | `ad629902dfe8` |
| 20 | combined min/max, `&&`, `||`, negation, and multi-case arithmetic | 2 | 160 ms | `43500eb3e4c3` |

The deeper rows were also independent eight-worker fresh campaigns.  In
addition to the final solver result, `path-flip queries` counts the local
producer queries actually discharged as SAT or UNSAT before composition.  It
therefore distinguishes a deep relation test from a run that only solves the
NameNode comparison.

| # | Deeper producer relation stress | path-flip queries | Z3 models | fastest recorded SAT | candidate sha |
|---:|---|---:|---:|---:|---|
| 21 | bounded interval plus a real nested boolean branch | 7 | 4 | 104 ms | `6f4cbf4bc313` |
| 22 | De Morgan negation over compound `&&` / `||` guards | 6 | 2 | 96 ms | `da22867170cc` |
| 23 | adjacent `Integer.MIN_VALUE/MAX_VALUE` ranges | 8 | 8 | 91 ms | `1e6fa65df0fa` |
| 24 | adjacent `Long.MIN_VALUE/MAX_VALUE` ranges | 7 | 2 | 82 ms | `50ef41fe6cbb` |
| 25 | cross-field inequalities and mixed affine output | 9 | 2 | 106 ms | `dac166856a7b` |
| 26 | multi-level `if` control flow on both producers | 10 | 4 | 111 ms | `c3d6a14a2a5a` |
| 27 | affine difference/sum guards spanning `int` and `long` | 6 | 2 | 97 ms | `02097d4e9eb8` |
| 28 | exact cross-field affine equalities | 4 | 4 | 97 ms | `2ce473de033c` |
| 29 | staged long/int range partition with `else-if` cases | 11 | 4 | 110 ms | `cbcbb9f2a0f3` |
| 30 | Java `int` negation overflow and wrapped multiplication | 6 | 2 | 83 ms | `7eb825d2f70d` |
| 31 | Java `long` negation and multiplication overflow | 6 | 2 | 85 ms | `c621e4aa87a1` |
| 32 | several exact bit-mask predicates | 7 | 2 | 123 ms | `ef408fe65b02` |
| 33 | wrapped left shift and signed right shift | 6 | 4 | 99 ms | `4ab1129f5bdc` |
| 34 | Java `int` unsigned right shift in guards and outputs | 4 | 2 | 95 ms | `b080c955124e` |
| 35 | XOR/OR local values feeding guards and output relations | 6 | 4 | 330 ms | `c6cca8a7a328` |
| 36 | Java `long` unsigned and signed right shifts | 4 | 2 | 84 ms | `3ee91b2acbb1` |
| 37 | bitwise complement stored in local variables | 4 | 2 | 145 ms | `ada0ecdca2c3` |
| 38 | symbolic shift distance with Java distance masking | 4 | 2 | 183 ms | `7df082abc0ec` |
| 39 | local boolean intermediates over nested short-circuit logic | 12 | 4 | 116 ms | `f165a202dde8` |
| 40 | deep nested cases combining masks, boundaries, `>>>`, and affine outputs | 35 | 2 | 167 ms | `b70928c0978c` |

Scenario 34 exposed and then validated one general GraphChecker fix.  The
concolic VM serializes Java `iushr`/`lushr` as the expression-IR operator
`>>u`, while the local path-flip solver and final Composer originally accepted
only the Java source spelling `>>>`.  The first fresh run
`scenario-34.ecdtWf` therefore failed closed with
`UNSUPPORTED_EXPRESSION_IR`; it is not a passing artifact.  Both SMT consumers
now canonicalize the VM spelling, unit tests cover local solving and final
composition, and the selected fresh run `scenario-34.Ysb6Ec` has zero
unsupported flips and zero final gaps.

The selected local evidence is under:

```text
/proj/silentfailure-PG0/gc-rpc-compare/final-scenario-campaigns/
  scenario-01.oNndiJ
  ...
  scenario-20.Ihx2FP

/proj/silentfailure-PG0/gc-rpc-compare/new-datanode-scenario-campaigns/
  scenario-21.uQZFfE
  ...
  scenario-40.sR1cS5
```

These directories are diagnostic run products, not checked-in truth. A new
agent should use the committed workload and generate a new immutable root.

The matrix was reproduced in full on 2026-08-25 from a rebuilt toolchain — a
fresh Hadoop build, a rebuilt Zero VM, and the current `src/main/java` — under

```text
/proj/silentfailure-PG0/gc-rpc-compare/matrix/matrix-20260825T044357Z
```

All twenty rows published `FINAL_READY`, `SAT_CANDIDATE`, `REACHABLE` and zero
final gaps; `matrix-summary.json` records the per-row candidate digests. That
run is again a diagnostic product and not truth: it is cited here because it
establishes that the matrix reproduces, not so a later agent can import it.

Two observations from it are worth carrying forward. Nineteen rows reproduced
the Z3 model count recorded above exactly, which is a stronger signal than
`sat` alone — the count is a property of the composed formula, so matching it
says the composition is the same shape rather than merely satisfiable. Row 16
returned two models where one is recorded; both agree on every root and differ
only in `RPC_COMPARE.E`, a boolean that scenario's overflow relation never
constrains. A model count *above* the recorded one is therefore not a
regression. A count *below* it is the alarming direction, because that is what
an over-narrow case guard or a dropped control decision produces.

Row 20 also reproduced candidate digest `43500eb3e4c3` byte for byte. Do not
generalise from that: a fresh generation normally re-hashes, and nineteen rows
did.

Two things changed the matrix after that run, both worth knowing before
reading a later one against it. First, the RPC-1 follow-up in
`ConcolicSmtComposer.exactHandoffProducerCase` was changed to match a handoff
to its producer case on an `exportEventId` the importer never writes on
interaction rows (the field exists only on the VM handoff event); every
handoff then missed its producer and the whole matrix went to
`FINAL_REFUSED`, 0/20, without any test noticing because the fixtures had been
given the field. The port-observation match was restored the same day. Second,
EVENT-1 activates the session event ledger from selected event sites instead
of from the presence of a shared-state carrier, so RPC-only cases now record
their real `PROGRAM_ORDER`/`REGION` edges. Row 10 is the one row sensitive to
that: with the ledger live it records three more order edges and returns two
models instead of four — a strict subset of the earlier four, differing only
in an ordering the program never allowed. That is the "count below the
record" case the previous paragraph warns about, and it is the one legitimate
instance of it: the earlier four were recorded without the ledger. The table
above now carries the corrected count.

The reference run from here on is

```text
/proj/silentfailure-PG0/gc-rpc-compare/matrix/matrix-20260825T152212Z
```

built from the tree after the first reduction wave (86,102 nonblank lines in
`src/main`): 20/20, every row's set of symbolic variables
`(inputKind, sourceId, fieldSignature)` identical to `matrix-20260825T044357Z`,
and every model count identical except row 10 as explained.
`experiments/shrink/gate.sh --matrix <new> --baseline <this run>` is the
comparison to run after each later wave.

The second reduction wave was gated the same way on

```text
/proj/silentfailure-PG0/gc-rpc-compare/matrix/matrix-20260825T173609Z
```

(`src/main` 84,186 nonblank; rebuilt Zero VM with the propagated-expression
guard): 20/20, symbolic variable sets identical to the first-wave run on all
twenty rows, every row faster (−4.1% total wall time, PLAN within noise), and
two cheaper checks that now precede every matrix run — recomposing all twenty
`candidate.smt2` from their recorded inputs (`experiments/shrink/recompose-matrix.sh`,
20/20 byte-identical) and replaying all 175 recorded path-flip queries through
the solver (`experiments/shrink/replay-flips.sh`, 175/175 identical). Row 16
returned one model where the first-wave run had two; one is the recorded
count, and the two runs differ only in `RPC_COMPARE.E`, exactly as described
above — the row oscillates between one and two on that unconstrained boolean
and neither direction is a regression for it. This run is the baseline from
here on.

Reproduce with `experiments/hdfs/causynth-rpc-compare/run-matrix.sh`, which
leases one Hadoop worktree per lane rather than per row — only
`DataNode.CAUSYNTH_RPC_SCENARIO` changes between a lane's rows, so its Hadoop
rebuild stays incremental.

The solver report, rather than directory existence, is authoritative:

```bash
final='<fresh-scenario-run>/final'

jq -e '
  .finalStatus == "FINAL_READY"
  and .claim == "SAT_CANDIDATE"
  and .reachability == "REACHABLE"
  and .gapCount == 0
' "$final/result.json"

jq -r '
  .solverAttempts[]
  | "query=\(.queryOrdinal) strategy=\(.strategy)"
    + " status=\(.status) elapsed_ms=\(.elapsedMillis)"
' "$final/z3-result.json"

jq -r '
  .symbolicVariableModels[] as $model
  | $model.variables[]
  | "source=\(.sourceKey) variable=\(.sourceId)"
    + " phase=\(.sourcePhaseId) value=\(.value)"
' "$final/z3-result.json"
```

For example, the first recorded scenario-20 valuation includes independent
DN0 and DN1 roots and Java-width boundary values:

```text
cluster0/dn0: A=-2147483648, B=false,
              C=-9223372036854775808, D=-2147483648, E=false
cluster0/dn1: A=0, B=false,
              C=-4611686018427387929, D=-2147483648, E=false
```

Unlisted roots in another scenario retain their concrete defaults; they must
not appear as unconstrained symbolic variables merely because a Java hook was
declared.

One solver-performance distinction matters. For the original scenarios 1--20,
nineteen selected candidates returned `sat` with a plain Z3 replay within 15
seconds. Scenario 14's plain default-strategy replay exceeded 60 seconds,
while the exact tuned query recorded in `z3-result.json` returned `sat` in 132
ms. All selected scenarios 21--40 returned a recorded SAT attempt within 330
ms, but they were not separately audited under the plain default strategy.
Therefore acceptance uses the stored query digest, options, status, and
witness. Do not rewrite the claim as “the default `z3 candidate.smt2` command
is always fast.” The next Composer should emit the selected solver options
directly into the final SMT if a standalone default-strategy replay is
required.

To rerun the currently selected scenario 1:

```bash
cd <this GraphChecker checkout>
CAUSYNTH_RPC_SCENARIO=1 \
CAUSYNTH_RPC_HADOOP_ROOT='<Hadoop checkout carrying the Causynth commits>' \
CAUSYNTH_RPC_RUN_BASE='<fresh-output-root>' \
experiments/hdfs/causynth-rpc-compare/run-z3.sh
```

`CAUSYNTH_RPC_HADOOP_ROOT` defaults to the checkout beside this repository
(`../hadoop`) and `CAUSYNTH_RPC_PROTOC` to the pinned protobuf 2.5 compiler.

For scenario `N`, use an isolated Hadoop worktree, change only
`DataNode.CAUSYNTH_RPC_SCENARIO` to `N`, and pass both that worktree and `N` to
the command. `run-z3.sh` refuses a mismatch.
`experiments/hdfs/causynth-rpc-compare/run-matrix.sh` does that leasing for
every row. The setup stage incrementally
rebuilds Hadoop; it does not require a clean full Hadoop build for every row.

## Hadoop modifications that GraphChecker relies on

These modifications are experiment/runtime adapters. They identify sources,
targets, lifecycles, and concrete serialization boundaries; they must not
encode the HDFS-11741 SMT formula inside Hadoop.

| Hadoop location | Manual responsibility |
|---|---|
| `RpcHeader.proto`, `Client`, `Server`, `CausynthRpcWire` | carry `leafPath`, opaque expression handle/UID, and optional producer provenance in the real request/response header; there is no Java `OUTBOUND_LEAVES`/`INBOUND_LEAVES` re-pair map |
| `CausynthExchangeLifecycle`, `CausynthRpcTrace`, `ProtobufRpcEngine` | bracket the actual Hadoop call attempt, send, receive, retry, response, and failure events |
| `CausynthTraceContext` | register stable client/NN/DN identities, lifecycle epochs, aliases for service receivers, and one workload request context |
| `CausynthSymbolicSource` | optional reflection bridge for one exact manually declared field, selector lookup, and fail-closed source rejection |
| `DelegationKey` | declare `K` and the selected expiry fields; if modeled `K` changes, re-key the same object in its owning map and reject collisions |
| `BlockTokenSecretManager` | place the K/expiry source hooks at real key rotation/removal/install transitions and annotate the `allKeys.get(keyId) == null` throw |
| `TestBalancer` and `TestBalancerWithEncryptedTransfer` | register client, NameNode, DataNode, handler, heartbeat, and SASL receiver aliases at MiniDFSCluster construction/request boundaries |
| `BlockManager` and `HeartbeatManager` | expose the exact heartbeat owner/runnable only for test-side alias registration |
| `CausynthSymbolicHandoff` | optional reflection bridge from Hadoop to GraphChecker's VM-owned expression broker |
| `CausynthSaslHandoff`, `SaslDataTransferClient`, `SaslDataTransferServer` | correlate one concrete same-JVM encrypted-SASL connection, export the DEK fields, and attach them to the freshly parsed receiver carrier; malformed, duplicate, stale, or mismatched attempts fail closed |
| `DataNode`, `NameNode`, `MiniDFSCluster`, `ClientDatanodeProtocol*` | provide the two-operation RPC matrix and its single annotated comparison target |

The ordinary Hadoop behavior remains concrete when GraphChecker is absent:
the reflection bridges are no-ops, protobuf still carries the ordinary
application values, and the symbolic handle is opaque to Hadoop. The IPC
header carrier is appropriate to real Hadoop IPC. The SASL carrier currently
depends on MiniDFSCluster's same-JVM endpoints and must not be described as a
cross-process protocol.

## HDFS-11741 acceptance after the refactor

The refactor is successful only if it preserves the following three distinct
data/state paths and composes them into one bounded target witness:

```text
Path A: NameNode -> Balancer

NN future/current key K
  -> NamenodeProtocol.getBlockKeys
  -> VM VALUE_HANDOFF for the selected key component
  -> Balancer key state
  -> cached DataEncryptionKey DEK(K)

Path B: NameNode -> DataNode

NN allKeys version after rotate/remove(K)
  -> heartbeat KeyUpdateCommand / ExportedBlockKeys
  -> VM VALUE_HANDOFF for the selected allKeys component
  -> DataNode.addKeys
  -> exact DN allKeys version without K

Path C: Balancer -> DataNode target

cached DEK(K)
  -> encrypted SASL username/keyId
  -> VM VALUE_HANDOFF attached to the fresh parsed keyId carrier
  -> BlockTokenSecretManager.retrieveDataEncryptionKey(K, nonce)
  -> DN allKeys.get(K) == null
  -> @CausynthExceptionTarget("hdfs-11741")
```

The sparse causal order is mandatory:

```text
K is created and owned by the NN map
  < getBlockKeys exports K
  < Balancer caches DEK(K)
  < NN expiry/rotation removes K
  < a later heartbeat installs the DN version without K
  < Balancer reuses the cached DEK(K)
  < SASL attaches keyId=K on the DN side
  < the target lookup observes the selected DN map version
```

Symbolic propagation supplies the exact expression on each real handoff;
runtime tracing supplies source/occurrence/exchange identity and order;
producer path conditions state when each expression and state transition is
valid; symbolic merging selects mutually compatible cases. None of these can
be replaced by a concrete-value correlation or a free `hasK` Boolean.

### Required fresh artifacts and Z3 witness

Run only
`TestBalancerWithEncryptedTransfer#testEncryptedBalancer1`, with the current
Hadoop classes, private frozen GraphChecker JAR, VM, target spec, protocol
stubs, symbolic-input declarations, and loop-bound file in one new immutable
generation. Eight replay workers remain enabled.

The run is accepted only when all of the following hold:

1. Seed trace is `CLOSED`, runtime refinement is `COMPLETE`, and the selected
   NN producer, DN producer, Balancer/SASL handoff, and target goals are ready.
2. Imported relations contain exact evidence for
   `HDFS11741.NAMENODE.CURRENT_KEY_ID`,
   `HDFS11741.NAMENODE.SELECTED_KEY_EXPIRY`, and
   `HDFS11741.DATANODE.SELECTED_KEY_EXPIRY`.
3. The same symbolic K lineage crosses getBlockKeys, cached DEK, SASL keyId,
   and the target operand. The heartbeat path supplies the other target
   operand: the exact DN map/version.
4. NN, Balancer, and DN containers have distinct case-local owner identity.
   The formula contains recorded `put/remove/get` transitions, exact array
   cardinality, bounded loop-count vectors, and guarded read-from/version
   choices. A whole-map free symbol is not sufficient.
5. Every selected handoff has a successful VM attach and `VALUE_HANDOFF`
   event with matching endpoints, occurrence, and send-before-receive order.
6. The target assertion is the actual selected lookup nullness predicate, not
   a fatal-local fresh Boolean or an old handwritten expiry formula.
7. Composer publishes zero selected material gaps. Background/unselected
   coverage diagnostics do not enter the candidate, but any missing selected
   source, endpoint, array length, loop case, state version, or occurrence
   fails closed.
8. Z3 returns raw `sat`, `result.json` reports `SAT_CANDIDATE` and
   `REACHABLE`, and the recorded model is tied to the current candidate and
   composition digests.

At minimum, `z3-result.json` must publish model values for:

```text
K                         : Int32
NN selected-key expiry    : Int64
DN selected-key expiry    : Int64
```

The composition manifest must additionally name the selected NN removal,
getBlockKeys/cache, heartbeat/install, SASL, DN map-version, and target cases,
plus the partial-order edges above. A SAT assignment containing only a
NameNode-local or target-local variable is not an HDFS-11741 witness.

If final model write-back/replay is available after the refactor, replay the
published source assignment in a fresh cluster and confirm the selected
producer paths and handoffs. Until that materializer is complete, report the
result precisely as a bounded trace-grounded SAT candidate, not as a concrete
schedule-forced reproduction.

### Known takeover blockers

- There is still no final campaign for the current source generation.
  `campaign-run79` stopped after seed/planning, `campaign-run80` stopped after
  freeze, and the configured `campaign-run81` root was never produced.
- The concolic launcher passes test-only heartbeat-expiry, key-update, and
  test-wait system properties, but the Hadoop test currently does not consume
  those properties. Zero replay can therefore remove a healthy DN or time out
  because instrumentation is slow. Wire these properties into the fixed test
  after every cluster construction/restart before starting the next full run.
- Historical run74 is obsolete: it was `UNKNOWN`, timed out, had 759 gaps,
  and did not contain the current three HDFS-11741 source IDs. It is useful
  only for diagnosing array-cardinality, coverage, occurrence-prefix, and
  endpoint/order pressure.
- `workflow.properties` now names exactly one generation root
  (`causynth_output_dir`); the instrumented classes, runtime region plan and
  campaign root all derive from it, and the campaign root is
  `<causynth_output_dir>/schedule`. Change that one line, or override
  `CAUSYNTH_OUTPUT_DIR`, for each new generation; never resume an old plan,
  worker summary, candidate, or frozen JAR.
- The absolute paths this document once used are not the paths on this
  machine. `/opt/GraphChecker` is an unrelated project and `/opt/hadoop` is a
  stale Hadoop checkout with none of the Causynth commits. Read every path
  below as relative to this GraphChecker checkout, and take the Hadoop
  checkout from `project_repo`/`CAUSYNTH_REPO`.

The immediate post-refactor sequence is therefore:

```text
wire the test-only timing bridge
  -> run focused Hadoop hook/SASL tests
  -> freeze one new generation
  -> seed/refine/plan
  -> eight-worker replay and import
  -> inspect the three path closures
  -> compose and solve
  -> audit source/state/handoff/order lineage
```

### Refactor boundary for the next agent

The production Java tree is approximately 92,870 nonblank/comment-stripped
lines (100,913 physical lines). Reaching the 30,000-line target is not a
dead-code-only cleanup. It requires one internal causal IR and deletion of old
internal artifact compatibility:

```text
static target/source/endpoint slice
  -> typed causal plan
  -> selected runtime events and VM handoffs
  -> eight-worker replay adds guarded cases/topology delta
  -> one Composer builds SMT
  -> one solver runner publishes the decision and witness
```

Preserve annotated-target discovery, manual exact-source declarations, direct
VM propagation, the two RPC operations, eight-worker replay, bounded
case/topology refinement, exact state versions/read-from choices, and one
fail-closed selected-closure gate. Collapse the parallel recorded/canonical/
selected session models, duplicate planner/worklist/status layers, duplicate
JSON codecs, default full trace, default graph generation, and shell-side
semantic revalidation. Shared-field support remains bounded
observe-and-confirm; the refactor need not implement arbitrary scheduler
control.

The only final acceptance authorities should be:

```text
candidate.smt2
candidate_composition_manifest.json
z3-result.json
run-manifest.json
```

`result.json` may remain a human-readable index but is not a second authority.
Raw traces, per-worker plans/results, graphs, replay directories, and path-flip
queries are compressed debug/failure bundles rather than normal final output.
Do not weaken HDFS-11741's selected causal closure merely to meet the LOC or
artifact-size target.

## Design in one sentence

GraphChecker uses one concrete execution to obtain a failure-directed causal
skeleton, summarizes each selected **region occurrence** as guarded local cases
containing typed interaction events, propagates symbolic expressions directly
through the VM at real communication and shared-state operations, and uses
parallel concolic replay to add new cases or bounded topology before composing
the stable failure-relevant structure into SMT.

This is not whole-program symbolic execution and not exhaustive schedule
exploration. It is bounded, failure-directed, replay-guided causal refinement.

## Core model

### Four distinct levels

| Level | Stable identity | Meaning |
|---|---|---|
| region template | `regionId` plus selected production-code envelope | reusable code structure, selected branch/effect sites, typed ports, and loop descriptors |
| region occurrence | logical source identity, `regionId`, and one selected causal context | one bounded runtime activation chosen for the current immutable plan |
| local case | one normalized guard and its case-local effects | one concolic path through that occurrence |
| event instance | typed static site plus a case-local ledger reference | one RPC handoff, field/container access, return, throw, start/join, or synchronization event |

Raw thread ids, VM event ids, expression handles, exchange ids, source epochs,
request instances, and call ordinals are provenance inside one replay. They do
not identify a later replay. A configured request <em>API name</em> may narrow a
local task only when that scope is already active at the selected root entry;
an effect-local label is never copied onto a remote handler or a continuation
inside a long-lived service.
An occurrence that must be revisited is anchored by stable selected context,
such as its incoming causal event, rather than by “the 39th invocation in the
seed.” A case additionally records the loop-count vector observed by that
replay; the vector is case evidence, not occurrence identity.

### A region summary is a disjunction of guarded interaction cases

For region occurrence `R`:

```text
Summary(R) = OR case_k

case_k = guard_k
         AND selectedInputBindings_k
         AND typedEvents_k
         AND localPartialOrder_k
         AND outputExpressions_k
         AND terminal_k
```

The guard, event membership, event order, state transitions, outputs, and
terminal are all **case-local**. They must never be independently unioned at
summary top level. Otherwise a guard from one replay could incorrectly enable
an RPC or map mutation observed only by another replay.

For example:

```java
if (x > 0) rpcA(f(x));
else       rpcB(g(x));
if (y)     rpcC(h(x));
```

may produce:

```text
x > 0  AND  y  => [RPC_A(f(x)), RPC_C(h(x))]
x > 0  AND !y  => [RPC_A(f(x))]
x <= 0 AND  y  => [RPC_B(g(x)), RPC_C(h(x))]
x <= 0 AND !y  => [RPC_B(g(x))]
```

Concolic replay flips only selected failure-relevant branches. These four
paths merge as four guarded cases of the same occurrence. Their events do not
become one unconditional set.

### Region boundaries are coarse

A region begins at a selected execution-context entry and includes the
selected nested calls executed in that context. It is not split at every RPC,
field access, return from a callee, or transport callback. It ends at normal
return, throw, the target, or an explicit bounded-loop/output checkpoint needed
to terminate a long-running occurrence.

A synchronous RPC call does not split the client region into prefix and
continuation relations. The call is one guarded event in the client case. The
remote handler runs in another thread/source context and is therefore another
region occurrence. If the client later calls another RPC, both RPC events and
their local order remain in the same client case.

This deliberately trades a somewhat longer local replay relation for a much
smaller static catalog, task plan, instrumentation surface, runtime state
machine, and composition model. If storage checkpoints are ever needed for
performance, they remain an implementation detail and never become a second
semantic identity. Do not implement such checkpoints for this milestone.

## Symbolic propagation is the authority

### RPC and other explicit handoffs

The VM already provides the important operation:

```text
sender export(expression) -> live broker handle
receiver attach(handle)    -> receiver location denotes the same expression
EventLedger                 -> VALUE_HANDOFF(exportEvent, attachEvent)
```

After a successful attach, receiver arithmetic, branches, container accesses,
and later RPC exports naturally build on the sender expression. The Composer
does not need to rediscover which sender value reached the receiver.

The VM operation is the **single propagation authority**. The minimum checks
at this boundary are:

1. the symbolic session is current and the exported source has a symbolic
   expression;
2. the handle is live and each attach resolves it atomically under the broker
   lock, without racing release;
3. the destination owner/location is explicit and its symbolic sort, or an
   adapter-declared encoding transform, is compatible; and
4. successful attach records the exact export and attach events joined by one
   `VALUE_HANDOFF` edge.

Static `siteId`, port, direction, and leaf path describe the typed effect and
its relevance to the plan. The ordinary interaction trace may retain the
message correlation and request/response half needed to materialize observed
topology. The handoff bridge carries only the live handle; it does not copy a
runtime identity tuple into a payload, diagnostic schema, or second join
protocol.

The live adapter still has to carry the actual broker handle from the real
send to the real receive. It may use that message's in-memory exchange context
and typed leaf to select the handle. This ephemeral data-plane transfer is the
propagation itself; it is not a post-hoc Java/Composer pairing authority.

Therefore Planner/Importer/Composer must not:

- perform an export-by-receive Cartesian search;
- reconstruct a pair from `(site/slot, exchange, attempt, direction, leafPath)`;
- recover a leaf by terminal suffix, single-port shape, payload, FIFO, call
  order, concrete equality, or object identity;
- require a second “attested delivery” proof after VM attach succeeded; or
- introduce sender/receiver port values unrelated to the attached expression.

The VM should likewise delete exchange/attempt/leaf/direction identity matching
after handle lookup, duplicate pre-attach and in-lock matching, concrete
fingerprint/reference-shape revalidation, import/attach counters, and the Java
“import then confirm consumption” envelope. A unique live handle already names
the expression. Those checks reject valid symbolic alternatives without adding
lineage once the explicit destination and sort are known.

One exported expression may be attached at several explicit receivers. Each
successful attach records its own `VALUE_HANDOFF` edge. Do not infer
single-consumer semantics from an attach counter.

When serialized local terms need an explicit SMT equality, the endpoints come
directly from the VM `VALUE_HANDOFF` edge. Emitting that mechanical equality is
lowering, not a new matching decision.

### Shared scalar and container state

RPC propagation does not replace shared-state modeling. A shared read must
still use the exact selected runtime location/version and a bounded writer
choice. Equal field names, equal concrete values, or two objects of the same
class do not identify one state location.

Map-like containers are modeled by the VM's existing immutable container
relations and `ContainerSmtCodec`:

```text
M_0 = stateBefore
M_1 = put(M_0, k1, v1)
M_2 = remove(M_1, kr)
M_3 = put(M_2, k2, v2)
result = get(M_3, queryKey)
```

This is not a projection onto one distinguished key `K`. `put`, `remove`,
`clear`, keyed reads, size, and iteration relations remain in the symbolic
state. Z3 solves symbolic keys, values, guards, and the final lookup together.
The Composer may use an equivalent select-over-store `ite` lowering for a
keyed read, but it must not add a second `hasK` model or a supplied target-key
membership Boolean.

A read-from selector chooses which complete version reaches a read; it does
not choose whether a symbolic key is present. A final accepted model cannot
use an unknown writer arm.

## Loops

Loop identity is independent of the removed communication segments.

- An array-backed indexed `for` is fixed-count within one invocation. Record
  its exact dynamic cardinality `N`; different invocations may have different
  `N`, but Z3 may not invent another length for a recorded case.
- A `while` or other data/control-dependent loop has an explicit per-loop body
  bound `K_L`. Each replay records its observed count `k <= K_L`; behavior
  beyond the bound is outside the model.

For a replay case `c` containing condition-controlled loops:

```text
case_c = guard_c
         AND loopCounts_c = [(L_1, k_1), ..., (L_m, k_m)]
         AND recordedEffects_c
         AND recordedOutputs_c

0 <= k_i <= K_(L_i)
```

The VM has already executed all `k_i` bodies while constructing the case's
symbolic container/field/output expressions. Composer therefore consumes the
resulting expression DAG directly; it does not symbolically unroll the loop a
second time or create per-iteration RPC/state ports.

This matters directly to HDFS-11741. If one replay reaches a shared-state
output after two loop bodies and another after three, their recorded final Map
expressions belong to two different guarded cases with counts `2` and `3`.
SMT may select either complete case, but cannot combine one case's guard with
the other's Map value. A replay that needs more than `K_L` is a named bounded
coverage gap, not an accepted candidate.

The HDFS bound values belong in experiment configuration keyed by stable loop
sites. Remove HDFS measurements and HDFS-specific numeric rationale from core
classes. The current HDFS workflow binds the checked-in
`experiments/hdfs/hdfs-11741/loop-bounds.jsonl` file.

Generate the declarations only after the coarse static plan publishes stable
loop sites. The checked-in JSONL format is one row per selected
condition-controlled loop:

```json
{"loopSiteId":"<a.B: void run()>#u17","loopBodyBound":32,"reason":"bounded experiment rationale"}
```

Every failure-relevant while loop on the selected cache, rotation, heartbeat,
state-install, or target chain must have exactly one explicit `K_L`; no retained
condition loop may inherit the core default. `causynth_loop_bounds` is a
required workflow key for that reason: `run_engine.sh` refuses a configuration
that names no declarations file at all, because an unset key and a campaign
whose declarations never arrived are the same run at the inherited bound, and
the frozen manifest would carry an empty `loopBounds` digest rather than a
missing one. A workload that retains no condition loop still names a file --
one with no rows -- because "none" is a claim and silence is not. A declaration
for an absent/stale site is also an error. Fixed array loops do not use this file: their exact `N`
is frozen in the occurrence plan from the selected execution evidence.

## Guarded causal composition and refinement

Cross-region composition is event-level:

```text
VM_VALUE_HANDOFF(send, receive) -> same symbolic expression and send < receive
FIELD_READ_FROM(write, read)    -> selected version/value and write < read
THREAD_START/JOIN, monitor, ... -> required happens-before edge
```

Event existence is derived from cases, not asserted independently:

```text
exists(e) <-> OR(case_k contains e)
handoff(s,r) -> exists(s) AND exists(r) AND caseOf(s) AND caseOf(r)
exists(read) -> exactlyOne(known readFrom arms)
NOT exists(read) -> no readFrom arm
readFrom(w,r) -> exists(w) AND exists(r) AND writerCase(w) AND w < r
```

The target predicate is tied to the actual selected lookup/branch event. It
must never be represented by a free `exists_target` Boolean.

Within one composed same-session witness, all selected events share one
partial-order domain. GraphChecker does not enumerate total schedules. Two
executions that differ only in the order of independent events belong to the
same causal class. A replay is interesting when it changes event existence,
read-from, communication destination/source, region occurrence existence,
selected state, or failure-relevant order.

Raw ledger event ids are session-scoped. A causally dependent handoff is
recorded with both endpoint regions in the same worker session; import then
normalizes it to the planned occurrence/site/slot while retaining that session
as provenance. Never merge raw event ids or select a “largest snapshot” across
sessions.

The concrete seed is one observed skeleton, not the complete graph. Refinement
uses a small delta vocabulary:

```text
NEW_LOCAL_CASE
NEW_EFFECT
NEW_OCCURRENCE
NEW_CAUSAL_BINDING
TOPOLOGY_DIVERGENCE
COVERAGE_GAP
```

If a replay reaches another guarded combination of sites already declared for
the same occurrence/schema, including another bounded loop-count vector, add
a local case. If it reveals a new selected site, endpoint, source, occurrence,
or output schema, finish the current immutable iteration and rebuild the target
closure for the next one.
Do not mutate a running plan. Historical cases are immutable; failure to
observe an old edge in one replay does not delete it.

Convergence means that the bounded failure-relevant worklist has no new local
case or topology obligation, every selected input has one authority, and no
selected coverage gap remains. It does not mean the entire distributed system
has reached a global fixed point.

## General production flow

```text
target + production bytecode + fixed workload
                 |
                 v
       concrete seed causal skeleton
                 |
                 v
  failure-directed region/event/loop plan
                 |
                 v
     one union instrumentation pass
                 |
                 v
  same-JVM replay of dependent occurrences
                 |
                 v
  guarded region cases + VM causal evidence
                 |
         +-------+-------+
         |               |
  same topology      new topology/gap
         |               |
 parallel case work   next immutable plan
         |               |
         +-------+-------+
                 |
                 v
   typed state/event composition -> SMT -> Z3
```

The stages are:

1. **Seed.** Run the exact configured workload on a stock JVM and record one
   runtime causal skeleton.
2. **Slice.** Start from both target operands and retain only necessary local
   definitions/guards, typed communication sites, exact state accesses,
   compatible bounded writers, and loop controls.
3. **Plan.** Publish one immutable target-first plan with one task per selected
   region occurrence. Union all selected inputs, outputs, branches, event
   sites, state accesses, and bounds for that occurrence.
4. **Instrument once.** Rewrite the union of selected production methods/sites
   once. Test classes stay runtime-only.
5. **Replay.** Execute causally dependent region occurrences in one fresh
   workload JVM so real RPC/async handles and shared state remain valid.
6. **Import.** Project only selected branch witnesses, preserve case-local
   typed evidence, loop counts, and terminal/output completeness, and normalize
   transient ids to planned sites and occurrence context.
7. **Explore.** Generate branch flips only for unresolved failure-frontier
   cases and run independent obligations in parallel fresh workload instances.
8. **Refine.** Merge same-schema cases deterministically or publish topology
   deltas and rebuild the next immutable plan.
9. **Compose.** Combine selected case guards, VM handoff edges, read-from arms,
   final container expressions, loop-count-qualified cases, partial order, and
   target predicate.
10. **Solve.** Emit the composition manifest, `candidate.smt2`, Z3 result, gaps,
    and frozen provenance.

The runtime records only selected, bounded event schemas. A global ledger
capacity is a resource limit, not a semantic loop bound: truncation or domain
saturation of selected evidence is a named gap. It is never interpreted as an
event being absent.

## Parallel concolic replay

Parallelism is outside the semantic model. It accelerates independent replay
obligations without sharing mutable VM state.

Suppose the target slice needs:

```text
R1: cache path        branch flip A or B
R2: heartbeat writer branch flip C or D
R3: target lookup    branch flip E
```

If `R1` and `R2` communicate with `R3`, one baseline causal campaign runs the
dependent group in one JVM. After import, independent missing cases can run as:

```text
worker 1: fresh cluster, flip R1/A
worker 2: fresh cluster, flip R1/B
worker 3: fresh cluster, flip R2/C
worker 4: fresh cluster, flip R2/D
worker 5: fresh cluster, flip R3/E
```

Each worker receives the same frozen plan and union-instrumented class tree,
owns a private cluster/result directory, and emits one or more normalized
cases. Results merge by canonical case identity, never completion order.

If a replay obligation itself requires an RPC chain, all its interacting
client/server regions run together in that worker's workload JVM; it is not
split across workers. Topology-dependent iterations are sequential: all
workers for iteration `n` finish before a new plan for `n+1` is published.

The generic entry point remains:

```bash
./run_engine.sh --config <workflow.properties> campaign
```

`run_engine.sh` is the sole campaign owner. Preserve the existing external
worker pool (`concolic_worker_count=8` for HDFS), immutable iteration/worker
directories, one target-first parse, one union instrumentation pass, and
deterministic merge. Do not restore per-goal JVMs, scheduler subprocess loops,
or duplicate experiment orchestration.

## Minimal cross-stage contract

Do not introduce a universal event class or a second graph database. Keep the
existing typed RPC, shared-state/container, thread, loop, and order records;
their **membership is case-local**. Immutable expressions, container versions,
and ledger rows may remain once in a deduplicated evidence table; each case
holds typed event/version/edge references rather than copying the payload.

| Artifact | Minimum content |
|---|---|
| static catalog | production `regionId`; selected method envelope; branch/effect `siteId`; typed communication port/leaf/encoding description; selected state/container site; loop site/kind |
| occurrence plan | iteration/plan digest; `sourceKey`; `regionId`; stable causal occurrence selector; union selected demands; dependencies; per-loop bound/cardinality |
| raw region result | task/session identity; selected branch witnesses; case-local typed events and ledger edge references; input/output expressions; state/container transitions; loop-count vector/cardinalities; terminal; gaps |
| imported summary | one occurrence/schema plus `OR(cases)`; every case keeps its own guard, events, order, state versions, outputs, terminal, and evidence references |
| topology delta | frozen plan reference; normalized observed site/occurrence/schema; delta kind; evidence reference or named gap |
| composition manifest | one source row for every selected guard, expression root, VM handoff edge, read-from arm, state transition, loop-count-qualified case, order term, and target assertion |
| campaign manifest | source/JAR/VM/config/target/adapter/loop-bound/plan digests; selected production-class digests; exact runtime workload-test class/classpath digest; worker/iteration lineage |

Only one layer owns each essential check:

| Invariant | Sole owner |
|---|---|
| selected site belongs to a concrete production method | static planner/instrumentation selection |
| live symbolic handle attaches to an explicit compatible location | VM broker |
| loop kind and bound/cardinality are declared | occurrence plan and bound hook |
| raw case belongs to its task and has required terminal/outputs | importer |
| every selected SMT input has exactly one authority | Composer acceptance gate |
| artifacts come from one frozen generation | campaign manifest |

Do not repeat these checks in every later layer. A check with no effect on
symbolic correctness, selected causal lineage, bound enforcement, or artifact
generation integrity is legacy and should be removed.

## What must be retained

The redesign must preserve the optimizations and working semantic components:

- production-only Soot scope and runtime-only Hadoop test classes;
- target-directed static selection, compact reverse indexes, lazy method-body
  fact construction, and existing static-analysis speedups;
- direct communication call-site/typed-port discovery and configured Hadoop/
  SASL adapter descriptions;
- one campaign-wide instrumentation union and exact selected site filtering;
- one VM symbolic session per workload, thread-local execution state, the
  expression broker, and the single event ledger;
- VM scalar/container versions, associative/indexed state relations, and
  `ContainerSmtCodec`;
- selected branch instrumentation, CFG backedge bounding, exact array
  cardinality, target/output capture, and named gaps;
- target-first scheduling, immutable iteration lineage, external worker
  parallelism, and deterministic merge; and
- every executed writer of a declared shared field or container recorded as
  a version, so a read's writer arms are the session's real writes (bounded
  by declared fields × executed writes, not by planned producers), and the
  sparse causal partial order that decides which arms are admissible.

After P0, remeasure static analysis. Do not restore the full test tree,
duplicate full-fact indexes, whole-program eager body loading, per-task
instrumentation, or per-event durable diagnostic I/O. Performance comparison
uses frozen runs or git history, never a live compatibility implementation.

## P0 complete: keep the legacy design deleted

The migration below is complete in production code. It is a permanent
tombstone, not an invitation to restore a compatibility reader. Any future hit
must remove the producer, consumer, fallback, schema field, fixture and
generated-artifact assumption together before another HDFS campaign.

| Area | Delete | Keep/update |
|---|---|---|
| static communication | The communication-free CFG-window construction in `CommunicationSegmentPlanner`; `CLIENT_PREFIX`, `CLIENT_CONTINUATION`, `SERVER_SEGMENT`; continuation NORMAL/THROW/UNWIND entry/terminal rows; `communication_segments.jsonl.gz` | retain direct `CommunicationCallSite` discovery, typed ports/full adapter leaf description, and static communication gaps; publish sites in the region template catalog |
| contracts | delete `CommunicationSegmentContract` and `SegmentInstanceId` after moving only typed port fields to the call-site catalog and loop fields to the loop contract; remove `segmentKey`, `producerSegmentKey`, segment `semanticOccurrenceId`, continuation/live-across schema from `RegionInstancePlan` and `ExecutionTask` | one region-occurrence identity; case-local typed event references and loop-count evidence |
| runtime planning | delete `CommunicationSegmentIndex`; remove `RuntimeRegionPlanner` segment rows, route/window ownership, prefix/continuation grouping, segment cursor/stamp/gaps, and segment special cases in `SymbolicRegionPlanner`/`RuntimeSelectedRegionFinalizer` | use existing catalog maps for static interaction-site lookup; union all selected demands for one occurrence into one task; retain occurrence, exact state owner/version, dependencies, bounds, and target closure |
| scheduling | prefix/continuation goal kinds and paired tasks in `RuntimeWorkflowDiscovery`, `ConcolicScheduler`, and `RegionPathWorklist`; segment fields in schedule indexes and shell sort keys | schedule region occurrences and their branch-case obligations; keep dependent occurrences in one worker workload |
| instrumentation | segment boundary parsing/validation in `ConcolicInstrumentationSelections`; entry/successor/handler/unwind open/seal hooks in `CausynthPipeline` | one region enter and normal/throw/target/bound exit plus selected branch, RPC, state/container, loop, output, and target hooks |
| Java runtime | `ConcolicRegionRuntime.SegmentActivation`, member cursor, pending continuation, live-across settlement, frame join, `openSegment`, `sealSegment`, exact continuation-boundary APIs, and segment-window gaps | one active region occurrence/result per planned task; case-local selected evidence and terminal/output capture |
| VM runtime | segment frame/watermark machinery in `threadContext`, segment JNI exports, and `expressionBroker.cpp` sealing a frame on export | broker publish/resolve/attach, shared symbolic heap, region context, container semantics, CFG bound hooks, and `EventLedger.VALUE_HANDOFF` |
| RPC evidence | delete `RecordedRpcHandoff` and the pairing/model role of `RpcExpressionHandoff`: export×receive pairing, wildcard identity agreement, tuple narrowing, delivery ordinal recovery, and fallback matching | retain only a generic runtime VM-call bridge if the ABI needs one; it returns VM status and exact event ids, while the session ledger serializes `VALUE_HANDOFF` once; the bridge owns no edge artifact or pairing schema |
| import/summary | segment path-condition windows, cross-segment merge refusal, continuation-only relation role, full-path compatibility fallback, and top-level union of `recordedRpcHandoff`/`recordedSharedState` in `PathObservation`, `ConcolicSummaryImporter`, and `RelationSummary` | project selected branch witnesses for the whole occurrence; move typed RPC/state/order evidence and loop-count vector into each guarded case |
| composition | `SegmentComposition`, continuation port equality, segment identity lowering, tuple-based handoff lookup, duplicate send/receive attestation gates, and synthetic per-iteration loop ports/state in `ConcolicSmtComposer` | consume case-local VM handoff edge references, state read-from choices, final container expressions, loop-count-qualified cases, partial order, and target predicate directly |
| artifacts/tests | legacy segment JSON fields, generated segment plans/summaries, segment golden fixtures, and tests whose only purpose is preserving those schemas | compile/smoke checks may cover the minimal retained VM/container contracts, but only the fixed HDFS workload is milestone acceptance |
| orchestration/gates | shell re-decoding of Java closure/output/terminal schemas; repeated scheduler filters; `member.tsv`; acceptance of old selection authorities; global telemetry-as-gap; causal-graph parity as an SMT gate | shell validates immutable paths/digests/task-set membership and launches stages; importer owns case admission, Composer owns final selected-input admission; graph output was removed outright in the second reduction wave (2026-08-25: `CausalGraphWriter`, `campaign_graph()`, `graph/causal_model.json`) — `canonicalModel` in the composition manifest keeps only `gaps` and the six `counts.*` that `run_engine.sh` reads |

Also keep the following compatibility residue deleted:

- duplicate identity/alias fields and their readers, including any reintroduced
  `relationContractHash`, nested `contractHash`, scalar fatal-prefix fallback,
  or `WORKLOAD_FALLBACK` path;
- per-event durable `CONCOLIC_HANDOFF_UNATTRIBUTED` logging and diagnostics that
  do not change a selected correctness decision;
- object-token, concrete-value, payload, FIFO, source-kind, terminal-leaf,
  single-port, and global-ordinal inference;
- old discovery/scheduler CLI paths and shell orchestration duplicated outside
  `run_engine.sh campaign`;
- HDFS-specific constants/rationale in core loop or composition classes; and
- code and fixtures for unsupported recursion or compatibility schemas that no
  selected production workload consumes.

In `run_engine.sh`, also remove the per-campaign source-code legacy grep (make
it a one-time cleanup/CI command), the second manually filtered scheduler pass,
shell `target-admitted`/`relation-complete` semantic reconstruction, duplicate
membership TSV, and old authority alternatives. A skipped or incomplete task
must reach the importer/classifier as a terminal gap/delta; shell must not kill
the iteration before the semantic owner can classify it. Only blockers inside
the frozen selected target closure affect acceptance. Unselected VM/catalog
telemetry remains diagnostic.

The old `artifact-provenance.sh` schema parser is gone (it no longer exists in
the tree); `campaign_freeze` emits every source/JAR/VM/config/production-class/
loop-bound digest into `campaign_provenance`, bound into `iteration_manifest.json`,
`run-manifest.json` and `result.json` — one provenance authority. In the third
reduction wave the shell also stopped re-decoding the Composer's and solver's
document schemas at EMIT: the Composer now owns `candidate_composition_manifest.json`'s
`schemaVersion`/`kind` tripwire, and `result.json` carries `freeSymbolCount` read
from the manifest's `freeSymbols` (fail-open: reported, never a refusal).

These searches are the zero-hit guard:

```bash
rg -n 'communication_segments|CommunicationSegmentContract|CommunicationSegmentIndex|SegmentInstanceId' src/main/java
rg -n 'segmentKey|semanticOccurrenceId|CLIENT_PREFIX|CLIENT_CONTINUATION|SERVER_SEGMENT|LIVE_ACROSS_LOCAL' src/main/java
rg -n 'RecordedRpcHandoff|matchedPair|recordedRpcHandoff' src/main/java
rg -n 'OPEN_PLANNED_SEGMENT|SEAL_PLANNED_SEGMENT|CONTINUATION_PORT_EDGE_KIND' src/main/java
rg -n 'System\.(importExpression|releaseExpression)|VM_RPC_EXPRESSION_HANDOFF_ATTESTATION|CausynthPayloadLeaves' src/main/java third_party/OpenJDK-Concolic-Execution-Engine
rg -n 'CausalGraphParityAudit|parityAudit|EXPRESSION_HANDOFF_EQUALITY' src/main/java
```

`VALUE_HANDOFF` should remain only in the VM/runtime ABI, one-time ledger
admission, case evidence, and its direct Composer consumer. It must not feed a
Java export/receive pairing index.

## Required updates and known correctness bugs

Implement the remaining items directly on the retained coarse model. Do not
build parallel old/new models.

| ID | Required change | Acceptance condition |
|---|---|---|
| `CASE-1` | Move RPC, state/container, order, output, and terminal evidence into each `RelationSummary` case. | No case guard can enable an event/version observed only by another case. |
| `RPC-1` | Make successful VM attach plus its `VALUE_HANDOFF` edge the only symbolic handoff authority; remove Java re-pair. | Receiver expressions descend from the sender expression; Composer performs no tuple search or fallback. |
| `REGION-1` | Collapse all prefix/server/continuation fragments of one local occurrence into one coarse occurrence task/result, while remote handlers remain their own occurrences. | One occurrence has one guarded summary and union demand schema; multiple RPC sites appear as guarded events. |
| `OCC-1` | Replace raw nth-invocation replay addressing with a stable selected source/region plus incoming causal anchor. Treat each target occurrence as a candidate. | Replays select the intended occurrence even when another branch creates/removes earlier activations; ambiguity is a named gap. |
| `PC-1` | Import only selected failure-slice branch witnesses for the whole occurrence. Delete segment windows and full ambient-PC fallback. | A case guard contains the relevant decisions and nothing from transport/startup noise. |
| `ORDER-1` | Preserve the case-local projection of VM ledger events/edges and normalize only their planned sites and occurrence context. | RPC, read-from, synchronization, and region order share one acyclic partial-order domain; no total schedule or second event graph. |
| `STATE-1` | Keep exact owner/location/version and case-local container mutation chains; materialize only target-demanded bounded writer cases. | NN, Balancer, and DN maps never merge by field name/value; accepted reads select a known complete version. |
| `LOOP-1` | Detach loop discovery/bounds from segment planning; create experiment-owned HDFS bound declarations; preserve each replay's loop-count vector and exact array cardinalities with its guarded final expressions. | Fixed arrays use exact per-invocation `N`; while-loop output comes from the matching replay count; no synthetic loop state or over-bound case is accepted. |
| `EVENT-1` | Activate the ledger from selected event sites, not from the presence of a shared-state carrier; record case ownership and exact handoff endpoints; keep raw order session-scoped. | RPC/SASL-only cases retain their edge; no cross-session event-id/snapshot merge; selected ledger truncation/saturation is a gap. |
| `READ-1` | Guard read-from choices and writer cases by exact event/case existence rather than emitting one unconditional exactly-one set per task. | A missing read has no arm; a selected arm implies its exact writer and reader cases and order. |
| `TARGET-1` | Bind target existence and predicate to the selected concrete lookup/branch event. | Missing target-event evidence fails closed; `exists_target` cannot be freely set true. |
| `TERM-1` | Finish a coarse occurrence only at its real terminal or after all demanded event/output frontier items settle. Remove first-output completion and deferred-target terminal rewriting. | A case cannot omit later required RPC/state/throw effects merely because an earlier output was captured. |
| `GRAPH-1` | Compare normalized case schemas/effects with the frozen plan and publish a small topology delta. | Same topology adds a case; new site/endpoint/source/occurrence/slot/schema starts the next immutable iteration. |
| `SMT-1` | Build one selected-input ledger before writing SMT. Each selected value must be a local symbolic root, VM handoff result, or known read-from arm. | No free selected port, unknown writer, supplied map-membership fact, stale generation, or unresolved selected gap reaches `candidate.smt2`. |
| `GATE-1` | Make Composer publish the sole `FINAL_READY` decision and selected blockers. Shell must not report `SAT_CANDIDATE` from reachability alone or reconstruct legacy trust states. | Acceptance requires current frozen provenance, ready Composer status, complete selected witness, zero selected blockers/candidate/unknown arms, and a parsed Z3 SAT result. |
| `PERF-1` | Preserve production-only/lazy static analysis, delete segment computation and duplicate unconsumed indexes, union-instrument once, and run independent replay obligations in the existing worker pool. | Static analysis does not regress from the optimized path; no per-goal analysis/instrument/JVM loop returns. |

The validation rule is intentionally small: validate once where an invariant is
created, then pass the result forward. Do not add a new attestation layer to
replace a deleted one.

## HDFS-11741 under the general model

The fixed workload supplies a real MiniDFSCluster, Balancer, Hadoop RPC,
heartbeat, and data-transfer SASL execution. The test may pass concretely. The
model searches bounded alternatives needed for this causal shape:

```text
NN key state --getBlockKeys--> Balancer key state --cache DEK(K)--+
                                                               |
NN key state --heartbeat response--> DN key state              |
       |                                                       |
       +--later rotation/removal and heartbeat without K        |
                                                               v
Balancer cached DEK(K) --SASL HANDSHAKE/keyId--> DN target lookup
                                                    allKeys.get(K) == null
```

NameNode, Balancer, and DataNode own distinct maps. Only recorded RPC/SASL
handoffs and selected state transitions connect them.

The witness must also enforce the sparse causal order:

```text
initial K
  < Balancer cache write of DEK(K)
  < NN rotate/remove K
  < later heartbeat installs DN state without K
  < Balancer cached reuse of DEK(K)
  < SASL handoff of keyId=K
  < DN target lookup
```

Lineage without this order is not an HDFS-11741 witness.

The fresh run should proceed as follows:

1. Verify the P0 zero-hit guard and freeze the GraphChecker JAR, rebuilt Zero
   VM, production classes,
   target specification, adapter catalog, loop-bound declarations, and exact
   workload command.
2. Record one stock-JVM execution of only
   `TestBalancerWithEncryptedTransfer#testEncryptedBalancer1`.
3. Slice backward from both operands of `allKeys.get(keyId) == null`:
   `keyId` through the SASL `HANDSHAKE/keyId` handoff and cached DEK, and
   `allKeys` through the exact DN map/version, DN key installation, heartbeat
   response, and upstream NN state. Retain NN-to-Balancer `getBlockKeys` too.
4. Publish one coarse target-first occurrence plan and union-instrument its
   selected production methods/sites once.
5. Run a baseline causal replay. At each real RPC/SASL boundary, VM export and
   attach propagate the live expression and record `VALUE_HANDOFF`. At each
   selected map operation, the VM records the full symbolic state transition.
6. Import guarded region cases. For a function containing several alternative
   RPC sites, branch flips add cases with different guarded event lists; they
   do not create client prefix/continuation segments.
7. Schedule only unresolved failure-frontier cases in parallel fresh clusters:
   early DEK caching, expired cached reuse, NN rotation/removal, heartbeat
   installation without the old key, required while-loop counts, and the target
   null branch. Keep each causally dependent RPC group in one worker JVM.
8. If replay reveals a new relevant occurrence/site/slot, finish the worker
   wave, publish `TOPOLOGY_DIVERGENCE`, rebuild the target closure, and repeat.
9. Compose the selected case guards, VM handoff edges, complete NN/Balancer/DN
   container histories, known read-from arms, loop-count-qualified cases,
   sparse partial order, and target predicate.
10. Emit a fresh manifest-bound `candidate.smt2`, run Z3, and retain either the
    accepted bounded witness or an exact named gap.

The relevant SMT shape is illustrative, not a handwritten replacement:

```text
BalancerKeys = VM_handoff(getBlockKeysResult)
DEK          = cacheCase(BalancerKeys, K)

NN_(i+1)     = rotateOrRemoveCase_i(NN_i, K)
DN_(j+1)     = heartbeatCase_j(DN_j, VM_handoff(NN_(i+1)))

SaslKey      = VM_handoff(DEK.keyId)
TargetValue  = get(DN_(j+1), SaslKey)
TargetValue  = null
```

Every term must point to an imported case and VM/state evidence in the
composition manifest. Z3 chooses symbolic `K`, guards, known writer arms, and
bounded loop exits. It does not choose an unrecorded communication pairing or
an abstract `hasK` fact.

## Ordered takeover plan

1. **Keep P0 at zero hits.** Never restore the segment/re-pair chain or its
   tests/readers; do not spend time fixing deleted continuation-window bugs.
2. **Publish the coarse contract.** Make one occurrence task/result and
   case-local typed evidence the only schema. Update all producers/consumers in
   the same changes; no compatibility schema.
3. **Simplify instrumentation/runtime.** One region lifecycle, selected sites,
   direct VM handoff, state/container hooks, loop bounds, outputs, and target.
4. **Simplify import/composition.** Guarded whole-occurrence cases, VM-edge
   handoff lowering, exact versioned state/container composition, and the
   selected-input gate.
5. **Update scheduling/parallel replay.** Region-case obligations rather than
   segment tasks; retain target-first immutable plans, one union tree, worker
   isolation, and deterministic merge.
6. **Verify HDFS experiment inputs.** Keep the checked-in per-loop bounds and
   workflow binding, then verify the two end-to-end communication/state chains
   and exact DN target map owner in a new seed plan.
7. **Run the fixed workload.** Use a new campaign root; never import a legacy
   segment artifact. Iterate until the bounded failure frontier is stable or a
   named gap remains, then compose and solve.

After removing segmentation/live-across replanning, remeasure
`SeedBackwardStaticAnalyzer.buildGlobalStaticIndex()`. It currently performs a
full application-method/body pass when a writer/caller demand first triggers
it. If it remains the measured static bottleneck, replace only those triggers
with demanded-field/callee reverse lookup. Do not combine this milestone with
a new whole-program analysis framework.

Compilation and focused smoke checks are useful engineering checks, but they
do not define the workload or justify retaining legacy fixtures. The only
milestone acceptance run is the fixed HDFS workload.

## Reduction plan: src/main to 30,000 lines

This section is the execution plan for the 30,000-line target stated under
"Refactor boundary for the next agent". It was written on 2026-08-25 from a
measured inventory, not from impression, and it is ordered by what the
inventory found. Priority order for the work is: **shrink first; the 20-row
RPC matrix must stay 20/20 after every wave; HDFS-11741 runs last** as the
final acceptance, not as a per-wave gate.

### Metric and gate

Two counts, both reported by `experiments/shrink/gate.sh --count-only`:

| metric | 2026-08-25 | target |
|---|---|---|
| `src/main` nonblank lines (comments included) | 97,810 | 30,000 |
| `src/main` code-only lines (comments stripped) | 82,131 | 30,000 |

The earlier 92,870 figure in "Refactor boundary" was counted with a different
stripper; the gate's counts are the reference from here on. `src/test` is not
counted, but tests that exist only to pin deleted code are deleted with it.

One gate per wave, run once after the whole wave lands — never after each
small cut: `experiments/shrink/gate.sh --matrix <matrix-root>` = P0 tombstone
zero-hit, compile, the unit suite, and 20/20 in `matrix-summary.json` from a
fresh `experiments/hdfs/causynth-rpc-compare/run-matrix.sh`. A failed gate is
bisected over the wave's diff, not answered by smaller waves.
`experiments/shrink/scan/run_all.sh` re-measures dead/test-only/shim/duplicate
helper lines in ~70 s and is re-run after each wave.

### What the inventory found

A javap-validated liveness scan over all 127 files, plus five per-package
inventories, agree on one fact: **only ~1.4% of `src/main` is dead or
test-only**. Unreferenced members total 198 lines; test-only-reachable code
1,157; delegate-only shims 882; duplicated private JSON helpers ~400 (302
removable); comment-only lines 15,679 (16%). No schema-compatibility reader
branches exist at all — every `SCHEMA_VERSION` reader is a strict equality
against the value the writer emits.

The bloat is structural. The top 15 classes hold 65,883 lines (67%); 32
methods over 150 lines hold 7,532. The same shape is implemented in parallel:
`ConcolicConstraintSolver.Encoder` and `ConcolicSmtComposer.Emitter` carry a
parallel `binary` (241/239 lines), parallel anonymous `ContainerSmtCodec.Host`
implementations (197/198), and 298 byte-identical operator-helper lines;
`RuntimeRegionPlanner` has five `*OutputClosure` methods over 150 lines each;
`ConcolicRegionRuntime` runs the same commit/validate/publish lifecycle four
times (map, field, source symbol, selector value; token similarity 0.95–0.98),
keeps seven parallel gap ledgers, three result envelopes, and a 625-line
reflective table for 32 VM entry points; `CausynthPipeline` emits the same
eight Jimple hook families twice (discovery trace vs replay region);
`SeedBackwardStaticAnalyzer` has five caller expanders and six propagation
walks on one skeleton; `RuntimeSelectedRegionFinalizer` and
`SymbolicRegionPlanner` contain thirteen identical deque-BFS drivers and eight
rebuilds of the same adjacency index; 69 hand-rolled index builds recur across
57 methods. Per-slice deletion ceilings were measured at 14–16%.

Therefore the plan is three waves of increasing depth, and the third is the
rewrite the "Refactor boundary" section already calls for.

### Wave 1 — mechanical (in flight; budget ≈ −15,000)

Five lanes partitioned by file, one executor each, one gate at the end.
Every item has file:line evidence in the inventory.

| lane | files | budget | content |
|---|---|---|---|
| runtime | `ConcolicRegionRuntime`, `CausynthTraceRecorder`, `RuntimeTraceContext` | −3,400 | dead members; 22 EngineApi forwarders + 19 single-caller wrappers + 6 default-argument overloads; `*ForTests` entry points whose tests can assert through a real path; seven gap ledgers → one kind-keyed ledger; six occurrence counters → one; three result envelopes → one; the four-fold lifecycle → one parameterised; recorder Lite/full → one; `FlatJsonRow` → Gson; runtime copies of contract-owned validations; Javadoc capped at one third |
| contract | `contract/**`, `launcher/**`, `concolic/JsonFields` | −2,000 | dead members and write-only fields; duplicate validations (keep the decode point); `declaredOutputPorts` dual wire shape → one; `LoopBoundPolicy` constant-only fields and two-shape writer → one; `junitFailure` stack scraper + its 448-line test; `launcher-outcome.json` serialized duplicates; 27 private JSON helper copies → `JsonFields`; Javadoc capped |
| static | `causynth/**`, `option/analysis/util/transformer`, `GraphCheckerMain` | −3,000 | trace-skip knobs never set; three delegate `finalizeRegions`; the finalizer gap channel whose only artifact nobody reads; `CampaignEnvelope` report with zero consumers; 18 write-only region/edge keys; helper copies → one `MapFields`; 4 signature regexes, 8 hierarchy walks, 6 body loaders, 7 ad-hoc hook refs → one each; the one-transform plugin registry (235 → 35); 13 BFS drivers → one; 4 callee/field resolvers → one; Javadoc capped |
| smt | `ConcolicSmtComposer`, `ConcolicConstraintSolver`, `ContainerSmtCodec`, `TargetReachPathQueryBuilder`, `BooleanReachConditionExtractor`, `RecordedSessionModel`, `CanonicalSessionModel`, `RecordedReadFrom`, `SharedStateEvidence` | −3,800 | dead `edgeEvidence` cluster; manifest members nobody reads (`droppedEdgeEvidenceAudit`, `fatalAbsenceMutationWitness`, `finalStatusEvidence`); 13 delegating overloads; test-only seams; `recorded == null` fallbacks (compose always sets it); legacy unscoped-name passes; composer re-validation of the query the builder just built; five derivable read maps; `CanonicalSessionModel` 780 → a `counts()` (its only contractual consumer is `canonicalModel.counts`); `CaseLocalLetCse` 351 (a pure size optimisation of `candidate.smt2`); Javadoc capped |
| planning | `RuntimeRegionPlanner`, `RuntimeRefinedGraphBuilder`, `ConcolicScheduler`, `RuntimeWorkflowDiscovery`, `RegionPathWorklist`, `ConcolicSummaryImporter`, `TopologyDelta` | −2,700 | 14 delegating constructors/overloads no production caller uses; orphan reads of ten fields no writer emits; a refusal that guards a provably impossible state; the non-target-first `schedule()` path `run_engine.sh` never takes; second `Map` row reader → one `RuntimeRows`; two number-folding copies → one; six typed audit ledgers → one `notes` array; duplicate phase-observation decode in the importer and topology delta; Javadoc capped |

Comments are roughly 8,000 of the 15,000: behaviour-free, but they are in the
count the owner reads. The per-slice deletion ceilings (6–20%) are the reason
wave 1 cannot be larger; everything past it is a merge.

### Wave 2 — in-file parallel implementations (budget ≈ −8,000 to −10,000)

Merges whose two halves live in one file or one package, so the 20-row matrix
alone can catch a regression:

- **SMT**: one operator/term lowering shared by `ConcolicConstraintSolver` and
  `ConcolicSmtComposer` (`binary`, `ContainerSmtCodec.Host`, the identical
  helper block); one emitter per SMT construct; readers of fields no writer
  emits (P0 leftovers) deleted.
- **runtime**: map/field/element planned admission → one, keyed by the
  existing `SharedCarrier.shape`; the 32-entry reflective table → one map;
  the eight materialize/symbolize hook bodies → one matcher behind the fixed
  hook signatures.
- **static**: the eight discovery/replay emitter pairs → one emitter per hook
  family (prerequisite: every hook ref through `HookCatalog`); natural-loop
  derivation in `CausynthPipeline` → consume `CfgLoopControl.LoopCfg`; the
  five caller expanders and six propagation walks → one, preserving FIFO
  dequeue order so `DF.<n>` edge ids stay stable.
- **planning**: the five `*OutputClosure` shapes in `RuntimeRegionPlanner` →
  one; the 69 index builds → indexes built once per artifact.

This wave changes bytecode the matrix executes; the gate's 20/20 with the
recorded Z3 model counts is the acceptance.

### Wave 3 — one causal IR (budget: the remaining ≈ −50,000)

Waves 1–2 land at roughly 75,000. The rest is not a cleanup; it is the
"Refactor boundary" rewrite, and its design center is a decision taken on
2026-08-25 that takes "Symbolic propagation is the authority" literally:

> **Every occurrence of a declared field is its own symbolic variable.** Each
> entry of a mint site mints a fresh symbol. At a read, if the value the VM
> holds carries a symbolic expression — propagated through the heap or a
> `VALUE_HANDOFF` — that expression is the authority; if it carries none, the
> read is a new free symbol. Manual input is only *which fields*, never which
> occurrence, owner, or selector. `allKeys.get(K)` is a symbolic map read
> that `ContainerSmtCodec` already expresses.

This removes the scheduler's offline prediction layer —
`ConcolicScheduler.SymbolicInputSelection` (2,615 lines: rotation, causal
version propagation, per-version boundaries, phase ownership, two-pass
un-selection), the runtime's one-producer-per-phase selector admission, the
planner's per-version boundary ledger, and the Hadoop-side selector hooks —
because all of it predicts at PLAN time what the VM records at replay.

The accepted cost is fail-open: a value that reaches a read through an
uninstrumented path the VM never observed becomes a free symbol, and Z3 may
return a witness the concrete system cannot realize. The composition manifest
must therefore name every free symbol that has no recorded lineage, so a
witness carries the list of what it assumes unconstrained and stays
auditable. This replaces the fail-closed refusals, and it is why several of
the HDFS-11741 scheduler fixes made earlier the same day become unnecessary
rather than wrong.

Parallel replay is untouched by this rule: eight-worker external replay,
target-first scheduling, immutable iteration lineage, and deterministic merge
stay as listed under "What must be retained". The rule removes symbol-to-read
*selection*, not task-to-worker *scheduling*. It composes with worker
isolation because expressions propagate only within one JVM and causally
dependent occurrences already share one worker workload, so a read sees
either an in-JVM propagated expression or a fresh symbol — never another
worker's expression.

Two consequences of the same principle, settled the same day, close the
"causal-graph change" question without new machinery. **Topology change is
observed, not predicted:** a new RPC entering the workload is a new region
appearing, and `TopologyDelta` judges divergence at the RPC exchange-event
level — a (sender occurrence, receiver occurrence, port) not in the frozen
catalog is `TOPOLOGY_DIVERGENCE`, and the next campaign iteration re-plans;
`planDigest` is the skeleton signature. **Concurrency does not depend on a
replay happening to hit the interleaving:** for a declared shared field or
container the VM records every symbolic write of the session as a version,
a read yields the version it actually saw, and the composer's read-from
lowering emits `(exactly-one RF_w)` over all recorded versions with each arm
guarded by the ledger's order constraint — Z3 chooses the writer, order
excludes the impossible ones, and no replay confirmation of a read-from
choice is needed. The planner's writer selection and the runtime's
planned-producer-only shared-state admission go; `RecordedReadFrom`,
`BoundedWriterUniverse`, and the `sharedFieldVersions` capture stay as the
mechanism. Fault injection is then a forced selector on the composed formula,
not a feature.

The execution plan for this — the three contracts (mint, read, compose),
the per-layer deletion list, and the four-step sequencing with its gates —
is `experiments/shrink/wave3-plan.md`. Its first gate is a specific
prediction: on the 20-row matrix every value a row reads is propagated, so
the new `freeSymbols` manifest array must be **empty on all twenty rows**;
that emptiness is the proof the fail-open read rule does not fire where
lineage exists.

The remaining wave-3 items:

1. **Decode once.** `ExecutionTask` and `RegionInstancePlan` become the only
   parsers of their rows; today `configuredSourcePhases` is re-decoded at ten
   sites, `outputClosure` at seven, path summaries in four passes, plan rows
   three times. Consumers take typed objects, never `task.json()`.
2. **One session model.** Collapse `RecordedSessionModel`,
   `CanonicalSessionModel`, and the selected-evidence views into one
   deduplicated evidence table with case-local typed references ("Minimal
   cross-stage contract").
3. **One planner layer.** `RuntimeRegionPlanner`, `RuntimeSelectedRegionFinalizer`,
   `SymbolicRegionPlanner`, `RuntimeWorkflowDiscovery`, and `RegionPathWorklist`
   become one target-first planner over one occurrence-scoped catalog. This
   is where the remaining HDFS-11741 blocker is fixed properly: root a region
   on the per-iteration boundary inside a once-entered service loop instead
   of on the loop method, and union all selected demands for one occurrence
   into one task so `phaseProjections()` no longer needs
   `resolveSourcePhaseOwnership` to repair the split after the fact.
4. **One instrumentation pass.** Discovery-trace and replay-region emitters
   share one Jimple builder; the trace recorder and region runtime share one
   hook table.
5. **One owner per check.** Delete every validation that "Minimal cross-stage
   contract" assigns to another layer, and the shell-side semantic
   revalidation in `run_engine.sh`.
6. **Derived fields off the wire.** `phaseKind`, `siteId`, `enclosingCallIds[0]`,
   `replayOccurrence`, `closure.producer.{regionId,relationKey}`,
   `slice.outputPort/outputCell`, the constant `schemaVersion/kind/authority`
   triplets on 18 row kinds, and the 17 same-value-two-names pairs are
   computed, not stored.

The retained-logic floor after wave 3 is not yet measured. If it lands above
30,000, the gap is reported with the list of what remains and why, rather than
closed by weakening HDFS-11741's selected causal closure — that boundary from
"Refactor boundary" still holds.

**Wave-4 gate (2026-08-26 00:09–01:35 UTC):** fresh matrix `matrix-20260826T000947Z` **20/20 PASS** on the
post-wave tree (unit suite 431/0/0, replay-flips 175/175). Against 173609Z every row keeps every
symbolic variable and several rows GAIN variables (`RPC_COMPARE.A/B/E` on rows 9, 11, 12, 15, 16)
because every configured field of every occurrence is now a root; model counts rose accordingly
(e.g. row 9: 1 → 16); `freeSymbols` is empty on all 20 rows. The gate's variable rule is now
"none lost"; gained variables are noted. This matrix is the new replay baseline (the 2026-08-25
artifacts are refused by the importer, by design). One defect was found by the first run
(0/20): the VM answers a concrete primitive with a `ConstExpr`, which the read rule took for a
propagated expression — fixed (`ConcolicRegionRuntime.isSymbolicExpression`).

### Decision 2026-08-25 (late): the design floor is ≈ 75,000, and the stage boundaries stay

After waves 3–4 every large file was clone-scanned by its executor: no repeated
block over 19 lines remains in `RuntimeRegionPlanner`, none over 10 in
`ConcolicRegionRuntime`, the analyzer has zero dead members. The remaining
duplication is the stage boundary itself — one fact encoded per artifact
(skeleton → plan → task → result → case → manifest), each with a decoder,
validation and refusal codes. That duplication is what makes the campaign
debuggable (dumps, per-stage re-entry, loud refusal when a producer changes
shape), and it is kept on purpose. The 30,000 target is therefore given up;
the tree is at its design floor (~76,000 nonblank after wave 4), with one
agreed further cut — `ConcolicConstraintSolver.Encoder` (≈ −700, a port onto the
composer's `Emitter`) once HDFS-11741 has produced its first witness. Merging
the per-iteration stages into one JVM (−15,000 to −20,000) is documented as
an option, not planned.

### Wave 4 — the IR rewrite proper (no gate between waves 3 and 4)

Contract: `experiments/shrink/ir-contract.md` — five row families
(`RegionRow`, `PlanRow`, `ResultRow`, `CaseEvidence`, manifest/z3-result),
exactly one decoder each, no layer re-parses another layer's JSON; refusal
codes and coverage-gap kinds move to their owner and are never deleted.
Decided 2026-08-25: wave 4 starts the moment wave 3 is written, with NO gate
between them — one gate for both waves (`mvn test` → fresh matrix →
variable-set compare by `inputKind|sourceId|fieldSignature` → FREE-SYMBOLS
empty), then HDFS-11741 from a fresh campaign root. Every legacy/compat path
is deleted in the same wave: decode refuses old artifact shapes (no
`ordinal 0 → sourcePhaseId` identity fallback, no string entries in
`symbolizedInputs`, no missing-`reused`/`freeSymbols` defaults, no tolerated
derived observation keys, no `CausynthJson`). Consequence: the 2026-08-25
matrix is no longer replayable by `recompose-matrix.sh`/`replay-flips.sh`;
the fresh matrix becomes the replay baseline. Expected landing: 58,000–63,000;
the remainder is design-required checks and is reported, not cut.

### Rules that apply to every wave

- Delete, never deprecate: no `@Deprecated`, no forwarding shim, no
  commented-out code, no "kept for compatibility".
- Do not add: no helper class, abstraction, or field "to make the merge
  cleaner" (wave 1 permits exactly two: `causynth/MapFields` and methods on
  `concolic/JsonFields`).
- Never touch: the 51 `Hook` names and 7 ad-hoc-bound hook names
  `CausynthPipeline` emits into Hadoop bytecode; the Hadoop-adapter reflection
  targets (`beginSourceRequest`, `endSourceRequest`, `recordRpc`,
  `registerSource`, `registerSourceAlias`, `restartSource`,
  `rejectConfiguredSourceField`, `symbolizeConfiguredSourceField`,
  `selectedConfiguredSourceIntValue`, `exportSymbolicLeaf`,
  `receiveSymbolicLeaf`, `completeResponseHandoff`,
  `HandoffResult.status/reason/handle`); the 32 VM entry-point names; the
  `HandoffLeafCarrier` single-letter fields; the three `java.lang.System`
  natives; the acceptance fields listed under "Completion criteria"; the
  artifact schema numbers pinned by files on disk. A name-based scan reports
  all of these as dead; they are not.
- Planner/executor split: the plan names file:line items with evidence;
  executors cut exactly that, batch the whole wave, gate once, and report
  what they did not cut and why.

## Completion criteria

The milestone is complete only when a single fresh frozen generation produces:

```text
candidate.smt2
candidate_composition_manifest.json
z3-result.json
gaps.json
run-manifest.json
result.json
```

Acceptance requires:

1. Z3 parses the generated SMT and returns `sat`;
2. the query asserts the actual target null lookup;
3. one symbolic key expression flows through the selected NN-to-Balancer,
   NN-to-DN, and Balancer-to-DN communication/state lineage;
4. every RPC value relation comes from successful VM propagation and its
   `VALUE_HANDOFF` edge, not Java re-pairing;
5. every map result comes from the selected complete `put/remove/get` state
   history on the exact owner/version, not a key-membership projection;
6. fixed arrays use exact per-invocation cardinality and while-loop outputs
   come from the matching bounded replay count vector;
7. every selected input has exactly one local, handoff, or known read-from
   authority, with no free port, unknown writer, bound exhaustion, stale
   generation, selected ledger truncation/saturation, or unresolved selected
   gap; and
8. the failure-relevant bounded case/topology worklist is stable.

Observed concolic cases are an existential under-approximation, not an
exhaustive partition of all program paths. SAT may use only fully recorded
known cases. This milestone makes no UNSAT-completeness claim, so it does not
invent an “all paths covered” proof or an unconstrained unknown case.

An old `sat`, handwritten SMT, target-method reach, a successful compile, or a
top-level zero exit code is not completion. No unbounded or UNSAT-completeness
claim is required.

## Required workload entry point

Every discovery and concolic stage must invoke exactly:

```text
org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer
  #testEncryptedBalancer1
```

`experiments/hdfs/hdfs-11741/workflow.properties` and
`source-first-launcher.sh` own this workload setup. No second workload or
fixture is introduced.

After rebuilding the custom VM from the retained ABI, use a new output root:

```bash
cd <this GraphChecker checkout>

export GRAPH_CHECKER_JAVA='<analysis-heap Java wrapper>'
export CAUSYNTH_CLASSPATH='<fresh Hadoop test-scope classpath>'
export CAUSYNTH_OUTPUT_DIR='<fresh generation root on the project volume>'

CAUSYNTH_SCHEDULE_MAX_JOBS=128 CAUSYNTH_CONCOLIC_JOBS=8 \
./run_engine.sh --config experiments/hdfs/hdfs-11741/workflow.properties campaign
```

`CAUSYNTH_OUTPUT_DIR` is the whole "new output root" ceremony: the instrumented
classes, the runtime region plan and the campaign root derive from it, and the
campaign root is `<root>/schedule`, so `<root>/schedule/final` holds the
artifacts below. The workflow already names
`experiments/hdfs/hdfs-11741/loop-bounds.jsonl`, `target.yaml` and the Hadoop
checkout; override the checkout with `CAUSYNTH_REPO` rather than editing the
file. Do not reuse any old plan, summary, VM image, or campaign directory.

After `GATE-1` is implemented, the minimum executable acceptance check is:

```bash
final='<fresh generation root>/schedule/final'

jq -e '
  .finalStatus == "FINAL_READY"
  and .pathSetComplete == true
  and (.finalStatusRefusals | length) == 0
' "$final/candidate_composition_manifest.json"

jq -e '
  .claim == "SAT_CANDIDATE"
  and .reachability == "REACHABLE"
  and .gapCount == 0
  and .evidence.unknownArmBindings == 0
  and .evidence.candidateBindings == 0
' "$final/result.json"

test "$(z3 "$final/candidate.smt2" | sed -n '1p')" = sat
```

`run_engine.sh campaign` applies the same gate itself and does not exit zero
on a run these commands would refuse: a claim other than `SAT_CANDIDATE`/
`UNSAT_CLOSED` exits `2`, and an accepted claim reached with `gapCount > 0`
exits `3` with the named gaps. The two stay separate on purpose -- the gap rows
never re-score the claim, so `result.json` still reports exactly what the
Composer and the solver decided -- but an accepted candidate and an unresolved
gap are not a run anybody may stop on. `result.json` also carries the frozen
`provenance`, which EMIT re-verifies against the inputs on disk before it
publishes anything.

These commands are necessary but not a replacement for the manifest checks
above: the composition manifest must contain the target assertion and every
selected-input authority, and `run-manifest.json` must bind the same source,
JAR, VM, config, target, adapter, loop-bound, region/task plan, production
classes, runtime workload-test class/classpath, iteration, and worker digests.
`result.json.claim` by itself is never acceptance.

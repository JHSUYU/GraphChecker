# Three-thread RPC concolic fixture

This fixture is the concrete end-to-end workload for the generic workflow.
Every execution creates exactly three application worker threads:

- producer A computes and publishes `a` from one `Boolean` input;
- producer B computes and publishes `b` from one `Boolean` and one external
  `int` input;
- the consumer calls `getRPCFromA()` and `getRPCFromB()`, then throws
  `BugReachedException` on the target comparison edge.

The target construction itself is the static-analysis entry point:

```java
throw new @CausynthExceptionTarget("three-thread-rpc")
        BugReachedException(a, b);
```

The fixture target file contains only the marker id. It does not repeat the
exception class or ask static analysis to search every throw site.

The producer workers rendezvous inside their worker frames, proving that both
are concurrently live before either computation proceeds. The harness joins
both producer threads to `TERMINATED` while the consumer is still `NEW`, and
only then starts the consumer. Thus the two concrete producer-support methods
cannot overlap the sole engine-backed consumer target. Each RPC getter records
the value and receiving thread at the actual call boundary; the fixture test
checks those observations against the two real publisher threads and the one
real consumer thread.

The fixture declares no RPC topology. The first Soot pass emits candidate
regions, trace hooks, and a frozen static graph. Runtime then selects the exact
root/class/thread descendant-call closure, and a small demand re-slice over
that frozen graph chooses the concrete `REGION.IN` ports without rerunning
Soot. Shared-field producer/consumer bindings come from receiver-identity,
write-before-read runtime evidence.
The JUnit truth-table sweep is only a concrete workload contract; it does not
provide a reach formula to the composer or extractor.

## Automatic workflow

Build the custom JDK first and make Z3 available. If the custom JDK cannot run
on the host because it needs `libffi.so.6`, the script uses the Docker image
configured by `custom_jdk_docker_image`.
The maintained configs intentionally leave `custom_jdk_library_path` unset:
the runner probes the custom Zero image directly and falls back to Docker only
when that real probe fails. Configure a library path only when the directory
actually exists; no empty compatibility directory is accepted.

Run the full workflow from an empty fixture output directory:

```bash
experiments/generic/three-thread-rpc/run.sh clean
experiments/generic/three-thread-rpc/run.sh all
```

To use a different fixture/workflow configuration, point the script at a
properties file explicitly (a relative override is resolved from the calling
directory):

```bash
CAUSYNTH_WORKFLOW_CONFIG=/path/to/workflow.properties \
  experiments/generic/three-thread-rpc/run.sh all
```

The script reads the fixture main class, trace-test name, replay Docker
image, GraphChecker JAR, class directories, runtime evidence, and
schedule paths from that properties file. Standard workflow paths follow
`workflow_path_base`; the fixture work root is the parent of
`causynth_output_dir`. Keep `workload_command` consistent with the same
fixture metadata when supplying a custom configuration.

Producer exploration remains explicitly bounded.  A workload with a larger
finite path product can raise any of
`producer_max_paths_per_region`, `producer_max_flips_per_path`,
`producer_max_path_tasks`, or `producer_max_path_wall_clock_ms` in its
properties file.  The runner passes those values to every planning round and
still fails closed if the resulting worklist reports a bound gap; it never
treats exhaustion of a configured budget as closure.

`clean` is guarded to remove only the configured fixture work root below the
project's `target` directory (`target/three-thread-rpc` by default). It does
not clean Maven output, the repository, or the custom JDK. `all` refuses to
start when that fixture directory is non-empty.

The runner deliberately has no Maven/JUnit command. `run.sh all` recompiles
the selected fixture and performs only these evidence-gated end-to-end stages:

1. Compile GraphChecker and the fixture, isolate the selected fixture classes,
   resolve the exact classfile exception marker, perform a backward static
   slice from that construction, instrument the trace, and execute a non-bug
   discovery seed.
2. Resolve every producer and the common consumer target from exact runtime
   shared-field read-from bindings. Re-slice the frozen graph inside the
   concrete call closure; unresolved dependencies stay concrete rather than
   becoming free symbols. No generated `REGION.*` identity is assumed.
3. Capture an unforced target seed and schedule its solver-ready target query.
   The seed schedule contains no forced branch.
4. Capture every producer seed. For each producer,
   `ConcolicPathFlipPlanner` repeatedly selects one pending path, Z3 derives
   its input model, the custom JDK executes that model naturally, and the
   strict importer validates the result. Exploration stops only when the
   worklist manifest is closed, then `RegionSummaryMerger` builds the guarded
   producer relation.
5. Compose the closed producer relations with the target seed into one
   structurally complete candidate SMT model.
6. Solve that candidate model by enumerating its discovered Boolean roots while
   leaving other scalar roots existential, invoke Z3 independently on the
   emitted SMT, and hash-bind the SMT, composition manifest, Boolean model, and
   relationship candidates into one `CANDIDATE_ONLY` result manifest.

The terminal candidate artifact set implemented by this workflow is:

```text
target/three-thread-rpc/candidate/candidate.smt2
target/three-thread-rpc/candidate/candidate_composition_manifest.json
target/three-thread-rpc/candidate/candidate_boolean_model.json
target/three-thread-rpc/candidate/candidate_result_manifest.json
```

It binds the generated root-input catalog, complete candidate truth table,
canonical condition, relationship candidates, and SMT by path, byte size, and
SHA-256. A discovered root may legitimately be non-influential when other
scalar inputs remain existential, so the workflow reports exact rows rather
than requiring every Boolean bit to change the result. The
manifest explicitly records `naturalReplayPromotionImplemented=false`.

## Inspecting or resuming stages

Discovery can be inspected without assuming generated identifiers:

```bash
experiments/generic/three-thread-rpc/run.sh discover
```

Individual producer capture and exploration remain available for diagnosis:

```bash
experiments/generic/three-thread-rpc/run.sh schedule-producer A
experiments/generic/three-thread-rpc/run.sh instrument A
experiments/generic/three-thread-rpc/run.sh replay A false false
experiments/generic/three-thread-rpc/run.sh import A
experiments/generic/three-thread-rpc/run.sh explore-producer A
```

The later stage commands are `candidate-compose` and `candidate-solve`.
`candidate` (and its alias `all`) always requires an empty work root so stale
artifacts cannot be mistaken for this run's result.

Five additional no-`while` branch fixtures live under `cases/`. Each keeps the
same two-Boolean, three-thread RPC shape and uses this runner with a separate
work root and target. For example:

```bash
CAUSYNTH_WORKFLOW_CONFIG=experiments/generic/three-thread-rpc/cases/additive-or/workflow.properties \
  experiments/generic/three-thread-rpc/run.sh all
```

`containers/` runs the same end-to-end workflow with live-ins at
`array[1].state.guard.enabled`, a deliberately misleading `array[0]`, and a
map-entry value's nested Boolean leaf. Its `MapProducer` also has two
existential `int` roots, `input1` and `input2`: values below 10 are clamped to
10, and the selected result uses exact Java `int` wrap semantics. The projected
cross-method `producer#field:inputN` ports are canonicalized to the declared
primitive fields only after exact static-chain and runtime owner-identity
checks, with the base read preceding the leaf read and no intervening write to
that exact leaf. The array relation closes with 2 cases and the map relation
with 10.
`dependent-scalar/` exercises a non-Boolean free scalar that affects a
producer relation. `cross-method-fields/` crosses several helper calls and
reads genuine instance/static field live-ins. `multitype/` combines Boolean,
`int`, `long`, `double`, `String.contains`, and a bounded `for` loop.  Each
uses the same runner through `CAUSYNTH_WORKFLOW_CONFIG`; none changes the
workflow or declares fixture-specific SMT.
`unreachable-parity/` reads the same nested array-index and map-entry field
shapes as the container workload, but its two guarded producers publish only
odd and even integers respectively. The annotated target requires those RPC
values to be equal. None of the four Boolean root valuations can reach it, so
the generated candidate SMT and independently invoked Z3 must both report
`UNREACHABLE`/`unsat`; the fixture and scripts contain no handwritten
reachability formula or expected-SMT shortcut.
## Core end-to-end robustness gate

The normal robustness gate is deliberately limited to these three concrete
three-thread workloads.  All three use two concurrently-live producers, a
deterministic runtime-confirmed read-from relation, and a consumer that starts
after both producers terminate.  They exercise the same generic workflow; no
workload supplies fixture-specific SMT or a declared RPC mapping.

1. `ThreeThreadRpcWorkload`, configured by `workflow.properties`, is the
   baseline Boolean-plus-`int` workload.  It covers two Boolean producer paths,
   an external integer producer live-in, Java integer arithmetic/overflow, RPC
   composition, and the consumer comparison.
2. `CrossMethodExternalFieldThreeThreadWorkload`, configured by
   `cross-method-fields/workflow.properties`, covers nullable Boolean/String
   inputs, `String.contains`, several helper-call hops, and genuine instance
   and static integer fields.  Helper return values must remain internal
   definitions rather than being promoted to root inputs.
3. `MixedTypeThreeThreadRpcWorkload`, configured by
   `multitype/workflow.properties`, covers Boolean, `int`, `long`, `double`,
   nullable `String.contains`, Java floating-point comparison semantics, and a
   bounded deterministic `for` loop.

Run exactly this core gate with:

```bash
experiments/generic/three-thread-rpc/run_robustness_matrix.sh core
```

The matrix recompiles each selected workload, runs the complete concolic
workflow, invokes Z3 on the emitted SMT, and validates the expected root-input
catalog and truth-table profile. `containers` additionally checks exact
`array[1].state.guard.enabled` and map-key-7 rebinding, a 2-case array relation,
a 10-case map relation, Java `int` wrap, schema-3 witness/context separation,
and input-only unforced producer-path replay. Its two Boolean roots produce four
`sat` rows because `input1` and `input2` remain existential in each row.
`unreachable-parity` additionally requires two closed
two-case producer relations, the exact odd/even output images, zero satisfying
rows, four unsatisfying rows, and direct Z3 `unsat`. Run all six maintained
profiles with `run_robustness_matrix.sh all`. Unit tests are not run by this
command.

## Completed: one binary-branch replay authority

Every observed binary decision now owns one immutable typed `BranchWitness`:
stable site/occurrence identity, the source execution's taken outcome, its one
canonical satisfied predicate, VM path-condition index, and predicate
normalization. The wire value carries no self-hash or nested duplicate VM event.
`BranchPredicateAlgebra` is the only predicate-complement implementation, and
only `BranchReplayContract.flip()` may derive the required opposite
outcome/predicate. A zero-PC branch event stays observation-only; it cannot be
turned into a synthetic witness by a parallel proof protocol.

The worklist emits a schema-3 task containing that contract. A separate
immutable typed `SolverPathContext` retains positioned non-branch
`_array_expr`/`MethodExpression` nodes needed by the solver; it rejects an
unwitnessed Boolean predicate and is never consumed as runtime branch evidence.
The solver, activation builder, static instrumentation gate, runtime, importer,
scheduler, and replay verifier consume the same replay contract; they no longer
reconstruct or cross-compare `targetBranch`, `expectedBranchPrefix`, replay
constraints, or a scheduled-target envelope. Runtime observations carry new
witnesses, and one validator checks the ordered prefix followed by the exact
required target. The required target is derived from the source witness rather
than serialized a second time. Malformed witnesses and duplicate branch-event
identities fail closed. Multiway `switch` remains a separate successor-aware
observation.

All six matrix profiles pass this protocol through candidate SMT generation,
independent Z3 checking, and their exact expected reach profiles; one profile
is intentionally unreachable and therefore expects Z3 `unsat`.

## TODO: promote a candidate with natural replay

Natural replay promotion is intentionally not implemented. A future stage must
materialize only the selected producer inputs in the full workload, prohibit
all downstream injection and branch override, observe the annotated exception
target naturally, and bind that observation to the candidate artifact hashes
before introducing any trusted/final result state.

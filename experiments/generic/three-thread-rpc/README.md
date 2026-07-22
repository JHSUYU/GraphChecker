# Three-thread RPC concolic fixture

This fixture is the concrete end-to-end workload for the generic workflow.
Every execution creates exactly three application worker threads:

- producer A computes and publishes `a` from one `Boolean` input;
- producer B computes and publishes `b` from one `Boolean` input;
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
3. Capture an unforced target seed and schedule its solver-ready bootstrap
   query. The seed schedule contains no forced branch.
4. Capture every producer seed. For each producer,
   `ConcolicPathFlipPlanner` repeatedly selects one pending path, Z3 derives
   its input model, the custom JDK executes that model naturally, and the
   strict importer validates the result. Exploration stops only when the
   worklist manifest is closed, then `RegionSummaryMerger` builds the guarded
   producer relation.
5. Compose the closed producer relations with the target seed. This produces
   a structurally complete `BOOTSTRAP` SMT model, but it is explicitly
   ineligible as a final report.
6. Exhaustively project the bootstrap SMT over its discovered Boolean roots in
   `BOOTSTRAP_REPLAY_MODEL` mode, invoke Z3 independently on the emitted SMT,
   and hash-bind the SMT, composition manifest, reach model, and relationship
   candidates into one `CANDIDATE_ONLY` result manifest.

The terminal artifact implemented by this workflow is:

```text
target/three-thread-rpc/bootstrap/candidate_result_manifest.json
```

It binds the generated root-input catalog, complete candidate truth table,
canonical condition, relationship candidates, and SMT by path, byte size, and
SHA-256. A discovered root may legitimately be non-influential after
existential projection of other scalar inputs, so the workflow reports exact
rows rather than requiring every Boolean bit to change the result. The
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

The later stage commands are `bootstrap-compose` and `bootstrap-project`.
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
map-entry value's nested Boolean leaf.
`dependent-scalar/` exercises a non-Boolean free scalar that affects a
producer relation. `cross-method-fields/` crosses several helper calls and
reads genuine instance/static field live-ins. `multitype/` combines Boolean,
`int`, `long`, `double`, `String.contains`, and a bounded `for` loop.  Each
uses the same runner through `CAUSYNTH_WORKFLOW_CONFIG`; none changes the
workflow or declares fixture-specific SMT.
`FourThreadSharedFieldWorkloadTest` is the compact recursive fork/merge
regression for `1 -> 2 -> 3` and `1 -> 4 -> 3`. Neither workload has a
`while` loop.

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
catalog and truth-table profile.  Unit tests are not run by this command.

## Completed: one binary-branch replay authority

Every observed binary decision now owns one immutable, content-hashed
`BranchWitness`: stable site/occurrence identity, the source execution's taken
outcome, its one canonical satisfied predicate, and exactly one evidence
variant (`VM_PC` or `CERTIFIED_NO_PC`). `BranchPredicateAlgebra` is the only
predicate-complement implementation, and only `BranchReplayContract.flip()`
may derive the required opposite outcome/predicate.

The worklist emits a schema-2 task containing that contract. The solver,
activation builder, static instrumentation gate, runtime, importer, scheduler,
and replay verifier consume the same contract; they no longer reconstruct or
cross-compare `targetBranch`, `expectedBranchPrefix`, replay constraints, or a
scheduled-target envelope. Runtime observations carry new witnesses, and one
validator checks the ordered prefix followed by the exact required target.
Duplicate branch-event identities and content-hash tampering fail closed.
Multiway `switch` remains a separate successor-aware observation.

The three core workloads pass this protocol through candidate SMT generation,
independent Z3 checking, and their exact expected reach profiles.

## TODO: promote a candidate with natural replay

Natural replay promotion is intentionally not implemented. A future stage must
materialize only the selected producer inputs in the full workload, prohibit
all downstream injection and branch override, observe the annotated exception
target naturally, and bind that observation to the candidate artifact hashes
before introducing any trusted/final result state.

## HDFS validation checkpoint

The frozen HDFS trace was re-aggregated without rerunning Soot, instrumentation,
or the workload. `target/hdfs-runtime-demand-reslice-v5` completed in 2:20.25
with 19,043,412 KiB peak RSS, versus the 10:26.98 / 19,679,528 KiB baseline.
All 430 instances used the runtime-guided re-slice; 63,673 candidate inputs
were pruned, 385 confirmed external inputs were restored, and warnings are 0.

The HDFS RPC/SASL mapping remains enabled for true transport boundaries.
`REGION_EDGE.0` retains 10 SASL equality bindings, while edges 802 and 2076
retain 50 and 10 exact read-from bindings. The v5 selector is complete and
selects the same five runtime calls (NN, DN, KeyUpdater, Dispatcher, target)
with all causal bounds verified.

The historical v5 HDFS checkpoint cannot be recomposed from this checkout
because its five configured replay-summary files are absent and have no
recoverable in-repository source. Regenerating those external experiment
artifacts is outside the three-workload reference gate. The intentionally loose
HDFS loop/read-from policies remain documented limitations; v5 measures only
the frozen-graph runtime re-slice, not a fresh full-HDFS catalog run.

# Three-thread RPC concolic fixture

This fixture is the concrete end-to-end workload for the generic workflow.
Every execution creates exactly three application worker threads:

- producer A computes and publishes `a` from one `Boolean` input;
- producer B computes and publishes `b` from one `Boolean` input;
- the consumer calls `getRPCFromA()` and `getRPCFromB()`, then throws
  `BugReachedException` on the target comparison edge.

The producer workers rendezvous inside their worker frames, proving that both
are concurrently live before either computation proceeds. The harness joins
both producer threads to `TERMINATED` while the consumer is still `NEW`, and
only then starts the consumer. Thus the two concrete producer-support methods
cannot overlap the sole engine-backed consumer target. Each RPC getter records
the value and receiving thread at the actual call boundary; the fixture test
checks those observations against the two real publisher threads and the one
real consumer thread.

The topology file hardcodes only the two allowed RPC channels. It contains no
region identifiers, Boolean valuation, reachability condition, or SMT text.
Concrete thread identities, region instances, producer/consumer bindings, and
branch observations all come from the trace and custom-JDK executions.
The JUnit truth-table sweep is only a concrete workload contract; it does not
provide a reach formula to the composer or extractor.

## Automatic workflow

Build the custom JDK first and make Z3 available. If the custom JDK cannot run
on the host because it needs `libffi.so.6`, the script uses the existing
`causynth-openjdk8-build:ubuntu18` container.

Run the full workflow from an empty fixture output directory:

```bash
experiments/generic/three-thread-rpc/run.sh clean
experiments/generic/three-thread-rpc/run.sh all
```

`clean` is guarded to remove only files below `target/three-thread-rpc`. It
does not clean Maven output, the repository, or the custom JDK. `all` refuses
to start when that fixture directory is non-empty.

The automatic command performs these evidence-gated stages:

1. Run the three-thread JUnit contract, isolate the fixture classes, perform
   static analysis, instrument the trace, and execute a non-bug discovery
   seed.
2. Resolve every producer and the common consumer target from
   `rpc-topology.jsonl`, runtime activation evidence, and exact read-from edge
   bindings. No generated `REGION.*` identity is assumed.
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
   `BOOTSTRAP_REPLAY_MODEL` mode. The primitive projector chooses a SAT model
   and exact guarded cases, then emits one `ALL` bundle containing producer
   input assignments followed by an engine-backed, observation-only target.
   Instrumentation and replay omit the activation-id selector for this bundle.
7. Run that bundle on the three real threads. A nonzero JVM exit is accepted
   only when the raw result contains the unique PRIMARY target row. The
   importer must prove a naturally observed bug branch with no branch override
   and no downstream injection, after which the scheduler emits a
   replay-validated target query.
8. Run `ConcolicCampaignRunner` in `FIXED_VALIDATED_GRAPH` mode. Campaign
   executions use unique attempt directories, and bounded incomplete runs
   retain an atomic resume checkpoint.
9. Verify every SHA-256 and row count in the campaign's immutable state
   generation. Re-schedule its exact validated target, compose the
   `VALIDATED_FINAL` SMT, prove generated relationships with Z3, and derive the
   final Boolean reach report in `FINAL_REPORT` mode.

The final user-facing result is:

```text
target/three-thread-rpc/final/boolean_reach_condition.json
```

The report contains the generated root-input catalog, complete truth table,
canonical condition, and proof metadata. The script additionally checks that
every topology-discovered producer Boolean is influential in that truth
table. The bootstrap report is replay-only and can never be substituted for
this final artifact.

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

The later stage commands are `bootstrap-compose`, `bootstrap-project`,
`bootstrap-replay`, `campaign`, and `final`. If a bounded campaign exits
incomplete, rerun `campaign`; its atomic `campaign_state_manifest.json` is the
only resume authority. Partial campaign directories without that pointer are
rejected rather than overwritten.

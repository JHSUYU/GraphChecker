# Three-thread RPC fixture

This fixture is the compact end-to-end regression for automatic region
discovery, two shared-field producers, custom-VM summaries, symbolic merge,
SMT composition, and Z3.

The public workflow is intentionally small:

```bash
# Build and isolate fixture classes.
experiments/generic/three-thread-rpc/run.sh prepare

# Stop after static/runtime discovery and target-task scheduling.
experiments/generic/three-thread-rpc/run.sh tasks

# Run the complete automatic VM -> SMT -> Z3 pipeline.
experiments/generic/three-thread-rpc/run.sh full
```

`clean` removes only this fixture's configured work directory. Individual
region scheduling, instrumentation, replay, import, merge, and composition are
internal functions of `full`; they are not separate supported workflows.

Producer campaigns are discovered from runtime-confirmed field/RPC occurrences.
Campaign identity is derived from region, owner/occurrence plan, and goal—not
from output field names or transient JVM ids. The shell never writes a summary
or SMT formula.

The robustness matrix runs `full` for each configured variant:

```bash
experiments/generic/three-thread-rpc/run_robustness_matrix.sh
```

The stress fixture and expected truth tables are documented under `stress/`.

# Manual container Z3 workload

Edit only:

```text
src/test/java/edu/uva/liftlab/graphchecker/manual/ContainerThreeThreadRpcWorkload.java
```

Then run from the repository root:

```bash
experiments/generic/three-thread-rpc/manual-container/run.sh
```

The command cleans its isolated work directory, builds GraphChecker without
compiling the regular test tree, compiles only the manual workload, runs the
real custom-JDK workflow, and prints only `sat` or `unsat`. Detailed workflow
output is saved in `target/manual-container-workflow.log`.

Individual commands are also available:

```bash
experiments/generic/three-thread-rpc/manual-container/run.sh clean
experiments/generic/three-thread-rpc/manual-container/run.sh build
experiments/generic/three-thread-rpc/manual-container/run.sh z3
```

The final SMT file is:

```text
target/manual-container-three-thread-rpc/candidate/candidate.smt2
```

This entry point does not run the maintained fixture matrix and does not
assert a fixed SAT/UNSAT profile.

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
real custom-JDK workflow, and finally runs Z3. The complete workflow and the
final `sat` or `unsat` result are shown live and saved together in:

```text
target/manual-container-three-thread-rpc/workflow.log
```

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

To download every JSON artifact from a remote GraphChecker server, preserving
the artifact directory layout and converting each JSONL file to a JSON array:

```bash
experiments/download-manual-container-json.sh \
  ZhenyuLi@c220g5-120102.wisc.cloudlab.us
```

Each download is written below:

```text
target/manual-container-three-thread-rpc-json/<UTC timestamp>/
```

The remote SSH session must start in the GraphChecker repository root because
the artifact source is the relative path
`target/manual-container-three-thread-rpc`.

This entry point does not run the maintained fixture matrix and does not
assert a fixed SAT/UNSAT profile.

# Fixed-RPC stress campaign

This campaign changes producer/consumer computation without changing the RPC
protocol. Every generated workload has exactly:

- two producer threads that rendezvous before computing;
- one `publishA` and one `publishB` to two shared primitive fields;
- both producers joined before the consumer starts;
- one `getRPCFromA`, followed by one `getRPCFromB`;
- one annotated target exception in the consumer.

There is no `while (true)`, variable-bound loop, reflection, native call, or
schedule-dependent expected result. Fixed loops use literal bounds.

## Engineering rule

Failures are collected for a whole campaign before production code changes.
A repair must address one shared semantic boundary and must not mention a
generated class, case number, field name, site ID, or container family.
The same invariant is checked once at its owning trust boundary; shell,
Importer, Worklist, and Composer must not accumulate duplicate defensive
checks.

## Truth table

Each workload is executed on a normal JVM for all four Boolean inputs:

```text
(false,false), (false,true), (true,false), (true,true)
```

The truth table records whether the exact annotated exception is reached.
`SAT` means at least one row reaches it; `UNSAT` means no row reaches it. This
normal-JVM result is test evidence only and is never supplied to GraphChecker,
the custom JDK, or Z3.

## Coverage

Each round contains 20 deterministic families, rotated between producer A and
producer B:

- scalar fields, compound guards, cross-method state, nested objects;
- inheritance, receiver aliases, multiple writes and object mutation;
- helper calls whose object parameters carry ordinary, inherited, hidden,
  nested, and container-element fields;
- arrays and literal-bound array loops;
- Map entry/mutation, List index/iterator, Set and Queue;
- map-of-array and array-of-map nesting;
- boxed primitives, String flow, and wide/narrow integral types.

The consumer variants add preceding guards and compound `&&`/`||` conditions.
Odd cases are SAT and even cases are UNSAT, giving ten of each per round.

## Commands

Generate, validate, and run one round:

```bash
python3 experiments/generic/three-thread-rpc/stress/generate_round.py 5
experiments/generic/three-thread-rpc/stress/validate_concrete_round.sh
GRAPH_CHECKER_STRESS_JOBS=20 \
  experiments/generic/three-thread-rpc/stress/run_stress_matrix.sh 5
```

Collect the five rounds:

```bash
experiments/generic/three-thread-rpc/stress/collect_rounds.sh 1 5
```

Each GraphChecker pass requires all three facts:

1. the workflow exits successfully;
2. final reachability equals the normal-JVM SAT/UNSAT label;
3. the composed model resolves both confirmed RPC producer bindings.

The third check prevents a missing producer from becoming an unconstrained
existential and accidentally producing the expected label.

## Pre-fix baseline

The first five-round collection validated all 100 concrete truth tables, then
produced 10 apparent GraphChecker passes and 90 failures. After checking both
producer bindings, some of those ten apparent passes were also incomplete.
The 90 reported failures grouped as:

```text
40  output admission
21  unmapped synthetic branch
15  invalid witness prefix
 8  target seed without a solver-ready branch
 5  non-numeric boxed primitive expression
 1  SAT reported unreachable
```

The groups reduced to four general defects:

- an exact primitive field first read only after a flip was rejected because
  the seed path had not observed it;
- synthetic Jimple branches were incorrectly assumed to own exactly one VM
  path-condition predicate;
- boxed primitive value shadows were overwritten with reference sort `L`;
- Composer bounds could silently remove a confirmed first-hop producer demand.

The history directory preserves the per-round manifests and raw pre-fix result
tables. A completed campaign replaces those result tables with verified
post-fix results rather than deleting the evidence.

## Final five-round gate

The post-fix campaign completed on 2026-07-27:

```text
round 1  20/20 PASS
round 2  20/20 PASS
round 3  20/20 PASS
round 4  20/20 PASS
round 5  20/20 PASS
total   100/100 PASS
```

Every round first passed all 20 four-row concrete truth tables. A GraphChecker
case counted as `PASS` only when the real custom-JDK/concolic workflow
completed, Z3 matched the declared SAT/UNSAT result, and the final composition
resolved exactly both fixed shared-field RPC producer bindings. The committed
`history/round-*-manifest.tsv` and `history/round-*-results.tsv` files are the
machine-readable evidence. Round 5 remains as the checked-in source fixture
set; its object-parameter helpers cover cross-method state, nested fields,
declared-owner inheritance/hidden fields, and container-element objects.

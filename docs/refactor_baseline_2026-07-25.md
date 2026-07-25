# GraphChecker fresh-refactor baseline

Baseline commit: `575e097ce30e0b366baa69e176552541ad69ffca`

Production Java scope:

```text
find src/main/java -name '*.java' -type f -print0 | xargs -0 wc -l
81,581 lines
```

The baseline was produced in a detached clean worktree. The configured custom
JDK was copied into that worktree; no artifact from the dirty primary worktree
was reused.

Command:

```bash
GRAPH_CHECKER_MATRIX_JOBS=13 \
  experiments/generic/three-thread-rpc/run_robustness_matrix_parallel.sh all
```

Result: 13/13 profiles, 6 reachable/sat, 7 unreachable/unsat, 0 failures.
Total parallel wall time was 290.15 seconds; coordinator maximum RSS was
1,147,176 KiB.

`Cases` lists the guarded relation case count for each producer. `Trace` is
`runtime/runtime_trace.jsonl`. `Candidate` is the complete candidate directory.
`Artifacts` is the complete profile work root. `Wall` is log creation through
last write and therefore has one-second resolution. `GC JVM` is the sum of all
`GraphChecker ran for ... ms` stages in the profile log; custom-JDK replay,
shell coordination and Z3 account for the remainder.

| Profile | Result | Boolean sat/unsat | Cases | Trace bytes | Candidate bytes | Artifact bytes | Wall s | GC JVM ms |
| --- | --- | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| baseline | reachable/sat | 2/2 | 2+4 | 73,689 | 50,645 | 1,231,219 | 95 | 18,488 |
| cross-method-fields | reachable/sat | 1/3 | 4+2 | 211,679 | 67,266 | 3,588,487 | 192 | 25,131 |
| multitype | reachable/sat | 2/2 | 10+2 | 118,486 | 97,944 | 3,144,035 | 179 | 22,467 |
| dependent-scalar | reachable/sat | 1/1 | 6+2 | 125,826 | 57,894 | 1,735,152 | 99 | 21,139 |
| containers | reachable/sat | 4/0 | 2+24 | 149,017 | 398,003 | 6,090,988 | 162 | 28,539 |
| unreachable-parity | unreachable/unsat | 0/4 | 12+14 | 159,531 | 637,078 | 6,856,540 | 190 | 30,824 |
| unreachable-correlated-fields | unreachable/unsat | 0/4 | 6+2 | 152,970 | 76,115 | 2,882,503 | 154 | 25,643 |
| unreachable-nested-object | unreachable/unsat | 0/4 | 5+5 | 101,073 | 75,310 | 4,870,627 | 202 | 25,648 |
| unreachable-inherited-alias | unreachable/unsat | 0/4 | 2+6 | 87,109 | 62,843 | 3,357,574 | 173 | 24,246 |
| unreachable-mutated-object | unreachable/unsat | 0/4 | 2+6 | 169,267 | 58,293 | 2,758,311 | 137 | 25,264 |
| unreachable-long-fields | unreachable/unsat | 0/4 | 5+5 | 110,663 | 76,637 | 6,015,018 | 232 | 27,306 |
| compound-target | reachable/sat | 3/1 | 2+2 | 114,282 | 77,566 | 5,177,041 | 269 | 35,870 |
| unreachable-compound-target | unreachable/unsat | 0/4 | 2+2 | 114,676 | 69,728 | 5,222,417 | 273 | 36,293 |

Semantic comparison after each PR uses the columns above plus root SMT sorts,
joint-output membership, target reached-path count and read-from binding
identity. Artifact byte identity and diagnostic-only IDs are deliberately not
part of the contract.

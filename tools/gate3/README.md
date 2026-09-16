# tools/gate3 — the offline regression gate

`gate3.sh` re-runs the offline owners of the engine — `explore.ExploreMain`,
`compose.ComposeMain`, `runtime.CausynthTraceRecorder`,
`plan.ConcolicScheduler` and the static pass `GraphCheckerMain` — over two
FROZEN CORPORA and writes one digest line per artifact. It executes no
workload, starts no campaign, and writes nothing under a corpus or under a
Hadoop tree. This is how every round-3 change was judged: change the engine,
re-run the gate, and account row by row for every digest that moved.

    gate3.sh <jar> <outdir>            # ~85 s, ~120 MB under <outdir>
    diff_gate.sh <outdir> [baseline]   # per-artifact differences vs baseline/

## READ THIS FIRST: the paths in these scripts are dead

The defaults at the top of `gate3.sh` name scratch directories on the BUILD
HOST THIS PROJECT RAN ON, WHICH HAS BEEN DECOMMISSIONED. Every one of them is
an environment variable with a default, so nothing needs editing — override
them:

| variable | what it names | default (dead) |
|---|---|---|
| `GATE3_CORPORA` | `id\|corpus out dir\|experiment dir`, one per line | two `/tmp/...` corpora |
| `GATE3_REPO` | the checkout whose `experiments/hadoop/<case>` is read | a `wt-stage` worktree |
| `GATE3_SPO`, `GATE3_MY` | only used to build the two defaults above | scratch dirs |
| `GATE3_SCOPE_MAP_DIR` | `<dir>/<id>/static_scope_map.jsonl` for wave 0 and the scheduler | empty (use the corpus's) |
| `GATE3_JAVA`, `GATE3_Z3`, `GATE3_XMX` | tools and heap | JDK 8, `/usr/local/bin/z3`, `-Xmx8g` |
| `GATE3_SUBGATES` | which sub-gates run | `wave0 compose plan static` |

**The `gate3.sh` here is the version that matches THIS commit.** It passes the
case's `symbolic-inputs` declaration to the recorder stage
(`-Dcausynth.symbolic.inputs=...`), which is what `run_engine.sh:run_java_main`
now does and which the region finalizer's demand walk reads. An older copy of
this script does not, and silently under-feeds the walk: measured on this tree,
the older script produces 11741 `rows=123 symbolize=43[CALL_RETURN:13,...]`
where the correct one produces `rows=133 symbolize=46[CALL_RETURN:16,...]`.
If a gate run's plan counts look low, check the script before the engine.

`baseline/DIGESTS.txt` is the digest text of the last baseline taken — staging
tip `0e3c1ab39`, i.e. the round-3 work through `r3/C3`, before the `r3/FIX1`,
`r3/PC4` and `r3/R4` merges. **The baseline artifacts themselves are not in
this repository, and neither are the corpora** (~400 MB). `diff_gate.sh`
compares artifact by artifact and needs a full baseline directory, so with the
digest text alone you can only compare DIGESTS.txt lines — which is enough to
see what moved, not to see how.

Gate at this commit (two-pass, campaign way), against that baseline: **8 of 46
rows differ, and every `wave0` and `compose` row is byte-identical**, so 17960's
claim is unmoved. The 8: six `plan` rows and one `meta` row
(`11741/meta/workflow.properties`, `matches-corpus=NO`) are `r3/PC4`'s declared-
port walk — 17960 45 -> 16 tasks, 11741 86 -> 133, 11741 `schedule_max_jobs`
128 -> 256 — and the eighth is `17960/static/candidate_dataflow_edges.jsonl.gz`,
the known Soot local-naming instability that PC4's unfinished item 4 removes.
Two successive runs of the gate were byte-identical on all 46 rows.

`GATE3-LOG.md` is the gate's own history: for each round-3 merge, which rows
moved, by how much, and whose change it was. It is the most detailed record of
what round 3 did to the artifacts, and its `$MY` / `$SPO` paths are dead in
the same way.

## Regenerating a corpus

A corpus is one acceptance campaign's output tree, `out/<case>/`. Produce one
with the acceptance harness (see `experiments/hadoop/accept/README.md`):

```bash
export CAUSYNTH_CUSTOM_JDK_HOME=/absolute/path/to/j2sdk-image   # the custom VM
CASES=hdfs-17960 bash experiments/hadoop/accept/accept.sh
# the corpus is then $OUT/out/hdfs-17960, default <repo>/target/accept/out/...
```

then point the gate at it:

```bash
GATE3_CORPORA="17960|/path/to/out/hdfs-17960|$PWD/experiments/hadoop/hdfs-17960" \
  tools/gate3/gate3.sh target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar /tmp/g
```

This requires the custom VM image and a Hadoop workload tree — see
`docs/HANDOVER.md`, which says what has to be rebuilt first. Approximate
campaign times on the old host: 17960 about 1 hour, 11741 about 30 minutes.

## The two-pass (campaign-way) invocation

`gate3.sh` reads `GATE3_SCOPE_MAP_DIR` at the top of each corpus loop, before
its own `static` sub-gate has run, so to gate a jar against ITS OWN static
maps — which is what `run_engine.sh` does in a campaign — run it twice:

```bash
gate3.sh "$JAR" "$OUT-a"                       # pass A: produce the maps
for id in 11741 17960; do
  mkdir -p "$MAPS/$id"
  cp "$OUT-a/$id/static/out/static_scope_map.jsonl" "$MAPS/$id/"
done
GATE3_SCOPE_MAP_DIR="$MAPS" gate3.sh "$JAR" "$OUT"   # pass B: the recorded run
diff_gate.sh "$OUT"
```

Pass A and pass B produce byte-identical `static` products, so `$MAPS` is this
run's own map either way.

## Rules that still apply

* **Never edit a kept corpus in place.** `ExploreMain` writes `slots.jsonl`
  beside `--sessions`; `restore_slots.sh` exists to put a corpus back if
  something did. Copy a corpus before experimenting on it.
* A sub-gate that cannot run prints `SKIPPED <reason>` in the digest field
  rather than failing the gate — so **check the SKIPPED count**, not only the
  exit status. `0 SKIPPED` is part of a green gate.
* `diff_gate.sh` exits 1 when anything differs. A moved row is not a failure;
  an UNEXPLAINED moved row is.

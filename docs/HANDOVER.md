# HANDOVER — start here

Operational entry point. `README.md` is the design; its **section 9** is the status
and the ordered to-do. This file is how to build it and run it.

## The host is gone

GraphChecker was developed on one build machine, and that machine has been
**decommissioned**. This repository is all that survived. Three things it
depended on are not here and must be rebuilt before any case can run:

| what | where it was | how to get it back | cost |
|---|---|---|---|
| the custom VM image | `third_party/.../build/linux-x86_64-normal-zero-release/images/j2sdk-image` | build it, below | hours |
| the Hadoop workload trees | `/opt/hadoop-hdfs-*` | clone `JHSUYU/hadoop` branches, below | minutes + a Hadoop build |
| the two frozen corpora | scratch dirs on that host | re-run the acceptance harness | 17960 ≈ 1 h, 11741 ≈ 30 min |

Paths in `docs/design/`, `docs/reports/` and `tools/gate3/GATE3-LOG.md` refer to
that host; read them as descriptions of what an artifact *was*.

## Layout

```
src/main/java/edu/uva/liftlab/graphchecker/
  causynth/   static pass + region finalizer (the scope slice)
  plan/       scheduler, scope map, dependency roles, loop-bound policy
  runtime/    the in-JVM recorder, region runtime, row publication, replay
  contract/   IMPORT gate + row invariants
  explore/    wave planner and focused-replay workers
  compose/    families, arms, claim policy, the composer
  smt/        lowering, canonical JSON, artifact IO
run_engine.sh            the campaign driver (stages, gates, waves)
experiments/hadoop/      one directory per case + the acceptance harness
tools/gate3/             the offline regression gate (see its README)
docs/design/             the reference design these were built from
docs/reports/round3/     the round-3 surveys and per-case diagnoses
docs/planner-memory/     the owner's standing rules — read before changing anything
docs/wip/                unfinished round-3 work, as patches
third_party/OpenJDK-Concolic-Execution-Engine/   the custom VM (in-tree, not a submodule)
```

## Build

```bash
mvn -o -T 1 package          # JDK 8, Maven 3.6; 46 @Test must pass
bash src/test/shell/run_engine_campaign_helpers_test.sh
```

Run Maven `nice -n 10 -T 1`. The jar the rest of the tooling wants is
`target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar`.

## Rebuild the VM image

The engine needs a concolic OpenJDK 8; the stock JDK cannot carry expressions.
The build is in-tree and containerized:

```bash
cd third_party/OpenJDK-Concolic-Execution-Engine
FULL_JDK=true JOBS=8 bash scripts/causynth_build_in_docker.sh
# Dockerfile: docker/causynth/Dockerfile
# result:     build/linux-x86_64-normal-zero-release/images/j2sdk-image
export CAUSYNTH_CUSTOM_JDK_HOME=$PWD/build/linux-x86_64-normal-zero-release/images/j2sdk-image
```

`FULL_JDK=true` selects `make hotspot jdk images` rather than the hotspot-only
incremental path; without it a change under `jdk/` is silently not rebuilt.

## Re-create the Hadoop workload trees

All workload trees are branches of `git@github.com:JHSUYU/hadoop.git`, upstream
base `734dd8a67c` (3.6.0-SNAPSHOT):

| branch | case |
|---|---|
| `gc/hadoop-tracing-prune` | the shared parent — tracing/scope edits common to the cases |
| `gc/hdfs-11741-current` | HDFS-11741 |
| `gc/hdfs-17897-striped-checksum` | HDFS-17897 |
| `gc/hdfs-17899-wire-base` | HDFS-17899 base |
| `gc/hdfs-17899-bug1`, `-bug2`, `-bug3` | HDFS-17899, one per request flow |
| `gc/hdfs-17960-snapshot-replay{,-jdk8}` | HDFS-17960 (the second is the JDK 8 variant) |

The same edits are captured **in this repository** under
`experiments/hadoop/<case>/tree-edits/` — sources verbatim plus `diffs/`, with a
`MANIFEST.md` naming each tree, its branch and its pushed sha — so a tree can be
re-created either by checking out the branch or by applying the captured edits to
`734dd8a67c`. Editing Hadoop sources for tracing/scope is permitted; keep the
diffs, and **never rebuild a tree while a campaign is running on it**.

## Run a case

```bash
export CAUSYNTH_CUSTOM_JDK_HOME=/absolute/path/to/j2sdk-image
DRY=1 CASES=hdfs-17960 bash experiments/hadoop/accept/accept.sh   # preflight only
CASES=hdfs-17960 bash experiments/hadoop/accept/accept.sh
```

`accept.sh` builds the jar, then per case runs that case's `run.sh validate` and
`run.sh campaign`, which exec `run_engine.sh` with the case's `execute.sh` as
workload and replay command. Cases run one at a time; at most two campaign lanes
on one machine, and no rebuild while a lane runs. Results land under `$OUT`
(default `target/accept`): `summary.tsv`, `logs/<case>.log`, `out/<case>/` (the
campaign tree — this is what a "corpus" is), `report/<case>/report.md`.

`report.py` decides PASS from the published claim: `SAT_CANDIDATE`,
`FINAL_READY`, no blocking gap, the mechanism the case is known to fail by,
`polarityDecides` true, and a finding that moves at least one root away from the
recording. See `experiments/hadoop/accept/README.md`.

## The offline gate

`tools/gate3/` re-runs the offline stages over a frozen corpus and digests every
artifact, so a change is judged by which digests moved. This is the normal loop;
a live campaign is expensive. The corpora are not in this repository — regenerate
one as above and point `GATE3_CORPORA` at it. `tools/gate3/README.md` has the
environment variables (the defaults are dead paths) and the two-pass invocation;
`GATE3-LOG.md` is round 3's row-by-row account and the model for explaining a
moved row; `baseline/DIGESTS.txt` is the digest text at staging `0e3c1ab39`,
before the three merges named below.

## The unfinished work

`docs/wip/{FIX1,R4,PC4}/` each hold the branch's commits as `git format-patch`
files, an `uncommitted.patch` of the mid-edit working tree, `status.txt`, and a
`NOTES.md` with the mandate and the definition of done.

**The commits are already merged into this history.** Only the
`uncommitted.patch` needs applying:

```bash
git apply docs/wip/FIX1/uncommitted.patch     # then finish item 4 — see NOTES.md
```

(`git am docs/wip/<name>/0*.patch` is only for replaying them onto a tree that
does not have them.)

**Those three merges were never validated by a live acceptance campaign** — only
offline, by the gate and the suite. The first job of whoever picks this up is to
run `experiments/hadoop/accept` on 17960 and on 11741. README section 9 says
exactly what landed and what did not.

## Before you change anything

Read `docs/planner-memory/` — `MEMORY.md` is the index. The design is fixed:
runtime symbolic propagation carries values, the static graph only *scopes*, an
anchor identifies the same target occurrence across replays, and the composer is
an OR over paths of (path condition AND fatal predicate) solved by z3, gated
fail-closed. Anything that decides what matters outside the slice, finds writers
via the graph, synthesizes a value, or adds a cap, default or heuristic is
rejected. Rows are the authority; refuse by name; delete rather than adapt; one
implementation per notion; state every fix for its whole class; suite <= 100 `@Test` (46 now).

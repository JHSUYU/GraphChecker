# Acceptance harness

Runs a case end to end and says whether it passed: campaign, then a plain z3
probe of the formula the campaign published, then a report. Nothing here
decides what a case proved — `report.py` reads the claim `ClaimPolicy`
published and compares the mechanism against the case's expected one.

## One case

```bash
export CAUSYNTH_CUSTOM_JDK_HOME=/absolute/path/to/j2sdk-image   # required
DRY=1 CASES=hdfs-17960 bash experiments/hadoop/accept/accept.sh # preflight only
CASES=hdfs-17960 bash experiments/hadoop/accept/accept.sh
```

`accept.sh` builds the jar in the repo it is committed in, then per case runs
`lib/run.sh <case dir> <case id> validate` and `... campaign` (which read the
case's declarations, set `lib/execute.sh` as workload and replay command and
exec `run_engine.sh`), with a
fresh `CAUSYNTH_OUTPUT_DIR`. Cases run one at a time.

Defaults, all overridable by environment: `JAR` = `<repo>/target/GraphChecker-
1.0-SNAPSHOT-jar-with-dependencies.jar` (setting it moves the run to that
jar's own repo, because `run_engine.sh` resolves the jar relative to its own
tree), `OUT` = `<repo>/target/accept`, `CASES` = the nine cases in `ACCEPT_ALL_CASES`,
`CASE_TIMEOUT_SECONDS` = 21600, `Z3_BIN` = `z3`, `Z3_TIMEOUT_SECONDS` = 600,
`MIN_FREE_GB` = 6, `PRUNE` = 0. `CAUSYNTH_CUSTOM_JDK_HOME` has no default: unset,
the preflight refuses it by name rather than guessing a VM image.
`SKIP_BUILD=1` reuses the jar already in `<repo>/target`.

## What PASS means

`report.py` reads `<case>/schedule/final/result.json` and passes the case only
when all of these hold:

* `claim` is `SAT_CANDIDATE` and `finalStatus` is `FINAL_READY`;
* THE single criterion on gaps: `gaps.json` names no gap of class BLOCKING, at
  any stage (PLAN, IMPORT, EXPLORE, REPLAY, COMPOSE -- each row states the
  stage that raised it), and the campaign did not withhold the candidate
  (`result.json` `accepted` is true).  `result.json`'s `blockers` are the
  composer's alone and missed PLAN and REPLAY blockers;
* `findingKind` is the mechanism this case is known to fail by —
  `EXPECTED_MECHANISM` at the top of `report.py`. The owner's ruling
  (2026-09-23): every tree of the block-key family carries 11741's expiry
  check, so a key goes stale there ONLY through a failed RPC. hdfs-17899
  bug1/2/3, hdfs-17897 and hdfs-17967 A/B/C therefore pass only with
  `MARKER_FLIPPED` whose `movedRoots` hold an IPC door fault
  (`FAULT:HADOOP_IPC:*`, a marker whose declared site is in
  `org.apache.hadoop.ipc.Client`) flipped to true and **no clock cell** — the
  fault alone reaches the fatal with every clock where the recording read it.
  hdfs-11741 is the bug that check fixes: `CLOCK_SKEW` (a flipped branch with no
  fault), or `MARKER_FLIPPED` should a fault reach its fatal too. hdfs-17960:
  `MARKER_FLIPPED` moving `HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED` to `false`;
* `polarityDecides` is true — the formula is unsatisfiable at the recorded
  valuation, so the mechanism explains the difference between the run that
  failed and the run that did not (only `RECORDED_FAILURE_EXPLAINED` is
  exempt, by construction);
* `valuationOrdinal` >= 1 and `movedRoots` is non-empty — a finding at the
  recorded valuation that moves nothing is the recording restated. A
  `CLOCK_SKEW` finding (11741) is exempt from the ordinal alone: a clock has a
  floor and no window, so the witness sits at the recorded valuation and the
  clock cells the model moved are its `movedRoots`, which must still be
  non-empty.

A case the table does not name cannot pass. The z3 probe is reported, never
gated on: it asks the published formula, unpinned, about the accepted
assignment and about the other polarity, which is a statement about the whole
formula rather than the slice the campaign solved.

## Results

Under `$OUT`: `summary.tsv` (one row per case, verdict and reason),
`logs/<case>.log` (validate + campaign output), `out/<case>/` (the campaign's
own tree, including `schedule/final/`), and per case under `report/<case>/`:
`report.md` (the readable narrative), `row.tsv` (its summary row),
`probe.tsv` + `probe/polarity.json` (what each polarity asserted and what z3
answered) and `status`.

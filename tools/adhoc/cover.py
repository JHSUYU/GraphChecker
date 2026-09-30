#!/usr/bin/env python3
"""cover.py <sweep-dir> <adhoc-experiment-dir> jobs [per-recording] [per-check]
   cover.py <sweep-dir> <adhoc-experiment-dir> cases <prescreen-dir>

Which tests pre-screen the selected checks, and which (check, test) pairs a
sweep then runs.

jobs: a greedy cover of <sweep-dir>/selected.jsonl (select.py rank) by the
usable workloads that reach each check (coverage_runs.py): again and again
the workload with the most selected checks that still have fewer than
<per-check> (2) pre-screening workloads, per second of its coverage run,
taking at most <per-recording> (16) of them, until every check has its
workloads or no workload is left.  Writes <sweep-dir>/prescreen-jobs.tsv,
one recording per row, "<workload><TAB><bound-seconds><TAB><check> ...":
the workload as a case id names it, the recording's wall-clock bound (five
times the coverage run, at least 300 s).  prescreen.sh records them.

cases: reads each batch's runtime/record-summary.json under <prescreen-dir>
(prescreen.sh's) and the experiment's batches.tsv, and writes
<sweep-dir>/cases.txt, sweep.sh's cases: the case ids
"<experiment>-<check>.<workload>" of the pairs whose workload passed and
whose recording ACTIVATED the check: every such check on its fastest
recording, preferring a workload not yet on four checks, then a second one
where a workload under four is left.  Every pair it leaves out is counted by
why on stderr."""
import collections
import glob
import json
import os
import sys

from coverage_runs import case_workload, usable_workloads

PER_WORKLOAD, PER_CASE_CHECK = 4, 2
BOUND_FACTOR, BOUND_FLOOR = 5, 300


def jobs(sweep, per_recording, per_check):
    selected = [json.loads(line) for line in
                open(os.path.join(sweep, "selected.jsonl"))]
    usable = usable_workloads(sweep, {w for row in selected
                                      for w in row.get("workloads", [])})
    reaches = collections.defaultdict(set)  # workload -> checks
    for row in selected:
        for workload in row.get("workloads", []):
            if workload in usable:
                reaches[workload].add(row["check"])
    covered = collections.Counter()
    rows = []
    while reaches:
        def gain(workload):
            wanted = [c for c in reaches[workload] if covered[c] < per_check]
            return min(len(wanted), per_recording) / max(1, usable[workload])
        workload = max(sorted(reaches), key=gain)
        if gain(workload) == 0:
            break
        checks = sorted((c for c in reaches.pop(workload)
                         if covered[c] < per_check))[:per_recording]
        covered.update(checks)
        rows.append("%s\t%d\t%s" % (case_workload(workload),
                                    max(BOUND_FLOOR, BOUND_FACTOR * usable[workload]),
                                    " ".join(checks)))
    with open(os.path.join(sweep, "prescreen-jobs.tsv"), "w") as out:
        for row in rows:
            out.write(row + "\n")
    unreached = [row["check"] for row in selected if not covered[row["check"]]]
    print("%d recordings for %d checks; %d checks no usable workload reaches: %s"
          % (len(rows), len(selected) - len(unreached), len(unreached),
             " ".join(unreached)), file=sys.stderr)


def cases(sweep, experiment, prescreen):
    batches = {}
    for line in open(os.path.join(experiment, "batches.tsv")):
        if line.strip() and not line.startswith("#"):
            batch, workload, checks = line.rstrip("\n").split("\t")
            batches[batch] = (workload, checks.split())
    pairs = collections.defaultdict(list)  # check -> [(seconds, workload)]
    why = collections.Counter()
    for path in sorted(glob.glob(os.path.join(prescreen, "B*", "runtime",
                                              "record-summary.json"))):
        batch = path.split(os.sep)[-3]
        summary = json.load(open(path))
        workload, _ = batches[batch]
        for check, outcome in summary["targets"].items():
            if summary["exit"] != 0:
                why["the workload exited %d%s" % (
                    summary["exit"], ", timed out" if summary["timedOut"]
                    else "")] += 1
            elif outcome["state"] != "ACTIVATED":
                why[outcome["state"]] += 1
            else:
                pairs[check].append((summary["wallSeconds"], workload))
    used = collections.Counter()
    taken = collections.defaultdict(list)  # check -> its workloads
    # The fewest choices first; the first case of a check is never lost to
    # the cap, only moved to a workload under it where one activated it.
    order = sorted(pairs, key=lambda check: (len(pairs[check]), check))
    for round_ in range(PER_CASE_CHECK):
        for check in order:
            free = [w for _, w in sorted(pairs[check])
                    if w not in taken[check] and used[w] < PER_WORKLOAD]
            rest = [w for _, w in sorted(pairs[check]) if w not in taken[check]]
            workload = (free or (rest if round_ == 0 else []) or [None])[0]
            if workload is not None:
                used[workload] += 1
                taken[check].append(workload)
    name = os.path.basename(os.path.abspath(experiment))
    chosen = ["%s-%s.%s" % (name, check, workload)
              for check in sorted(taken) for workload in taken[check]]
    with open(os.path.join(sweep, "cases.txt"), "w") as out:
        for case in chosen:
            out.write(case + "\n")
    print("%d cases for %d activated checks; pairs left out: %s"
          % (len(chosen), len(pairs), dict(why)), file=sys.stderr)


def main():
    sweep, experiment, mode = sys.argv[1:4]
    if mode == "jobs":
        jobs(sweep, int(sys.argv[4]) if len(sys.argv) > 4 else 16,
             int(sys.argv[5]) if len(sys.argv) > 5 else 2)
    elif mode == "cases":
        cases(sweep, experiment, sys.argv[4])
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()

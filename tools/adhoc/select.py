#!/usr/bin/env python3
"""select.py <sweep-dir> <adhoc-experiment-dir> declare [tree]
   select.py <sweep-dir> <adhoc-experiment-dir> rank <static-dir> <cases-file>

Chooses a sweep's checks by what the engine's own static slice of each can
move (score.py), in two steps around the slices (slice.sh).

declare: every check reach.py found that a sweep can run is declared in the
experiment's checks.tsv -- a new one appended as <Class>-<throw line>, its
two fastest usable workloads in the row -- and printed as one
"<check>.<workload>" line, its fastest usable workload's: slice.sh's cases.
Given the <tree> the sweep runs, a check whose line no longer holds its
`throw new` (the tree moved since coverage) is skipped and named on stderr.
A timeout's check is never declared: an automatic cluster lifts every bound
sized for a native run, so no replay reaches it.

rank: reads <static-dir>/<check>/score.json (slice.sh's $GC_OUT/static/<key>)
of every check of <cases-file> and writes <sweep-dir>/selected.jsonl: the
checks whose slice reaches a root near enough (keep), best score first, at
most three per class so one class does not fill a sweep, each its reach.py
row with its name, score and features; then every twentieth dropped check,
"calibration": true, which a sweep runs to measure what the static slice
misses.  cover.py pre-screens them.  A check with no score.json is named on
stderr.

<sweep-dir> is the coverage sweep's (coverage_runs.py)."""
import collections
import hashlib
import json
import os
import sys

from coverage_runs import case_workload, reached, usable_workloads

PER_CLASS, PER_CHECK, CALIBRATION = 3, 2, 20
TIMEOUT_EXCEPTIONS = {"TimeoutException", "SocketTimeoutException"}


def holds_throw(path, line):
    """Whether the tree's line still is the check's `throw new`."""
    try:
        lines = open(path).read().split("\n")
    except OSError:
        return False
    return 0 < line <= len(lines) and "throw new" in lines[line - 1]


def declared(experiment):
    """(file, throw line) -> check name, of every row checks.tsv declares."""
    names = {}
    for row in open(os.path.join(experiment, "checks.tsv")):
        if row.strip() and not row.startswith("#"):
            name, source, line = row.split("\t")[:3]
            names[(source, int(line))] = name
    return names


def declare(sweep, experiment, tree):
    checks = reached(sweep)
    usable = usable_workloads(sweep, {w for check in checks
                                      for w in check["workloads"]})
    names = declared(experiment)
    rows = []
    for check in checks:
        if check["exception"] in TIMEOUT_EXCEPTIONS:
            continue
        if tree and not holds_throw(os.path.join(tree, check["file"]),
                                    check["throwLine"]):
            print("skipped, moved since coverage: %s:%d"
                  % (check["file"], check["throwLine"]), file=sys.stderr)
            continue
        fastest = sorted((usable[w], w) for w in check["workloads"] if w in usable)
        if not fastest:
            continue
        workloads = [case_workload(w) for _, w in fastest[:PER_CHECK]]
        key = (check["file"], check["throwLine"])
        name = names.get(key)
        if name is None:
            name = "%s-%d" % (check["cls"].rsplit(".", 1)[-1], check["throwLine"])
            names[key] = name
            own = "%s=:%s" % (check["root"], check["cls"].replace(".", "/"))
            rows.append("\t".join([name, check["file"], str(check["throwLine"]),
                                   own, " ".join(workloads)]))
        print("%s.%s" % (name, workloads[0]))
    with open(os.path.join(experiment, "checks.tsv"), "a") as out:
        for row in rows:
            out.write(row + "\n")


def rank(sweep, experiment, root, cases_file):
    rows = {(row["file"], row["throwLine"]): row for row in reached(sweep)}
    sites = {name: site for site, name in declared(experiment).items()}
    kept, dropped = [], []
    for line in open(cases_file):
        if not line.strip() or line.startswith("#"):
            continue
        name = line.strip().split(".", 1)[0]
        path = os.path.join(root, name, "score.json")
        if not os.path.exists(path):
            print("no slice: %s (%s)" % (name, path), file=sys.stderr)
            continue
        score = json.load(open(path))
        row = dict(rows.get(sites[name], {}), check=name)
        row.update((k, v) for k, v in score.items() if k not in ("roots", "unrooted"))
        (kept if score["keep"] else dropped).append(row)
    kept.sort(key=lambda row: (-row["score"], row["check"]))
    per_class = collections.Counter()
    chosen = []
    for row in kept:
        cls = os.path.basename(sites[row["check"]][0])
        if per_class[cls] < PER_CLASS:
            per_class[cls] += 1
            chosen.append(row)
    chosen += [dict(row, calibration=True) for row in dropped
               if hashlib.sha256(row["check"].encode()).digest()[0]
               % CALIBRATION == 0]
    with open(os.path.join(sweep, "selected.jsonl"), "w") as out:
        for row in chosen:
            out.write(json.dumps(row, sort_keys=True) + "\n")
    print("kept %d of %d scored checks, %d after %d per class, and %d "
          "calibration" % (len(kept), len(kept) + len(dropped),
                           sum(per_class.values()), PER_CLASS,
                           len(chosen) - sum(per_class.values())),
          file=sys.stderr)


def main():
    sweep, experiment, mode = sys.argv[1:4]
    if mode == "declare":
        declare(sweep, experiment, sys.argv[4] if len(sys.argv) > 4 else "")
    elif mode == "rank":
        rank(sweep, experiment, sys.argv[4], sys.argv[5])
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()

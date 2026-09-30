#!/usr/bin/env python3
"""select.py <sweep-dir> <adhoc-experiment-dir> declare [tree]
   select.py <sweep-dir> <adhoc-experiment-dir> rank <static-dir> <cases-file>

Chooses a sweep's checks by what the engine's own static slice of each can
move (score.py), in two steps around the slices (slice.sh).

declare: every check reach.py found that a sweep can run is declared in the
experiment's checks.tsv -- a new one appended as <Class>-<throw line>, its
<per-check> (2) fastest usable workloads in the row -- and printed as one
"<check>.<workload>" line, its fastest usable workload's: slice.sh's cases.
Given the <tree> the sweep runs, a check whose line no longer holds its
`throw new` (the tree moved since coverage) is skipped and named on stderr.

rank: reads <static-dir>/<check>/score.json (slice.sh's $GC_OUT/static/<key>)
of every check of <cases-file> and writes <sweep-dir>/selected.jsonl: the
checks whose slice reaches a root (keep), best score first, at most three per
class so one class does not fill a sweep, each its reach.py row with its
name, score and features; then every twentieth dropped check, "calibration":
true, which a sweep runs to measure what the static slice misses.  Prints each
one's case id, "<experiment>-<check>.<workload>", its <cases-file> workload's.
A check with no score.json is named on stderr.

<sweep-dir> holds reached.jsonl (reach.py), workloads.tsv (the coverage
sweep's "<test class><TAB><method>" rows), cov-jobs.txt and cov-fanout.log
(the coverage sweep's fanout.sh jobs and log: how long each workload ran).
A workload is usable where its coverage run passed (coverage.sh exits with
the test's status: its recording fails the same way), ran the system's node
class (system.sh's system_node_class, the marker coverage.sh leaves: a test
that starts no node opens no recording window) and names its test class
unambiguously.  A timeout's check is never declared: an automatic cluster
lifts every bound sized for a native run, so no replay reaches it."""
import collections
import hashlib
import json
import os
import re
import sys

sweep, experiment, mode = sys.argv[1:4]
PER_CLASS, PER_CHECK, CALIBRATION = 3, 2, 20
TIMEOUT_EXCEPTIONS = {"TimeoutException", "SocketTimeoutException"}
checks_tsv = os.path.join(experiment, "checks.tsv")


def holds_throw(path, line):
    """Whether the tree's line still is the check's `throw new`."""
    try:
        lines = open(path).read().split("\n")
    except OSError:
        return False
    return 0 < line <= len(lines) and "throw new" in lines[line - 1]


def declared():
    """(file, throw line) -> check name, of every row checks.tsv declares."""
    names = {}
    for row in open(checks_tsv):
        if row.strip() and not row.startswith("#"):
            name, source, line = row.split("\t")[:3]
            names[(source, int(line))] = name
    return names


def usable_workloads(reaching):
    """Each passing, node-starting, unambiguous workload's coverage seconds;
    one of <reaching> that is not usable is named on stderr.  fanout.sh
    logs "<job> <host> exit=<status> <seconds>s", job n being line n of the
    jobs file, whose last word is the workload's output prefix."""
    jobs = [line.split()[-1] for line in open(os.path.join(sweep, "cov-jobs.txt"))
            if line.strip()]
    seconds, failed = {}, {}
    for line in open(os.path.join(sweep, "cov-fanout.log")):
        match = re.match(r"(\d+) \S+ exit=(\d+) (\d+)s$", line.strip())
        if match:
            workload = os.path.basename(jobs[int(match.group(1))])
            if match.group(2) == "0":
                seconds[workload] = int(match.group(3))
            else:
                failed[workload] = match.group(2)
    classes = collections.defaultdict(set)
    for line in open(os.path.join(sweep, "workloads.tsv")):
        test_class, _ = line.rstrip("\n").split("\t")
        classes[test_class.rsplit(".", 1)[-1]].add(test_class)
    usable = {}
    for workload in sorted(reaching):
        if workload in failed:
            print("skipped, its test failed under coverage (exit=%s): %s"
                  % (failed[workload], workload), file=sys.stderr)
        elif workload in seconds and not os.path.exists(
                os.path.join(sweep, "cov", workload + ".node")):
            print("skipped, starts no node: %s" % workload, file=sys.stderr)
        elif workload in seconds and len(classes[workload.split(".")[0]]) == 1:
            usable[workload] = seconds[workload]
    return usable


def reached():
    return [json.loads(line) for line in open(os.path.join(sweep, "reached.jsonl"))]


def declare(tree):
    checks = reached()
    usable = usable_workloads({w for check in checks for w in check["workloads"]})
    names = declared()
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
        workloads = [w.replace(".", "-", 1) for _, w in fastest[:PER_CHECK]]
        key = (check["file"], check["throwLine"])
        name = names.get(key)
        if name is None:
            name = "%s-%d" % (check["cls"].rsplit(".", 1)[-1], check["throwLine"])
            names[key] = name
            own = "%s=:%s" % (check["root"], check["cls"].replace(".", "/"))
            rows.append("\t".join([name, check["file"], str(check["throwLine"]),
                                   own, " ".join(workloads)]))
        print("%s.%s" % (name, workloads[0]))
    with open(checks_tsv, "a") as out:
        for row in rows:
            out.write(row + "\n")


def rank(root, cases_file):
    rows = {(row["file"], row["throwLine"]): row for row in reached()}
    sites = {name: site for site, name in declared().items()}
    kept, dropped, workload = [], [], {}
    for line in open(cases_file):
        if not line.strip() or line.startswith("#"):
            continue
        name, workload[name] = line.strip().split(".", 1)
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
            print("%s-%s.%s" % (os.path.basename(os.path.abspath(experiment)),
                                row["check"], workload[row["check"]]))
    print("kept %d of %d scored checks, %d after %d per class, and %d "
          "calibration" % (len(kept), len(kept) + len(dropped),
                           sum(per_class.values()), PER_CLASS,
                           len(chosen) - sum(per_class.values())),
          file=sys.stderr)


if mode == "declare":
    declare(sys.argv[4] if len(sys.argv) > 4 else "")
elif mode == "rank":
    rank(sys.argv[4], sys.argv[5])
else:
    sys.exit(__doc__)

"""What a coverage sweep's directory says, for select.py and cover.py.

<sweep-dir> holds reached.jsonl (reach.py), workloads.tsv (workloads.py:
"<test class><TAB><method>" rows), cov-jobs.txt and cov-fanout.log (the
coverage sweep's fanout.sh jobs and log: how long each workload ran, and
with what status), and cov/<workload>.node, the marker coverage.sh leaves
for a run that started a node.  A workload is named "<TestClass>.<method>".
"""
import collections
import json
import os
import re
import sys


def reached(sweep):
    """reach.py's rows: every reached check, with its workloads."""
    with open(os.path.join(sweep, "reached.jsonl")) as rows:
        return [json.loads(line) for line in rows]


def usable_workloads(sweep, reaching):
    """Each usable workload's coverage seconds: its run passed (coverage.sh
    exits with the test's status, and its recording fails the same way),
    started a node of the system (a test that starts none opens no
    recording window) and names its test class unambiguously.  One of
    <reaching> that is not usable is named on stderr.  fanout.sh logs
    "<job> <host> exit=<status> <seconds>s", job n being line n of the jobs
    file, whose last word is the workload's output prefix."""
    with open(os.path.join(sweep, "cov-jobs.txt")) as lines:
        jobs = [line.split()[-1] for line in lines if line.strip()]
    seconds, failed = {}, {}
    with open(os.path.join(sweep, "cov-fanout.log")) as log:
        for line in log:
            match = re.match(r"(\d+) \S+ exit=(\d+) (\d+)s$", line.strip())
            if match:
                workload = os.path.basename(jobs[int(match.group(1))])
                if match.group(2) == "0":
                    seconds[workload] = int(match.group(3))
                else:
                    failed[workload] = match.group(2)
    classes = collections.defaultdict(set)
    with open(os.path.join(sweep, "workloads.tsv")) as rows:
        for line in rows:
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


def case_workload(workload):
    """A coverage workload as a case id names it: <TestClass>-<method>."""
    return workload.replace(".", "-", 1)

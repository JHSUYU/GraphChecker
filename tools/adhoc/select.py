#!/usr/bin/env python3
"""select.py <system-dir> <sweep-dir> <adhoc-experiment-dir> <checks> [per-check] [tree]

Chooses a sweep's checks and cases from what reach.py found: ranks every
reached check by how much of its guard is state that another node sends or a
clock decides, takes the best <checks> of them that the experiment does not
already declare -- at most three per class, so one class does not fill a
sweep -- and appends them to the experiment's checks.tsv, named
<Class>-<throw line>.  Each check runs on its <per-check> (default 2)
fastest workloads, no workload on more than four checks.  Prints the case ids,
"<experiment>-<check>.<TestClass>-<method>", one per line.

<sweep-dir> holds reached.jsonl (reach.py), workloads.tsv (the coverage
sweep's "<test class><TAB><method>" rows), cov-jobs.txt and cov-fanout.log
(the coverage sweep's fanout.sh jobs and log: how long each workload ran).
The system's system.sh names in system_focus the classes where its nodes
coordinate; their checks rank first.

A timeout's check is never chosen: an automatic cluster lifts every bound
sized for a native run, so no replay reaches it.  Nor is a workload whose
coverage never ran the system's node class (system.sh's system_node_class):
a test that starts no node opens no recording window, so its seed fails.  Given the <tree> the sweep
annotates, a check whose line no longer holds its `throw new` (the tree moved
since coverage) is skipped and named on stderr."""
import collections
import json
import os
import re
import subprocess
import sys

system_dir, sweep, experiment = sys.argv[1], sys.argv[2], sys.argv[3]
wanted = int(sys.argv[4])
per_check = int(sys.argv[5]) if len(sys.argv) > 5 else 2
tree = sys.argv[6] if len(sys.argv) > 6 else ""
PER_CLASS, PER_WORKLOAD = 3, 4

def system_value(name):
    return subprocess.run(
        ["bash", "-c", 'source "$1/system.sh" && printf %%s "${%s}"' % name,
         "-", system_dir], check=True, capture_output=True,
        text=True).stdout


focus = system_value("system_focus")

# What the guard reads, weighed by whether a remote write or a clock decides
# it: a clock or expiry, a version another node stamped, a node's view of the
# cluster, durable or secret state.  A guard over the call's own arguments is
# input validation, and one over the node's own disk is start-up, not
# coordination.
SIGNALS = [
    (4, r"currentTimeMillis|nanoTime|monotonicNow|Time\.now|\bnow\b|[Ee]xpir"
        r"|[Tt]imeout|[Dd]eadline|[Ll]ease|[Ee]lapsed|[Ss]tale|lastUpdate"),
    (3, r"[Vv]ersion|[Gg]eneration|[Gg]en[Ss]tamp|\bgen\b|[Ee]poch|\bterm\b"
        r"|[Tt]erm\(|[Tt]x[Ii]d|[Ss]eq[Nn]o|[Kk]eyId|[Ss]erial|[Cc]ookie"),
    (3, r"[Cc]lusterState|getCollection|getSlice|getReplica|[Ll]eader"
        r"|liveNodes|isLive|[Aa]live|[Dd]ecommission|[Mm]aintenance"
        r"|HAState|isActive|[Ss]tandby|[Ss]afe[Mm]ode|[Rr]egist|[Bb]lockPool"
        r"|getState\(|[Ss]tate\b|UNDER_CONSTRUCTION|[Rr]ecover|[Rr]outing"),
    (2, r"[Cc]ommit|isDeleted|[Rr]eserve|[Cc]heckpoint|[Ee]dit[Ll]og|[Jj]ournal"
        r"|[Ff]inaliz|[Rr]ollback|[Ss]napshot|[Tt]oken|[Ss]ecret|BlockKey"),
]
VALIDATION = (r"== null|!= null|isEmpty\(\)|instanceof|Preconditions|[Pp]arams?\b"
              r"|\brequired\b|[Cc]onf\b|conf\.|[Pp]arse|[Ss]yntax|[Ss]chema"
              r"|[Ff]ield|[Pp]ermission|[Aa]cl\b|[Ll]ength|[Ff]ormat|\bargs?\b")
# A node's own disk: the layout it upgrades from, what it finds on start-up.
LOCAL = (r"[Ll]ayout[Vv]ersion|LAYOUT|getPreviousDir|canRollback|StartupOption"
         r"|[Ss]ymlink|isReservedName|logVersion|exists\(\)")
TIMEOUT_EXCEPTIONS = {"TimeoutException", "SocketTimeoutException"}
ARGUMENT_EXCEPTIONS = {
    "IllegalArgumentException", "HadoopIllegalArgumentException",
    "InvalidPathException", "AclException", "SyntaxError",
    "AccessControlException", "UnsupportedOperationException",
    "NumberFormatException", "InvalidRequestException"}


def holds_throw(path, line):
    """Whether the tree's line still is the check's `throw new`."""
    try:
        lines = open(path).read().split("\n")
    except OSError:
        return False
    return 0 < line <= len(lines) and "throw new" in lines[line - 1]


def starts_a_node(workload):
    """Whether the workload's coverage ran the system's node class: the
    marker coverage.sh leaves (reading every .lines file took HDFS's 2818
    workloads over half an hour)."""
    return os.path.exists(os.path.join(sweep, "cov", workload + ".node"))


def score(check):
    text = check["cond"] + " " + check["operand"]
    value = sum(weight for weight, pattern in SIGNALS if re.search(pattern, text))
    if re.search(VALIDATION, text):
        value -= 2
    if re.search(LOCAL, text):
        value -= 4
    if check["exception"] in ARGUMENT_EXCEPTIONS:
        value -= 3
    if focus and re.search(focus, check["cls"]):
        value += 2
    return value


# How long each workload ran under coverage: fanout.sh logs "<job> <host>
# exit=<status> <seconds>s", job n being line n of the jobs file, whose last
# word is the workload's output prefix.
jobs = [line.split()[-1] for line in open(os.path.join(sweep, "cov-jobs.txt"))
        if line.strip()]
seconds = {}
for line in open(os.path.join(sweep, "cov-fanout.log")):
    match = re.match(r"(\d+) \S+ exit=0 (\d+)s$", line.strip())
    if match:
        seconds[os.path.basename(jobs[int(match.group(1))])] = int(match.group(2))
# A workload is named by its test class's simple name: one two packages share
# names none.
classes = collections.defaultdict(set)
for line in open(os.path.join(sweep, "workloads.tsv")):
    test_class, _ = line.rstrip("\n").split("\t")
    classes[test_class.rsplit(".", 1)[-1]].add(test_class)

declared = set()
checks_tsv = os.path.join(experiment, "checks.tsv")
for row in open(checks_tsv):
    if row.strip() and not row.startswith("#"):
        _, source, line = row.split("\t")[:3]
        declared.add((source, int(line)))

reached = [json.loads(line) for line in open(os.path.join(sweep, "reached.jsonl"))]
nodeless = sorted({w for check in reached for w in check["workloads"]
                   if not starts_a_node(w)})
for workload in nodeless:
    print("skipped, starts no node: %s" % workload, file=sys.stderr)
reached.sort(key=lambda check: (-score(check), len(check["workloads"])))
per_class = collections.Counter()
per_workload = collections.Counter()
rows, cases = [], []
for check in reached:
    if len(rows) == wanted:
        break
    cls = check["cls"].rsplit(".", 1)[-1]
    if (check["file"], check["throwLine"]) in declared or per_class[cls] == PER_CLASS:
        continue
    if check["exception"] in TIMEOUT_EXCEPTIONS:
        continue
    if tree and not holds_throw(os.path.join(tree, check["file"]),
                                check["throwLine"]):
        print("skipped, moved since coverage: %s:%d"
              % (check["file"], check["throwLine"]), file=sys.stderr)
        continue
    usable = sorted((seconds[w], w) for w in check["workloads"]
                    if w in seconds and w not in nodeless
                    and len(classes[w.split(".")[0]]) == 1
                    and per_workload[w] < PER_WORKLOAD)
    chosen = [w for _, w in usable[:per_check]]
    if not chosen:
        continue
    name = "%s-%d" % (cls, check["throwLine"])
    workloads = [w.replace(".", "-", 1) for w in chosen]
    per_class[cls] += 1
    per_workload.update(chosen)
    own = "%s=:%s" % (check["root"], check["cls"].replace(".", "/"))
    rows.append("\t".join([name, check["file"], str(check["throwLine"]), own,
                           " ".join(workloads)]))
    cases += ["%s-%s.%s" % (os.path.basename(experiment), name, w)
              for w in workloads]
with open(checks_tsv, "a") as out:
    for row in rows:
        out.write(row + "\n")
for case in cases:
    print(case)

#!/usr/bin/env python3
"""reached.py COVDIR [WORKLOADS_TSV] : throw sites whose guarding `if` ran on a workload's healthy path while
the throw itself did not -- an ad-hoc check the recording evaluates and passes.
Reads COVDIR/workloads.tsv, <name>.lines and throwsites-<name>.jsonl; prints JSON rows."""
import sys, json, os, collections
d = sys.argv[1]
out = collections.OrderedDict()
for row in open(sys.argv[2] if len(sys.argv) > 2 else os.path.join(d, "workloads.tsv")):
    name, tree = row.split("\t")[:2]
    cov = collections.defaultdict(set)
    for l in open(os.path.join(d, name + ".lines")):
        c, n = l.rstrip("\n").split("\t"); cov[c.split("$")[0]].add(int(n))
    for l in open(os.path.join(d, "throwsites-%s.jsonl" % name)):
        s = json.loads(l)
        if s["condLine"] <= 0: continue
        lines = cov.get(s["cls"].replace(".", "/"), set())
        if s["condLine"] in lines and s["throwLine"] not in lines:
            key = (s["cls"], s["cond"], s["operand"])
            e = out.setdefault(key, dict(s, workloads=[]))
            e["workloads"].append(name)
for e in out.values(): print(json.dumps(e))

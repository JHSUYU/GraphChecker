#!/usr/bin/env python3
"""reach.py <sites.jsonl> <coverage-dir> : the checks a workload's healthy
path evaluates and passes -- the guarding `if` ran, the throw did not -- one
JSON row per check with every workload that reaches it.  <coverage-dir> holds
<workload>.lines (coverage.sh), the workload named by the file."""
import collections
import json
import os
import sys

sites = [json.loads(line) for line in open(sys.argv[1])]
cover = sys.argv[2]
reached = collections.OrderedDict()
for name in sorted(os.listdir(cover)):
    if not name.endswith(".lines"):
        continue
    workload = name[:-len(".lines")]
    executed = collections.defaultdict(set)
    for line in open(os.path.join(cover, name)):
        cls, number = line.rstrip("\n").split("\t")
        executed[cls.split("$")[0]].add(int(number))
    for site in sites:
        lines = executed.get(site["cls"].replace(".", "/"), ())
        if site["condLine"] in lines and site["throwLine"] not in lines:
            key = (site["file"], site["throwLine"])
            row = reached.setdefault(key, dict(site, workloads=[]))
            row["workloads"].append(workload)
for row in reached.values():
    print(json.dumps(row))

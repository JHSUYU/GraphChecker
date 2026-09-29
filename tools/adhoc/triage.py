#!/usr/bin/env python3
"""triage.py <round> [gc-out] : one row per case of a sweep (sweep.sh), from
its summary and its final result: the case, the class of its outcome, the
finding and moved roots, the confirmation, the elapsed seconds, and where a
campaign failed, the stage and reason.

Classes:
  CONFIRMED     a SAT witness the program agreed with (confirmation true): a
                candidate bug, to read by hand
  REFUTED       a SAT witness CONFIRM could not realize: a false positive the
                engine filtered
  NO_WITNESS    the corpus supports no witness (or none at the recorded path)
  STOPPED       the campaign failed at a stage: the stage and its reason
  RUNNING       no summary yet"""
import csv
import glob
import json
import os
import re
import sys

round_name = sys.argv[1]
out = sys.argv[2] if len(sys.argv) > 2 else os.path.expanduser("~/gc-out")
cases = dict(line.rstrip("\n").split("\t", 1)
             for line in open(os.path.join(out, "sweep-%s-cases.tsv" % round_name)))
rows = []
for n, case in sorted(cases.items(), key=lambda item: int(item[0])):
    root = os.path.join(out, "accept-%s-%s" % (round_name, n))
    summary = os.path.join(root, "summary.tsv")
    row = {"n": n, "case": case, "class": "RUNNING", "elapsed": "",
           "finding": "", "confirmed": "", "stage": "", "reason": ""}
    if os.path.exists(summary):
        lines = list(csv.DictReader(open(summary), delimiter="\t"))
        if lines:
            last = lines[-1]
            row["elapsed"] = last.get("elapsed", "")
            row["finding"] = last.get("finding", "")[:160]
    results = glob.glob(os.path.join(root, "out", "*", "schedule", "final", "result.json"))
    if results:
        result = json.load(open(results[0]))
        confirmation = result.get("confirmation") or {}
        row["confirmed"] = confirmation.get("confirmed", "")
        claim = result.get("claim", "")
        if claim == "SAT_CANDIDATE" and confirmation.get("confirmed") is True:
            row["class"] = "CONFIRMED"
        elif claim == "SAT_CANDIDATE":
            row["class"] = "REFUTED"
        else:
            row["class"] = "NO_WITNESS"
        row["finding"] = (result.get("findingKind", "") + " "
                          + ",".join(r if isinstance(r, str) else r.get("rootId", "")
                                     for r in result.get("movedRoots", []) or []))[:160]
    elif os.path.exists(summary):
        logs = [p for p in glob.glob(os.path.join(root, "logs", "*.log"))
                if "driver" not in p]
        text = open(logs[0], errors="replace").read() if logs else ""
        stage = re.findall(r"stage=(\w+)", text)
        reason = re.findall(r"reason=(.*)", text)
        row["class"] = "STOPPED"
        row["stage"] = stage[-1] if stage else ""
        row["reason"] = (reason[-1] if reason else "")[:200]
    rows.append(row)
writer = csv.DictWriter(sys.stdout, fieldnames=list(rows[0].keys()), delimiter="\t")
writer.writeheader()
writer.writerows(rows)
counts = {}
for row in rows:
    counts[row["class"]] = counts.get(row["class"], 0) + 1
print("# " + " ".join("%s=%d" % item for item in sorted(counts.items())), file=sys.stderr)

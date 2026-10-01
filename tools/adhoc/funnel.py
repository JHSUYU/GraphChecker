#!/usr/bin/env python3
"""funnel.py <night-dir> <static-dir> <prescreen-dir> : a nightly sweep's
report (nightly.sh), as Markdown on stdout.

The funnel counts what each step kept: the checks coverage reached
(reached.jsonl), the declared ones a usable workload reaches (declared.txt),
those with a slice (<static-dir>/<check>/score.json), those the slice keeps,
the selection (at most three per class) and its calibration tail
(selected.jsonl), the pre-screen's recordings and the pairs they activated
(prescreen-jobs.tsv, <prescreen-dir>/<batch>/runtime/record-summary.json),
the batch cases (cases.txt) and their checks' outcomes (triage.tsv).  The
outcome of the kept checks' cases stands beside the calibration checks':
a calibration case that reaches COMPOSE with a witness is one the static
selection would have dropped.  findings.tsv's mechanisms close it: the new
ones, and the known bugs the sweep found again."""
import collections
import csv
import json
import os
import sys

CLASSES = ("CONFIRMED", "REFUTED", "NO_WITNESS", "STOPPED", "DEAD",
           "RUNNING", "PENDING")


def lines(path):
    if not os.path.exists(path):
        return []
    return [line.rstrip("\n") for line in open(path)
            if line.strip() and not line.startswith("#")]


def main():
    night, static, prescreen = sys.argv[1:4]
    manifest = json.load(open(os.path.join(night, "manifest.json")))
    declared = [case.split(".", 1)[0]
                for case in lines(os.path.join(night, "declared.txt"))]
    scores = [json.load(open(os.path.join(static, check, "score.json")))
              for check in declared
              if os.path.exists(os.path.join(static, check, "score.json"))]
    selected = [json.loads(row)
                for row in lines(os.path.join(night, "selected.jsonl"))]
    calibration = {row["check"] for row in selected if row.get("calibration")}
    recordings = [row.split("\t")
                  for row in lines(os.path.join(night, "prescreen-jobs.tsv"))]
    recorded = activated = 0
    for batch, _, _, _ in recordings:
        path = os.path.join(prescreen, batch, "runtime", "record-summary.json")
        if os.path.exists(path):
            summary = json.load(open(path))
            recorded += 1
            activated += sum(1 for outcome in summary["targets"].values()
                             if summary["exit"] == 0
                             and outcome["state"] == "ACTIVATED")
    cases = lines(os.path.join(night, "cases.txt"))
    triage = list(csv.DictReader(open(os.path.join(night, "triage.tsv")),
                                 delimiter="\t"))
    findings = list(csv.DictReader(open(os.path.join(night, "findings.tsv")),
                                   delimiter="\t"))
    print("# Nightly %s\n" % os.path.basename(night.rstrip("/")))
    print("Snapshot `%s` (%s, `%s`), build key `%s`, VM `%s`, tree `%s` @ `%s`.\n"
          % (manifest["snapshot"], manifest["tag"], manifest["commit"][:12],
             manifest["buildKey"], manifest["vm"]["path"],
             manifest["tree"]["path"], manifest["tree"]["commit"][:12]))
    print("| step | count |\n| --- | --- |")
    for label, count in (
            ("checks coverage reached",
             len(lines(os.path.join(night, "reached.jsonl")))),
            ("declared (a usable workload reaches it)", len(declared)),
            ("sliced", len(scores)),
            ("kept by the slice", sum(1 for s in scores if s["keep"])),
            ("selected (at most three per class)",
             len(selected) - len(calibration)),
            ("calibration (every twentieth dropped check)", len(calibration)),
            ("pre-screen recordings (finished)",
             "%d (%d)" % (len(recordings), recorded)),
            ("(check, test) pairs activated", activated),
            ("batch cases (one recording each)", len(cases)),
            ("checks run in them", len(triage))):
        print("| %s | %s |" % (label, count))
    by = collections.defaultdict(collections.Counter)
    for row in triage:
        # A batch case's row is "<experiment>-B<n>/<check>" (triage.py).
        check = row["case"].rsplit("/", 1)[-1]
        by["calibration" if check in calibration else "kept"][row["class"]] += 1
    print("\n| outcome | kept | calibration |\n| --- | --- | --- |")
    for name in CLASSES:
        print("| %s | %d | %d |" % (name, by["kept"][name],
                                    by["calibration"][name]))
    new = [row for row in findings if row["status"] == "new"]
    print("\n%d mechanism(s) among the confirmed witnesses, %d new%s"
          % (len(findings), len(new), ":" if new else "."))
    for row in new:
        print("- `%s` %s %s: %s (%s)" % (row["sig"], row["kind"], row["target"],
                                          row["moved roots"], row["best case"]))
    # The known bugs the sweep found again (findings.py --annotated).
    known = [row for row in findings if row.get("known bug")]
    print("\n%d mechanism(s) at a known bug's marked site%s"
          % (len(known), ":" if known else "."))
    for row in known:
        print("- %s: `%s` %s, %s (%s)" % (row["known bug"], row["sig"],
                                           row["kind"], row["moved roots"],
                                           row["best case"]))


if __name__ == "__main__":
    main()

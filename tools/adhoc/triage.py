#!/usr/bin/env python3
"""triage.py <round> [gc-out] : one row per case of a sweep (sweep.sh), from
its summary and its final result: the case, the class of its outcome, the
finding and moved roots, the confirmation, the elapsed seconds, and where a
campaign failed, the stage and reason.

Classes:
  CONFIRMED     a SAT witness the program agreed with (confirmation true): a
                candidate bug, to read by hand
  REFUTED       a SAT witness CONFIRM could not realize (EMIT publishes it
                SAT_UNCONFIRMED): a false positive the engine filtered, the
                confirmation's reason as the reason
  NO_WITNESS    the corpus supports no witness (or none at the recorded path)
  STOPPED       the campaign failed at a stage: the stage and its reason
  DEAD          started, no verdict, and no process on any lift names its
                directory any more (a quota, a reboot, stop-run.sh)
  RUNNING       started, no verdict yet, still running (or a lift did not
                answer, which the reason says)
  PENDING       not started

A STOPPED or DEAD case's reason is what its logs state: the campaign's own
failure, the case timeout, a stage's Java main or trace aggregation that
failed, a full disk or quota.  LIFTS (default lift06-15) are the hosts
asked whether a run is still alive."""
import concurrent.futures
import csv
import glob
import json
import os
import re
import subprocess
import sys

round_name = sys.argv[1]
out = sys.argv[2] if len(sys.argv) > 2 else os.path.expanduser("~/gc-out")
lifts = os.environ.get("LIFTS", " ".join(
    "lift%02d" % n for n in range(6, 16))).split()
cases = dict(line.rstrip("\n").split("\t", 1)
             for line in open(os.path.join(out, "sweep-%s-cases.tsv" % round_name)))

# A run is named by its output directory, the rule tools/rounds/stop-run.sh
# stops it by: in the command line of everything below the harness, and as
# OUT in the harness's own environment.  Printed per directory some process
# of this user still names (never the scan's own shell, which names them all).
SCAN = r'''
for pid in $(pgrep -u "$(id -un)"); do
  [[ ${pid} == $$ ]] && continue
  args=$(tr '\0' ' ' <"/proc/${pid}/cmdline" 2>/dev/null)
  env=$(tr '\0' '\n' <"/proc/${pid}/environ" 2>/dev/null | grep -m 1 '^OUT=')
  for dir in "$@"; do
    [[ ${args} == *"${dir}/"* || ${env} == "OUT=${dir}" ]] && echo "${dir}"
  done
done | sort -u
'''


def alive(dirs):
    """The directories some lift still runs, and the lifts that did not say."""
    def ask(host):
        try:
            done = subprocess.run(
                ["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=10", host,
                 "bash", "-s", "--"] + dirs, input=SCAN, capture_output=True,
                text=True, timeout=120)
        except subprocess.TimeoutExpired:
            return host, None
        return host, done.stdout.split() if done.returncode == 0 else None
    running, silent = set(), []
    if not dirs:
        return running, silent
    with concurrent.futures.ThreadPoolExecutor(len(lifts) or 1) as pool:
        for host, named in pool.map(ask, lifts):
            if named is None:
                silent.append(host)
            else:
                running.update(named)
    return running, silent


# What a log states about why a run ended, most specific first: the trace
# aggregation (SEED's silent stop), a stage's Java main, the engine's die(),
# a full disk or quota (the write that failed names it).
STATED = [r"Failed to aggregate Causynth runtime trace: (.*)",
          r'Exception in thread "main" (.*)',
          r"^Error: (.*)",
          r"(.*(?:Disk quota exceeded|No space left on device).*)"]


def stated(root, case_text):
    """(stage, reason) as the case's logs and status state them."""
    stage = re.findall(r"stage=(\w+)", case_text)
    reason = re.findall(r"reason=(.*)", case_text)
    if stage and reason:
        return stage[-1], reason[-1]
    begun = re.findall(r"\[campaign\] stage (\w+)", case_text)
    stage = begun[-1] if begun else ""
    status = "".join(open(path).read() for path in glob.glob(
        os.path.join(root, "report", "*", "status")))
    if re.search(r"exit=124\b", status):
        elapsed = re.findall(r"elapsed=(\w+)", status)
        return stage, "killed at the case timeout%s" % (
            " after " + elapsed[-1] if elapsed else "")
    for pattern in STATED:
        found = re.findall(pattern, case_text, re.M)
        if found:
            return stage, found[-1].strip()
    return stage, ""


rows = []
for n, case in sorted(cases.items(), key=lambda item: int(item[0])):
    root = os.path.join(out, "accept-%s-%s" % (round_name, n))
    summary = os.path.join(root, "summary.tsv")
    row = {"n": n, "case": case,
           "class": "RUNNING" if os.path.isdir(root) else "PENDING",
           "elapsed": "", "finding": "", "confirmed": "", "stage": "",
           "reason": ""}
    lines = (list(csv.DictReader(open(summary), delimiter="\t"))
             if os.path.exists(summary) else [])
    if lines:
        row["elapsed"] = lines[-1].get("elapsed", "")
        row["finding"] = lines[-1].get("finding", "")[:160]
    results = glob.glob(os.path.join(root, "out", "*", "schedule", "final", "result.json"))
    logs = sorted(glob.glob(os.path.join(root, "logs", "*.log")))
    text = "\n".join(open(path, errors="replace").read() for path in logs)
    if results:
        result = json.load(open(results[0]))
        confirmation = result.get("confirmation") or {}
        row["confirmed"] = confirmation.get("confirmed", "")
        claim = result.get("claim", "")
        if claim == "SAT_CANDIDATE" and confirmation.get("confirmed") is True:
            row["class"] = "CONFIRMED"
        elif claim == "SAT_UNCONFIRMED":
            row["class"] = "REFUTED"
            row["reason"] = confirmation.get("reason", "")[:200]
        else:
            row["class"] = "NO_WITNESS"
        row["finding"] = (result.get("findingKind", "") + " "
                          + ",".join(r if isinstance(r, str) else r.get("rootId", "")
                                     for r in result.get("movedRoots", []) or []))[:160]
        # What refused the witness, occurrence addresses elided.
        blockers = result.get("blockers") or []
        if blockers and not row["reason"]:
            row["reason"] = re.sub(r"\S*/region/\S*", "<occ>", blockers[0]["kind"]
                                   + " " + blockers[0]["detail"])[:200]
    elif lines:
        row["class"] = "STOPPED"
        row["stage"], row["reason"] = stated(root, text)
        row["reason"] = row["reason"][:200]
    elif row["class"] == "RUNNING":
        # Resolved below, against every lift at once.
        row["stage"], row["reason"] = stated(root, text)
    rows.append(row)

started = [os.path.join(out, "accept-%s-%s" % (round_name, row["n"]))
           for row in rows if row["class"] == "RUNNING"]
running, silent = alive(started)
for row in rows:
    root = os.path.join(out, "accept-%s-%s" % (round_name, row["n"]))
    if row["class"] != "RUNNING":
        continue
    if root in running:
        row["reason"] = ""
    elif silent:
        row["reason"] = ("alive unknown: %s did not answer" % " ".join(silent))
    else:
        row["class"] = "DEAD"
        row["reason"] = ("its head is gone with no verdict"
                         + (": " + row["reason"] if row["reason"] else ""))[:200]
writer = csv.DictWriter(sys.stdout, fieldnames=list(rows[0].keys()), delimiter="\t")
writer.writeheader()
writer.writerows(rows)
counts = {}
for row in rows:
    counts[row["class"]] = counts.get(row["class"], 0) + 1
print("# " + " ".join("%s=%d" % item for item in sorted(counts.items())), file=sys.stderr)

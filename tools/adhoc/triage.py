#!/usr/bin/env python3
"""triage.py <round> [gc-out] : one row per case of a sweep (sweep.sh), from
its summary and its final result: the case, the class of its outcome, the
finding and moved roots, the confirmation, how many claims CONFIRM refuted on
the way (result.json refutedClaims), the elapsed seconds, and where a campaign
failed, the stage and reason.  A batch case (one recording for
several checks, run_engine.sh causynth_static_root) is one row per check,
"<case>/<check>", from that check's own campaign (out/<case>/targets/<check>/)
or, for a check the recording did not activate, its record-summary state.

Classes:
  CONFIRMED     a SAT witness the program agreed with (confirmation true): a
                candidate bug, to read by hand
  REFUTED       no confirmed witness, and CONFIRM refuted a claim on the way
                (a refuted model, which the campaign excludes and follows
                with the next claim or more exploration), or published one
                SAT_UNCONFIRMED: a false positive the engine filtered, the
                last refutation's reason as the reason
  NO_ROOT       no witness, and EXPLORE ended on an anchor every admitted
                path decided on no symbol (NO_ROOT_REACHES_ANCHOR, BLOCKING
                at its fixed point): no root reaches the predicate; the
                gap's detail as the reason (nothing decided on the way to
                the throw, no shared state read before the decision, or the
                reads the closure demanded)
  NO_WITNESS    the corpus supports no witness (or none at the recorded path)
  STOPPED       the campaign failed at a stage: the stage and its reason
  DEAD          started, no verdict, and no process on any lift names its
                directory any more (a quota, a reboot, stop-run.sh)
  RUNNING       started, no verdict yet, still running (or a lift did not
                answer, which the reason says)
  PENDING       not started

A STOPPED or DEAD case's reason is what its logs state: the campaign's own
failure, the case timeout, a stage's Java main or trace aggregation that
failed, a full disk or quota.  <gc-out> defaults to tools/lib/gc-env.sh's
GC_OUT; whether a run is still alive is asked of every lift there
(tools/lib/alive.sh)."""
import csv
import glob
import json
import os
import re
import subprocess
import sys

LIB = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lib")
round_name = sys.argv[1]
out = sys.argv[2] if len(sys.argv) > 2 else subprocess.run(
    ["bash", "-c", 'source "$1/gc-env.sh" && printf %s "${GC_OUT}"', "_", LIB],
    check=True, capture_output=True, text=True).stdout
cases = dict(line.rstrip("\n").split("\t", 1)
             for line in open(os.path.join(out, "sweep-%s-cases.tsv" % round_name)))


def alive(dirs):
    """The directories some lift still runs (a run is named by its output
    directory, the rule tools/rounds/stop-run.sh stops it by), and the lifts
    that did not say."""
    if not dirs:
        return set(), []
    said = subprocess.run(["bash", os.path.join(LIB, "alive.sh")] + dirs,
                          check=True, capture_output=True, text=True).stdout
    rows = [line.split(" ", 1) for line in said.splitlines()]
    return ({what for word, what in rows if word == "alive"},
            [what for word, what in rows if word == "silent"])


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


NO_ROOT = "NO_ROOT_REACHES_ANCHOR"


def no_root(result_path):
    """The detail of the BLOCKING NO_ROOT_REACHES_ANCHOR gap EMIT published
    beside a result (final/gaps.json)."""
    gaps = os.path.join(os.path.dirname(result_path), "gaps.json")
    if not os.path.exists(gaps):
        return ""
    for gap in json.load(open(gaps)).get("gaps", []):
        if gap.get("code") == NO_ROOT:
            return gap.get("detail", "")[:200]
    return ""


def classify(row, result_path, lines, root, text):
    """A row's class from its campaign's result.json, else from its logs:
    stopped once the case has its summary row, else still running."""
    if result_path is not None:
        result = json.load(open(result_path))
        confirmation = result.get("confirmation") or {}
        row["confirmed"] = confirmation.get("confirmed", "")
        claim = result.get("claim", "")
        refuted = result.get("refutedClaims") or []
        row["refuted"] = len(refuted)
        if claim == "SAT_CANDIDATE" and confirmation.get("confirmed") is True:
            row["class"] = "CONFIRMED"
        elif claim == "SAT_UNCONFIRMED" or refuted:
            row["class"] = "REFUTED"
            row["reason"] = (confirmation.get("reason", "")
                             if claim == "SAT_UNCONFIRMED"
                             else refuted[-1].get("reason", ""))[:200]
        elif NO_ROOT in (result.get("blockingGapCodes") or {}):
            row["class"] = "NO_ROOT"
            row["reason"] = no_root(result_path)
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


rows = []
for n, case in sorted(cases.items(), key=lambda item: int(item[0])):
    root = os.path.join(out, "accept-%s-%s" % (round_name, n))
    summary = os.path.join(root, "summary.tsv")
    base = {"n": n, "case": case,
            "class": "RUNNING" if os.path.isdir(root) else "PENDING",
            "elapsed": "", "finding": "", "confirmed": "", "refuted": "",
            "stage": "", "reason": ""}
    lines = (list(csv.DictReader(open(summary), delimiter="\t"))
             if os.path.exists(summary) else [])
    if lines:
        base["elapsed"] = lines[-1].get("elapsed", "")
        base["finding"] = lines[-1].get("finding", "")[:160]
    logs = sorted(glob.glob(os.path.join(root, "logs", "*.log")))
    text = "\n".join(open(path, errors="replace").read() for path in logs)
    targets = sorted(glob.glob(os.path.join(root, "out", "*", "targets", "*", "")))
    if not targets:
        row = dict(base)
        results = glob.glob(os.path.join(root, "out", "*", "schedule", "final",
                                         "result.json"))
        classify(row, results[0] if results else None, lines, root, text)
        rows.append(row)
        continue
    states = {}
    for path in glob.glob(os.path.join(root, "out", "*", "runtime",
                                       "record-summary.json")):
        states.update(json.load(open(path))["targets"])
    for target in targets:
        name = os.path.basename(os.path.dirname(target))
        row = dict(base, case="%s/%s" % (case, name))
        state = states.get(name, {}).get("state", "ACTIVATED")
        if state != "ACTIVATED":
            row.update({"class": "STOPPED", "stage": "SEED", "reason": (
                state + ": " + states[name].get("detail", ""))[:200]})
        else:
            log = os.path.join(target, "campaign.log")
            result = os.path.join(target, "schedule", "final", "result.json")
            classify(row, result if os.path.exists(result) else None, lines,
                     root, text + "\n" + (open(log, errors="replace").read()
                                          if os.path.exists(log) else ""))
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

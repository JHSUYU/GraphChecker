#!/usr/bin/env python3
"""triage.py <round> [gc-out] : one row per case of a sweep (sweep.sh), from
its summary and its final result: the case, the class of its outcome, the
finding and moved roots, the confirmation, how many claims CONFIRM refuted on
the way (result.json refutedClaims), the declared bounds that cut its search
(result.json bounded: their configuration keys, counted BOUNDED on the last
line -- RULES: a bound is a named, rare last resort), the elapsed seconds,
and where a campaign failed, the stage and reason.

Classes:
  CONFIRMED     a SAT witness the program agreed with (confirmation true): a
                candidate bug, to read by hand
  CONFIG_ONLY   a CONFIRMED witness that moves configuration only
                (result.json configurationOnly, COMPOSE's rule): a finding,
                read after the others -- a configuration-validation throw
                fires by design
  REFUTED       the campaign published SAT_UNCONFIRMED, its confirmation
                did not confirm the model (refuted, or decided by no
                replay): a false positive the engine filtered, the
                confirmation's reason as the reason
  UNSAT         the formula is unsatisfiable (UNSAT_CLOSED): no world of the
                corpus reaches the fatal; where the anchor was decided on no
                symbol (result.json concrete[]), that is the reason, and
                where the unsat core names refuted claims the formula
                excludes (result.json restsOnRefutations), how many
  RUN_DEFECT    the run or the engine named a defect that leaves no verdict
                (result.json defects[]): the first defect as the reason, a
                bug to fix
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
        row["bounded"] = ",".join((result.get("bounded") or {}).get("by", []))
        if claim == "SAT_CANDIDATE" and confirmation.get("confirmed") is True:
            row["class"] = ("CONFIG_ONLY"
                            if result.get("configurationOnly") is True
                            else "CONFIRMED")
        elif claim == "SAT_UNCONFIRMED":
            row["class"] = "REFUTED"
            row["reason"] = confirmation.get("reason", "")[:200]
        elif claim == "UNSAT_CLOSED":
            row["class"] = "UNSAT"
            anchors = [c for c in result.get("concrete") or []
                       if c.get("kind") == "ANCHOR"]
            if anchors:
                row["reason"] = ("the anchor was decided on no symbol: %d of "
                                 "%d path(s) decided it, %d read(s) demanded"
                                 % (anchors[0].get("decided", 0),
                                    anchors[0].get("paths", 0),
                                    anchors[0].get("reads", 0)))
            rests = result.get("restsOnRefutations") or []
            if rests:
                row["reason"] = ("rests on %d refuted claim(s) %s; %s" % (
                    len(rests), ",".join(r.get("pathId", "") for r in rests),
                    row["reason"])).rstrip("; ")
        else:
            row["class"] = "RUN_DEFECT"
            defects = result.get("defects") or []
            if defects:
                row["reason"] = re.sub(r"\S*/region/\S*", "<occ>",
                                       defects[0].get("code", "") + " "
                                       + defects[0].get("detail", ""))[:200]
        row["finding"] = (result.get("findingKind", "") + " "
                          + ",".join(r if isinstance(r, str) else r.get("rootId", "")
                                     for r in result.get("movedRoots", []) or []))[:160]
        blockers = result.get("blockers") or []
        if blockers and not row["reason"]:
            row["reason"] = re.sub(r"\S*/region/\S*", "<occ>", blockers[0]["kind"]
                                   + " " + blockers[0]["detail"])[:200]
    elif lines:
        row["class"] = "STOPPED"
        row["stage"], row["reason"] = stated(root, text)
        row["reason"] = row["reason"][:200]
    elif row["class"] == "RUNNING":
        row["stage"], row["reason"] = stated(root, text)


rows = []
for n, case in sorted(cases.items(), key=lambda item: int(item[0])):
    root = os.path.join(out, "accept-%s-%s" % (round_name, n))
    summary = os.path.join(root, "summary.tsv")
    row = {"n": n, "case": case,
           "class": "RUNNING" if os.path.isdir(root) else "PENDING",
           "elapsed": "", "finding": "", "confirmed": "", "refuted": "",
           "bounded": "", "stage": "", "reason": ""}
    lines = (list(csv.DictReader(open(summary), delimiter="\t"))
             if os.path.exists(summary) else [])
    if lines:
        row["elapsed"] = lines[-1].get("elapsed", "")
        row["finding"] = lines[-1].get("finding", "")[:160]
    logs = sorted(glob.glob(os.path.join(root, "logs", "*.log")))
    text = "\n".join(open(path, errors="replace").read() for path in logs)
    results = glob.glob(os.path.join(root, "out", "*", "schedule", "final",
                                     "result.json"))
    classify(row, results[0] if results else None, lines, root, text)
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
print("# " + " ".join("%s=%d" % item for item in sorted(counts.items()))
      + " BOUNDED=%d" % sum(1 for row in rows if row["bounded"]),
      file=sys.stderr)

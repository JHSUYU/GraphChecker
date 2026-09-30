#!/usr/bin/env python3
"""ab_compare.py <ab-out> [case...] -- the comparing half of offline-ab.sh.

For every case and stage, the baseline's and the candidate's stage
directories are compared file by file: every file either side wrote (links
are inputs and skipped; logs and timings are not outputs), with each side's
own output root, jar and declarations checkout replaced by one token each,
so a path is never a difference.  A
stage's `status` counts only by its exit.  A differing file is summarised as
rows added/removed (jsonl), the top-level keys that differ (json), or its
size; the rows of both sides are the same with only their order changed is
said as such, since that is how hash-order nondeterminism shows.  Every
stage is byte-identical across two runs of one jar, on any host, so none is
normalized and every one gates.

The base~acc column compares the BASELINE with the accepted run's own
artifact of the stage ("same" / "drift:n/m" / "tree-moved" / "-"), for
reading only: it says what has moved since the round was accepted, and never
gates.

Prints the table, writes <ab-out>/report.tsv and <ab-out>/diffs/
<case>.<stage>[.accepted].txt.  Exit 0 when every gating stage is
identical, 1 when one differs, 2 when none differs but one could not be
checked (it failed or timed out on the baseline too, or never ran).
"""

import collections
import difflib
import gzip
import hashlib
import json
import os
import sys

CHAINS = {"SEED": ["SEED.static", "SEED.trace", "PLAN", "EXPLORE.0",
                    "SOLVE.0"],
          "IMPORT": ["IMPORT"], "EXPLORE.N": ["EXPLORE.N"],
          "COMPOSE": ["COMPOSE", "CONFIRM"]}
STAGES = [stage for chain in CHAINS.values() for stage in chain]
SIDES = ("baseline", "candidate")
NOT_OUTPUT = {"stdout.log", "stderr.log", "time.txt", "prepare.log"}
# SEED.static's class output is the input scope copied in (classes/) and
# Soot's rewrite of it, not an artifact.
NOT_COMPARED_DIRS = {"SEED.static": {"classes", "instrumented-classes"}}


def read(path):
    with open(path, "rb") as handle:
        data = handle.read()
    return gzip.decompress(data) if path.endswith(".gz") else data


def status_of(stage_dir):
    """The stage's status line as a dict, or None when it never ran."""
    try:
        with open(os.path.join(stage_dir, "status")) as handle:
            line = handle.read().strip()
    except OSError:
        return None
    fields = {}
    for word in line.split(" "):
        key, _, value = word.partition("=")
        fields[key] = value
    if fields.get("exit") == "skipped":
        fields["reason"] = line.split("reason=", 1)[1].rsplit(" host=", 1)[0]
    return fields


def outputs(stage_dir, tokens, stage=""):
    """relative path -> normalized bytes, for every file the stage wrote."""
    found = {}
    skipped = NOT_COMPARED_DIRS.get(stage, set())
    for root, dirs, files in os.walk(stage_dir):
        dirs[:] = sorted(d for d in dirs
                         if not os.path.islink(os.path.join(root, d))
                         and d not in skipped)
        for name in sorted(files):
            path = os.path.join(root, name)
            if os.path.islink(path) or name in NOT_OUTPUT:
                continue
            rel = os.path.relpath(path, stage_dir)
            if name == "status":
                found[rel] = ("exit=" + (status_of(root) or {}).get(
                    "exit", "?")).encode()
                continue
            data = read(path)
            for raw, token in tokens:
                data = data.replace(raw, token)
            found[rel] = data
    return found


def describe(name, before, after):
    """One differing file, in a few words."""
    if name.endswith((".jsonl", ".jsonl.gz")):
        old = collections.Counter(before.splitlines())
        new = collections.Counter(after.splitlines())
        added = sum((new - old).values())
        removed = sum((old - new).values())
        if not added and not removed:
            return name + " same rows, order differs"
        return "%s +%d/-%d rows" % (name, added, removed)
    if name.endswith(".json"):
        try:
            old, new = json.loads(before), json.loads(after)
        except ValueError:
            old = new = None
        if isinstance(old, dict) and isinstance(new, dict):
            keys = sorted(k for k in set(old) | set(new)
                          if old.get(k) != new.get(k))
            if not keys:
                return name + " same content, order differs"
            return "%s keys %s" % (name, ",".join(keys[:6]))
    return "%s %dB->%dB" % (name, len(before), len(after))


def compare(before, after):
    """(differing file descriptions, unified-diff text)."""
    notes, text = [], []
    for name in sorted(set(before) | set(after)):
        if name not in after:
            notes.append(name + " only in baseline")
        elif name not in before:
            notes.append(name + " only in candidate")
        elif before[name] != after[name]:
            notes.append(describe(name, before[name], after[name]))
            lines = list(difflib.unified_diff(
                pretty(before[name]), pretty(after[name]),
                "baseline/" + name, "candidate/" + name, n=1, lineterm=""))
            text.extend(lines[:80] + (["... (%d more)" % (len(lines) - 80)]
                                      if len(lines) > 80 else []))
    return notes, text


def pretty(data):
    text = data.decode("utf-8", "replace")
    try:
        return json.dumps(json.loads(text), indent=1,
                          sort_keys=True).splitlines()
    except ValueError:
        return text.splitlines()


# ---------------------------------------------------------------------------
# What a stage computed, in one line (the summary cell).
# ---------------------------------------------------------------------------

def rows(path):
    try:
        return len(read(path).splitlines())
    except OSError:
        return "-"


def load(path):
    try:
        return json.loads(read(path))
    except (OSError, ValueError):
        return None


def jsonl(path):
    try:
        return [json.loads(line) for line in read(path).splitlines()
                if line.strip()]
    except (OSError, ValueError):
        return []


def sha8(data):
    return hashlib.sha256(data).hexdigest()[:8]


def wave_dir(stage_dir):
    """The wave an EXPLORE stage wrote: the one real obligations-* directory
    among the linked accepted waves of its private iteration."""
    it = os.path.join(stage_dir, "iteration-0000")
    for name in sorted(os.listdir(it)) if os.path.isdir(it) else []:
        path = os.path.join(it, name)
        if name.startswith("obligations-") and not os.path.islink(path):
            return path
    return it


def headline(stage, d, status):
    if status is None:
        return "not run"
    if status.get("exit") == "skipped":
        return "skipped: " + status.get("reason", "")
    j = os.path.join
    if stage == "SEED.static":
        return "graph=%s scope=%s skel=%s" % (
            rows(j(d, "out/candidate_dataflow_edges.jsonl.gz")),
            rows(j(d, "out/static_scope_map.jsonl")),
            rows(j(d, "out/region_skeletons.jsonl.gz")))
    if stage == "SEED.trace":
        return "plan=%s skel=%s rows" % (
            rows(j(d, "concolic_region_plan.jsonl")),
            rows(j(d, "region_skeletons.jsonl")))
    if stage == "PLAN":
        index = load(j(d, "runtime_workflow_schedule_index.json")) or {}
        target = (index.get("target") or {}).get("occurrenceId", "")
        return "tasks=%s target=%s" % (
            rows(j(d, "execution_task_plan.jsonl")),
            sha8(target.encode()) if target else "-")
    if stage in ("EXPLORE.0", "EXPLORE.N"):
        w = wave_dir(d)
        grown = [r for r in jsonl(j(w, "growth.jsonl"))
                 if r.get("kind") == "EXPOSED_REGION"]
        return "%s obl=%s grow=%d gaps=%s tasks=%s" % (
            os.path.basename(w)[-4:], rows(j(w, "obligations.jsonl")),
            len(grown), rows(j(w, "gaps.jsonl")), rows(j(w, "tasks.jsonl")))
    if stage == "SOLVE.0":
        verdicts = collections.Counter()
        for name in sorted(os.listdir(d)):
            if os.path.isdir(j(d, name)):
                result = jsonl(j(d, name, "obligation_result.jsonl"))
                verdicts[result[-1].get("verdict", "?") if result
                         else "exit=" + (status_of(j(d, name)) or {})
                         .get("exit", "?")] += 1
        return "%d obl: %s" % (sum(verdicts.values()), " ".join(
            "%s=%d" % kv for kv in sorted(verdicts.items())))
    if stage == "IMPORT":
        gate = load(j(d, "import_gate.json")) or {}
        return "sessions=%s violations=%s blocking=%s" % (
            gate.get("sessions"), gate.get("violations"),
            gate.get("blocking"))
    if stage == "COMPOSE":
        manifest = load(j(d, "final/candidate_composition_manifest.json"))
        if not manifest:
            return "no manifest"
        claim = manifest.get("solver", {}).get("campaignClaim", {})
        smt2 = j(d, "final/candidate.smt2")
        data = read(smt2) if os.path.exists(smt2) else b""
        moved = ",".join("%s=%s" % kv for kv in
                         sorted(claim.get("movedRoots", {}).items()))
        return "%s %s pol=%s moved={%s} paths=%d val=%d smt2=%dB/%s" % (
            claim.get("claim"), claim.get("findingKind"),
            str(claim.get("polarityDecides")).lower(), moved,
            len(manifest.get("paths", [])),
            len(manifest.get("solver", {}).get("valuations", [])),
            len(data), sha8(data))
    if stage == "CONFIRM":
        if os.path.exists(j(d, "confirm_skipped.txt")):
            return read(j(d, "confirm_skipped.txt")).decode().strip()
        worker = j(d, "final/confirm/worker")
        realized = load(j(worker, "realized.json"))
        if realized:
            return "realized: confirmed=%s" % realized.get("confirmed")
        if status.get("exit") != "0":
            summary = load(j(d, "confirm_summary.json")) or {}
            return "refused: " + summary.get("reason", "exit "
                                              + status.get("exit", "?"))
        return "replay: %s expected edge(s)" % rows(
            j(worker, "expected_edges.jsonl"))
    return ""


def outcome_exit(stage, d, status):
    """Whether a non-zero exit is the stage's answer rather than a failure."""
    if stage == "CONFIRM" and status.get("exit") == "1":
        try:
            return b"CONFIRM refused:" in read(os.path.join(d, "stderr.log"))
        except OSError:
            return False
    return False


# ---------------------------------------------------------------------------
# The baseline against the accepted run (reading only).
# ---------------------------------------------------------------------------

def accepted_pairs(stage, d, acc):
    """(baseline file, accepted file) pairs this stage can be held to."""
    it = os.path.join(acc, "schedule", "iteration-0000")
    pairs = []
    if stage == "SEED.static":
        for name in ("candidate_dataflow_edges.jsonl.gz",
                     "region_skeletons.jsonl.gz", "static_scope_map.jsonl",
                     "scope_frontier.jsonl", "communication_gaps.jsonl.gz"):
            pairs.append((os.path.join(d, "out", name),
                          os.path.join(acc, name)))
    elif stage == "SEED.trace":
        for name in ("concolic_region_plan.jsonl", "region_skeletons.jsonl"):
            pairs.append((os.path.join(d, name),
                          os.path.join(acc, "runtime", name)))
    elif stage == "PLAN":
        name = "runtime_workflow_schedule_index.json"
        pairs.append((os.path.join(d, name), os.path.join(it, name)))
    elif stage in ("EXPLORE.0", "EXPLORE.N"):
        w = wave_dir(d)
        for name in ("obligations.jsonl", "tasks.jsonl", "gaps.jsonl",
                     "graph.jsonl", "growth.jsonl", "explore_manifest.json"):
            pairs.append((os.path.join(w, name),
                          os.path.join(it, os.path.basename(w), name)))
        if stage == "EXPLORE.N":
            # The closing wave rewrites the slot table last: the final one.
            pairs.append((os.path.join(d, "iteration-0000", "slots.jsonl"),
                          os.path.join(it, "slots.jsonl")))
    elif stage == "SOLVE.0":
        for name in sorted(os.listdir(d)):
            if not os.path.isdir(os.path.join(d, name)):
                continue
            for file in ("obligation.jsonl", "obligation_query.smt2",
                         "focused_task.jsonl"):
                pairs.append((os.path.join(d, name, file), os.path.join(
                    it, "obligations-0000", name, file)))
    elif stage == "IMPORT":
        gates = sorted(n for n in os.listdir(it)
                       if n.startswith("obligations-") and os.path.exists(
                           os.path.join(it, n, "import_gate.json")))
        if gates:
            pairs.append((os.path.join(d, "import_gate.json"),
                          os.path.join(it, gates[-1], "import_gate.json")))
    elif stage == "COMPOSE":
        for name in ("candidate.smt2", "candidate_composition_manifest.json",
                     "claim.json"):
            pairs.append((os.path.join(d, "final", name),
                          os.path.join(acc, "schedule", "final", name)))
    elif stage == "CONFIRM":
        worker = os.path.join(d, "final", "confirm", "worker")
        for root, _, files in os.walk(worker):
            for name in files:
                mine = os.path.join(root, name)
                pairs.append((mine, os.path.join(
                    acc, "schedule", "final", "confirm", "worker",
                    os.path.relpath(mine, worker))))
    return pairs


def against_accepted(stage, d, acc, status, case_root):
    """(same / drift:n/m / tree-moved / -, the drifting files)."""
    if status is None or status.get("exit") == "skipped":
        return "-", []
    tokens = []
    for name in STAGES:
        tokens += [(os.path.join(case_root, name, "iteration-0000"), "<IT>"),
                   (os.path.join(case_root, name, "final"), "<FINAL>"),
                   (os.path.join(case_root, name, "obligations-"),
                    "<IT>/obligations-")]
    tokens += [(os.path.join(case_root, "SEED.static", "out"), "<OUT>"),
               (os.path.join(case_root, "SEED.trace"), "<OUT>/runtime"),
               (os.path.join(acc, "schedule", "iteration-0000"), "<IT>"),
               (os.path.join(acc, "schedule", "final"), "<FINAL>"),
               (acc, "<OUT>")]
    tokens = [(a.encode(), b.encode()) for a, b in tokens]
    pairs = [(m, a) for m, a in accepted_pairs(stage, d, acc)
             if os.path.exists(m) or os.path.exists(a)]
    if stage == "SEED.static":
        manifest = load(os.path.join(acc, "schedule", "final",
                                     "run-manifest.json")) or {}
        recorded = (manifest.get("provenance", {})
                    .get("productionClasses", {}).get("sha256", ""))
        try:
            copied = read(os.path.join(d, "classes.sha256")).decode().strip()
        except OSError:
            copied = ""
        if recorded and copied and recorded != copied:
            return "tree-moved", ["the scope copied from the case's tree is "
                                  "not the one the recording was seeded "
                                  "from (productionClasses sha256)"]
    if not pairs:
        return "-", []
    drift = []
    for mine, theirs in pairs:
        try:
            a, b = read(mine), read(theirs)
        except OSError:
            drift.append("%s: missing on one side" % mine)
            continue
        for raw, token in tokens:
            a, b = a.replace(raw, token), b.replace(raw, token)
        if a != b:
            drift.append("%s vs %s: %s" % (mine, theirs, describe(
                os.path.basename(mine), b, a)))
    if not drift:
        return "same", []
    return "drift:%d/%d" % (len(drift), len(pairs)), drift


# ---------------------------------------------------------------------------

def main(argv):
    out = os.path.abspath(argv[1])
    accepted = {}
    with open(os.path.join(out, "accepted.tsv")) as handle:
        for line in handle:
            case, acc = line.rstrip("\n").split("\t")
            accepted[case] = acc
    cases = argv[2:] or list(accepted)
    with open(os.path.join(out, "chains.txt")) as handle:
        chains = handle.read().split()
    stages = [stage for chain in chains for stage in CHAINS[chain]]
    repos = {}
    with open(os.path.join(out, "sides.tsv")) as handle:
        for line in handle:
            side, _, repo = line.rstrip("\n").split("\t")
            repos[side] = repo
    report = []
    worst = 0
    for case in cases:
        roots = {side: os.path.join(out, side, case) for side in SIDES}
        tokens = []
        for side in SIDES:
            tokens.append((os.path.join(out, side).encode(), b"<SIDE>"))
            tokens.append((os.path.join(out, "jars", side + ".jar").encode(),
                           b"<JAR>"))
            tokens.append((repos[side].encode(), b"<REPO>"))
        for stage in stages:
            dirs = {side: os.path.join(roots[side], stage) for side in SIDES}
            status = {side: status_of(dirs[side]) for side in SIDES}
            heads = {side: headline(stage, dirs[side], status[side])
                     for side in SIDES}
            times = "/".join((status[s] or {}).get("wall_s", "-") for s in SIDES)
            base = status["baseline"]
            notes, diff = [], []
            if base is None or status["candidate"] is None:
                result = "ERROR"
                notes = ["never ran on the %s side (see logs/)" % ", ".join(
                    s for s in SIDES if status[s] is None)]
            elif base.get("exit") == "skipped" and status["candidate"].get(
                    "exit") == "skipped" and base.get("reason") == status[
                    "candidate"].get("reason"):
                result = "skipped"
            else:
                notes, diff = compare(
                    outputs(dirs["baseline"], tokens, stage),
                    outputs(dirs["candidate"], tokens, stage))
                if heads["baseline"] != heads["candidate"]:
                    notes.insert(0, "%s -> %s" % (heads["baseline"],
                                                  heads["candidate"]))
                if notes:
                    result = "DIFFERS"
                elif base.get("exit") != "0" and not outcome_exit(
                        stage, dirs["baseline"], base):
                    result = "ERROR"
                    notes = ["both sides exit %s (see %s/stderr.log)" % (
                        base.get("exit"), dirs["baseline"])]
                else:
                    result = "identical"
            summary = "; ".join(notes) if notes else heads["baseline"]
            acc, drift = against_accepted(stage, dirs["baseline"],
                                          accepted[case], base,
                                          roots["baseline"])
            os.makedirs(os.path.join(out, "diffs"), exist_ok=True)
            if result == "DIFFERS":
                with open(os.path.join(out, "diffs", "%s.%s.txt" % (
                        case, stage)), "w") as handle:
                    handle.write("\n".join(notes + [""] + diff) + "\n")
            if drift:
                with open(os.path.join(out, "diffs", "%s.%s.accepted.txt" % (
                        case, stage)), "w") as handle:
                    handle.write("baseline vs the accepted run:\n"
                                 + "\n".join(drift) + "\n")
            # A gating stage skipped on both sides was not checked either.
            worst = max(worst, {"DIFFERS": 2, "ERROR": 1}.get(result, 0),
                        int(result == "skipped"))
            report.append((case, stage, result, acc, times, summary))
    with open(os.path.join(out, "report.tsv"), "w") as handle:
        handle.write("case\tstage\tresult\tbaseline~accepted\twall_s(b/c)"
                     "\tsummary\n")
        for row in report:
            handle.write("\t".join(row) + "\n")
    sides = {}
    with open(os.path.join(out, "sides.tsv")) as handle:
        for line in handle:
            side, jar, repo = line.rstrip("\n").split("\t")
            with open(os.path.join(out, "jars", side + ".jar"), "rb") as j:
                sides[side] = "%s (sha %s, declarations %s)" % (
                    jar, hashlib.sha256(j.read()).hexdigest()[:12], repo)
    print("baseline:  " + sides.get("baseline", "?"))
    print("candidate: " + sides.get("candidate", "?"))
    print("output:    " + out)
    width = 118
    print("%-16s %-11s %-9s %-10s %-11s %s" % (
        "case", "stage", "result", "base~acc", "wall b/c s", "summary"))
    for case, stage, result, acc, times, summary in report:
        print("%-16s %-11s %-9s %-10s %-11s %s" % (
            case, stage, result, acc, times,
            summary if len(summary) <= width else summary[:width - 3] + "..."))
    counts = collections.Counter(row[2] for row in report)
    print("%d stage(s): %s" % (len(report), " ".join(
        "%s=%d" % kv for kv in sorted(counts.items()))))
    return {2: 1, 1: 2}.get(worst, 0)


if __name__ == "__main__":
    sys.exit(main(sys.argv))

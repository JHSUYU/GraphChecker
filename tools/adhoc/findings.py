#!/usr/bin/env python3
"""findings.py <sweep-dir> [--ledger FILE] [--static DIR]

One row per mechanism among a sweep's confirmed witnesses: every
<sweep-dir>/accept-*/out/<case>/schedule/final/result.json whose claim is
SAT_CANDIDATE and whose confirmation is true.  Two witnesses are one
mechanism when they share a signature:

  sig = the first 16 hex digits of
  sha256(the check -- its TARGET_SITE, out/<case>/static_scope_map.jsonl --,
         the finding kind,
         per moved root, sorted: its kind (MARKER, INTEGRAL, CLOCK; a marker
         of a fault door is FAULT), the method of its site, its declared
         callee, the role of its node (the node name without its digits and
         epoch: dn, nn, node), the role and api of its causal context, and
         for a clock how far the model moved it off the recording:
         <=1s, <=1min, <=1h or >1h)

A moved root's site and callee are its plan input action's (portId, or
sourceId for a declared source, = the root; execution_task_plan.jsonl); its
kind, recorded value, node and context are its roots.jsonl row in the
witness's selected session.  Everything read is kept by PRUNE.

Weight, per witness (a signature takes its best):
    (finding kind + mediated) x (1 + native reproduction rate) - extra roots
  finding kind     STATE_/MESSAGE_PAIRING_FLIPPED 5, MARKER_FLIPPED with a
                   fault door root 4, other MARKER_FLIPPED 3,
                   RECORDED_FAILURE_EXPLAINED 3, CLOCK_SKEW 2 when every
                   clock moved at most a minute (else 1: a clock-sync
                   assumption)
  mediated         2 when every moved root the check's static slice holds
                   (--static DIR: slice.sh's $GC_OUT/static/<key>, whose
                   score.json names the check's TARGET_SITE) it reaches only
                   through a field or a wire, else 0
  reproduction     result.json's reproduction (run_engine.sh REPRODUCE): the
                   share of its native runs that took the fatal arm at the
                   claim's anchor; 0 when it ran none
  extra roots      1 per moved root beyond the first

Writes <sweep-dir>/findings.tsv, best weight first, with the best case's native
reproduction (runs at the anchor / runs).  With --ledger, the
ledger (one JSON row per signature: sig, firstSeen, lastSeen, cases, status)
is read and rewritten: a signature it did not hold is new, one it held is
known, and one dismissed.tsv beside it names (sig, reason, JIRA id; by hand)
is dismissed.  What cannot be read of a witness is named on stderr."""
import argparse
import collections
import datetime
import glob
import hashlib
import json
import os
import re
import sys

KIND_WEIGHT = {"STATE_PAIRING_FLIPPED": 5, "MESSAGE_PAIRING_FLIPPED": 5,
               "RECORDED_FAILURE_EXPLAINED": 3}
FAULT_SOURCE = "EXPLICIT_SYMBOLIC_FAULT"
BUCKETS = ((1e9, "<=1s"), (60e9, "<=1min"), (3600e9, "<=1h"))


def lines(path):
    with open(path) as source:
        for line in source:
            if line.strip():
                yield line


def target_site(case_dir):
    for line in lines(os.path.join(case_dir, "static_scope_map.jsonl")):
        if '"TARGET_SITE"' in line:
            return json.loads(line)["siteId"]
    raise ValueError("no TARGET_SITE in %s/static_scope_map.jsonl" % case_dir)


def actions(plan, roots):
    """root id -> the plan object that defines it (an input action's portId
    or a declared source's sourceId)."""
    found = {}

    def walk(value):
        if isinstance(value, dict):
            key = value.get("portId") or value.get("sourceId")
            if key in roots and "siteId" in value:
                found.setdefault(key, value)
            for item in value.values():
                walk(item)
        elif isinstance(value, list):
            for item in value:
                walk(item)

    for line in lines(plan):
        if any(root in line for root in roots):
            walk(json.loads(line))
    return found


def node_role(node):
    """hdfs-17897/dn0#epoch0 -> dn."""
    return re.sub(r"\d+", "", node.rsplit("/", 1)[-1].split("#", 1)[0])


def skew_bucket(row, model):
    nanos = abs(int(model) - int(row["recordedValue"])) * row["clockNanos"]
    return next((name for bound, name in BUCKETS if nanos <= bound), ">1h")


def witness(final):
    """One confirmed witness's signature parts and weight, or None."""
    result = json.load(open(os.path.join(final, "result.json")))
    if result.get("claim") != "SAT_CANDIDATE" \
            or (result.get("confirmation") or {}).get("confirmed") is not True:
        return None
    schedule = os.path.dirname(final)
    case_dir = os.path.dirname(schedule)
    moved = result["movedRoots"]
    session = next(v["selectedSessionId"] for v in result["valuations"]
                   if v["ordinal"] == result["valuationOrdinal"])
    rows = {}
    for path in glob.glob(os.path.join(schedule, "iteration-*", "sessions",
                                       session, "roots.jsonl")):
        for line in lines(path):
            row = json.loads(line)
            for key in (row["rootId"], row.get("symbol")):
                if key in moved:
                    rows[key] = row
    missing = sorted(set(moved) - set(rows))
    if missing:
        raise ValueError("no roots row in session %s for %s" % (session, missing))
    ids = {row["rootId"] for row in rows.values()}
    plans = {}
    for plan in glob.glob(os.path.join(schedule, "iteration-*",
                                       "execution_task_plan.jsonl")):
        plans.update(actions(plan, ids))
    parts, clocks = [], []
    for key, model in moved.items():
        row = rows[key]
        action = plans.get(row["rootId"])
        if action is None:
            raise ValueError("no plan action defines %s" % row["rootId"])
        kind = row["kind"]
        if kind == "MARKER" and action.get("sourceKind") == FAULT_SOURCE:
            kind = "FAULT"
        bucket = ""
        if kind == "CLOCK":
            if "clockNanos" not in row:
                raise ValueError("clock root %s states no clockNanos" % row["rootId"])
            bucket = skew_bucket(row, model)
            clocks.append(bucket)
        context = row["occurrence"].get("context", {})
        parts.append((kind, action["siteId"].rsplit("#", 1)[0],
                      action.get("declaredCallee")
                      or action.get("runtimeDeclaredCallee", ""),
                      node_role(row["occurrence"]["node"]),
                      "%s/%s" % (context.get("role", ""), context.get("api", "")),
                      bucket, action["siteId"]))
    kind = result["findingKind"]
    if kind == "MARKER_FLIPPED":
        weight = 4 if any(part[0] == "FAULT" for part in parts) else 3
    elif kind == "CLOCK_SKEW":
        weight = 2 if all(b in ("<=1s", "<=1min") for b in clocks) else 1
    else:
        weight = KIND_WEIGHT.get(kind, 0)
    reproduction = result.get("reproduction") or {}
    runs = reproduction.get("runs", 0)
    return {"target": target_site(case_dir), "kind": kind, "parts": parts,
            "weight": weight, "extra": len(parts) - 1,
            "native": "%d/%d" % (reproduction.get("atAnchor", 0), runs),
            "rate": reproduction.get("atAnchor", 0) / runs if runs else 0.0}


def signature(found):
    body = [found["target"], found["kind"]] + sorted(
        "|".join(part[:6]) for part in found["parts"])
    return hashlib.sha256("\n".join(body).encode()).hexdigest()[:16]


def describe(part):
    """FAULT Client$Connection.sendRpcRequest @dn CLIENT/heartbeat."""
    kind, method, _, role, context, bucket, _ = part
    owner, _, name = method.strip("<>").partition(": ")
    name = name.split(" ", 1)[-1].split("(", 1)[0]
    return " ".join(filter(None, (kind, "%s.%s" % (owner.rsplit(".", 1)[-1], name),
                                  bucket, "@" + role, context)))


def mediated(found, scores):
    """Whether the check's slice reaches every moved root it holds only
    through a field or a wire, and holds at least one."""
    rows = scores.get(found["target"], [])
    held = [[row for row in rows if row["site"] == part[6]]
            for part in found["parts"]]
    held = [found_rows for found_rows in held if found_rows]
    return bool(held) and all(row["mediated"] for rows_ in held for row in rows_)


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("sweep")
    parser.add_argument("--ledger")
    parser.add_argument("--static")
    args = parser.parse_args()
    scores = {}
    if args.static:
        for path in glob.glob(os.path.join(args.static, "*", "score.json")):
            score = json.load(open(path))
            scores[score["target"]] = score["roots"]
    witnesses = collections.defaultdict(list)
    for final in sorted(glob.glob(os.path.join(
            args.sweep, "accept-*", "out", "*", "schedule", "final"))):
        if not os.path.exists(os.path.join(final, "result.json")):
            continue
        case = os.path.relpath(os.path.dirname(os.path.dirname(final)), args.sweep)
        try:
            found = witness(final)
        except (ValueError, KeyError, OSError) as error:
            print("unreadable witness %s: %s" % (case, error), file=sys.stderr)
            continue
        if found is None:
            continue
        found["case"] = case
        base = found["weight"] + (2 if mediated(found, scores) else 0)
        found["weight"] = round(base * (1 + found["rate"]) - found["extra"], 2)
        witnesses[signature(found)].append(found)
    now = datetime.datetime.now().isoformat(timespec="seconds")
    ledger, dismissed = {}, {}
    if args.ledger:
        if os.path.exists(args.ledger):
            ledger = {row["sig"]: row for row in map(json.loads, lines(args.ledger))}
        path = os.path.join(os.path.dirname(args.ledger), "dismissed.tsv")
        if os.path.exists(path):
            for line in lines(path):
                if not line.startswith("#"):
                    sig, reason = (line.rstrip("\n").split("\t") + [""])[:2]
                    dismissed[sig] = reason
    table = []
    for sig, found in witnesses.items():
        best = max(found, key=lambda f: (f["weight"], f["case"]))
        cases = sorted(f["case"] for f in found)
        status = ("dismissed" if sig in dismissed
                  else "known" if sig in ledger else "new")
        row = ledger.setdefault(sig, {"sig": sig, "firstSeen": now, "cases": []})
        row.update(lastSeen=now, status=status,
                   cases=sorted(set(row["cases"]) | set(cases)))
        roots = " + ".join(describe(part) for part in sorted(best["parts"]))
        table.append((best["weight"], best["native"], sig, status, best["kind"],
                      best["target"], roots, best["case"], len(cases),
                      " ".join(cases)))
    table.sort(key=lambda row: (-row[0], row[2]))
    with open(os.path.join(args.sweep, "findings.tsv"), "w") as out:
        out.write("weight\tnative\tsig\tstatus\tkind\ttarget\tmoved roots"
                  "\tbest case\tcases\tall cases\n")
        for row in table:
            out.write("\t".join(str(v) for v in row) + "\n")
    if args.ledger:
        os.makedirs(os.path.dirname(os.path.abspath(args.ledger)), exist_ok=True)
        with open(args.ledger + ".partial", "w") as out:
            for row in sorted(ledger.values(), key=lambda r: r["firstSeen"]):
                out.write(json.dumps(row, sort_keys=True) + "\n")
        os.replace(args.ledger + ".partial", args.ledger)
    print("%d confirmed witness(es), %d mechanism(s), %d new"
          % (sum(map(len, witnesses.values())), len(witnesses),
             sum(1 for row in table if row[3] == "new")), file=sys.stderr)


if __name__ == "__main__":
    main()

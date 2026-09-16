#!/usr/bin/env python3
"""fatalread.py <case-dir> <work-dir>

Which arms the fatal predicate's own guarded read has, and which one the model
took.  Written for the acceptance report: a verdict says the target was
reached, this says what it read to get there -- the DataNode's reconstructed
map, or an initial snapshot nobody reconstructed.

The join is the one the extractor publishes, and it is made of three
publications, none of which this script derives for itself:

  1. the fatal assertion of candidate.smt2 (`:named fatal_path`, or the
     per-path `:named path_fatal__<ordinal>` the composer spells today) names
     one `merged_boundary__` constant;
  2. a single equality in the same file binds that constant to a guarded
     read's `rf_value__` term;
  3. the composition manifest's `guardedReadModel` holds that read's arms.

Where the model's own choice is published beside them (a reach report carrying
`fatalStateSelection`), the chosen arm is marked; otherwise the arms are
reported unmarked.

**It refuses by name.**  Any of the three missing is reported as
`unresolved: <what was not published>` in fatal_arms.json, and report.py
prints that sentence instead of a fatal-read section.  As this lands, no stage
of the pipeline publishes a `guardedReadModel`, a `merged_boundary__` constant
or a `fatalStateSelection` row (grep over src/main, run_engine.sh and
experiments at the staging tip: zero hits for each), so this is the answer
every case gets until the composer publishes the read's arms again.  A report
that printed "0 arm(s)" there would be stating that the fatal read has no
arms, which is a claim about the failure and not about the artifacts.
"""
import json, os, re, sys

case_dir, work = sys.argv[1], sys.argv[2]
final = os.path.join(case_dir, "schedule", "final")

BOUNDARY = re.compile(r"merged_boundary__[A-Za-z0-9_]+")
FATAL_LABEL = re.compile(r":named (?:fatal_path|path_fatal__[0-9]+)\b")
BINDING = re.compile(
    r"^\(assert \(= (merged_boundary__[A-Za-z0-9_]+) (rf_value__[A-Za-z0-9_]+)\)\)$")


def load(name):
    try:
        with open(os.path.join(final, name)) as handle:
            return json.load(handle)
    except Exception:
        return {}


manifest = load("candidate_composition_manifest.json")
reach = load("z3-result.json")
smt = os.path.join(final, "candidate.smt2")

boundaries, bindings = set(), {}
if os.path.exists(smt):
    with open(smt, errors="replace") as handle:
        for line in handle:
            line = line.strip()
            if FATAL_LABEL.search(line):
                boundaries.update(BOUNDARY.findall(line))
                continue
            match = BINDING.match(line)
            if match:
                bindings[match.group(1)] = match.group(2)

values = {bindings[b] for b in boundaries if b in bindings}
selected = {}
for row in (reach.get("fatalStateSelection", {}) or {}).get("arms", []):
    selected[row.get("selector")] = row

model = (manifest.get("guardedReadModel", {}) or {}).get("reads", [])
arms, carrier = [], "-"
for read in model:
    for arm in read.get("arms", []) or []:
        if arm.get("valueTerm") not in values:
            continue
        carrier = arm.get("sessionLocationKey", carrier)
        owner = arm.get("writerCaseOwner", "")
        chosen = selected.get(arm.get("selector"), {})
        arms.append({
            "selector": arm.get("selector", ""),
            "valueTerm": arm.get("valueTerm", ""),
            "sessionLocationKey": arm.get("sessionLocationKey", ""),
            "locationKey": arm.get("locationKey", ""),
            "declaredField": arm.get("declaredField", ""),
            "writerCaseOwner": owner,
            "initialState": owner.startswith("INITIAL_SOURCE."),
            "selected": bool(chosen.get("selected")),
        })

# Which publication is missing, named as itself.  Order matters: the formula
# is read first, so a manifest that publishes no model is only reported when
# the formula did name a boundary to join it to.
unresolved = ""
if not arms:
    if not os.path.exists(smt):
        unresolved = "there is no %s to read the fatal assertion from" % smt
    elif not boundaries:
        unresolved = ("candidate.smt2 names no merged_boundary__ constant in"
                      " its fatal assertion, so no guarded read is joined to"
                      " the fatal predicate")
    elif not values:
        unresolved = ("candidate.smt2 binds none of its %d fatal boundary"
                      " constant(s) to an rf_value__ term" % len(boundaries))
    elif not model:
        unresolved = ("the composition manifest publishes no guardedReadModel,"
                      " so the arms of the fatal read are not stated")
    else:
        unresolved = ("no arm of the %d published guarded read(s) carries a"
                      " value term the fatal predicate names" % len(model))

report = {
    "fatalSite": manifest.get("fatalSite", "-"),
    "carrier": carrier,
    "resolved": bool(arms),
    "unresolved": unresolved,
    "truncatedCarrier": carrier in {
        gap.get("subject")
        for gap in manifest.get("symbolicPropagationGaps", []) or []
        if gap.get("reason") == "INITIAL_CONTAINER_SNAPSHOT_TRUNCATED"},
    "arms": arms,
}
with open(os.path.join(work, "fatal_arms.json"), "w") as handle:
    json.dump(report, handle, indent=1)
if unresolved:
    print("fatal read: not read -- %s" % unresolved)
else:
    print("fatal read: %d arm(s), carrier %s%s"
          % (len(arms), carrier,
             " (TRUNCATED)" if report["truncatedCarrier"] else ""))

#!/usr/bin/env python3
"""One page per case, from a campaign's own artifacts.

`result.json` answers "what did the run conclude".  An owner asking whether
to believe it needs the things the conclusion rests on, side by side and on
one screen: which roots the recording minted and what each recorded, how many
paths were merged at each anchor and what each one's condition and fatal
predicate say, what z3 answered, which mechanism (if any) the witness named,
every gate and blocking row, how big the formula is, and where the wall clock
went.  This prints exactly that and derives nothing.

Usage: tools/case_onepager.py <lane out dir> [<lane out dir> ...]

A lane out dir is the directory holding one case, e.g.
`$SP/laneAV/out/hdfs-17960`, or a lane's `out/` with several cases under it.
"""
import json
import os
import sys


def read_json(path, default=None):
    try:
        with open(path, encoding="utf-8") as handle:
            return json.load(handle)
    except (OSError, ValueError):
        return default


def cases(root):
    """Every case directory under `root`, or `root` itself when it is one."""
    if os.path.isdir(os.path.join(root, "schedule")):
        return [root]
    found = []
    for name in sorted(os.listdir(root)):
        path = os.path.join(root, name)
        if os.path.isdir(os.path.join(path, "schedule")):
            found.append(path)
    return found


def rule(title):
    print()
    print(title)
    print("-" * max(len(title), 60))


def short(text, width=88):
    text = " ".join(str(text).split())
    return text if len(text) <= width else text[:width - 1] + "…"


def page(case):
    final = os.path.join(case, "schedule", "final")
    manifest = read_json(os.path.join(
        final, "candidate_composition_manifest.json"), {})
    result = read_json(os.path.join(final, "result.json"), {})
    # SOLVE publishes into the manifest it solved: one occurrence, one file.
    reach = manifest.get("solver", {})
    gaps = read_json(os.path.join(final, "gaps.json"), [])

    print("=" * 78)
    print("CASE  " + os.path.basename(case.rstrip("/")))
    print("=" * 78)
    print("claim          %s" % result.get("claim", "<none>"))
    print("reachability   %s" % result.get("reachability", "<none>"))
    print("finalStatus    %s" % result.get(
        "finalStatus", manifest.get("finalStatus", "<none>")))
    print("why            %s" % short(result.get("whyNotAccepted", "")))

    rule("ROOTS  (name | recorded value | solver term)")
    merge = manifest.get("pathMerge", {})
    roots = merge.get("roots", [])
    if not roots:
        print("  none -- the formula asks its question about constants")
    for root in roots:
        print("  %-46s %-12s %s" % (
            short(root.get("fieldSignature")
                  or root.get("portId")
                  or root.get("rawSymbol", ""), 46),
            root.get("recordedValue", "") or "<unstated>",
            root.get("solverTerm", "")))

    rule("PATHS MERGED  anchor %s#%s" % (
        short(merge.get("anchorSiteId", "<none>"), 60),
        merge.get("anchorOccurrence", "?")))
    print("  %-3s %-10s %-5s %-7s %s" % (
        "#", "outcome", "pi", "admitted", "phi"))
    for path in merge.get("paths", []):
        print("  %-3s %-10s %-5s %-7s %s" % (
            path.get("pathOrdinal", "?"),
            "taken" if path.get("observedTakenOutcome") else "not-taken",
            path.get("pathConditionTerms", "?"),
            "yes" if path.get("admitted") else "NO",
            short(path.get("fatalPredicateTerm", ""), 44)))

    rule("SOLVER")
    print("  state          %s" % reach.get("state", "<none>"))
    print("  reachability   %s" % reach.get("reachability", "<none>"))
    claim = reach.get("campaignClaim", {})
    findings = claim.get("witnessFindings") or []
    print("  finding kind   %s" % (findings[0].get("findingKind")
                                   if findings else "<none named>"))
    for valuation in reach.get("valuations", [])[:6]:
        finding = valuation.get("witnessFinding", {})
        if finding.get("narrative"):
            print("  narrative      %s" % short(finding["narrative"], 70))
            break

    rule("GATES AND BLOCKING ROWS")
    refusals = manifest.get("finalStatusRefusals", []) or merge.get("gates", [])
    for refusal in refusals:
        print("  GATE     %-26s %s" % (refusal.get("kind", "?"),
                                       short(refusal.get("detail", ""), 44)))
    for blocker in result.get("blockers", []):
        print("  BLOCKER  %-26s %s" % (blocker.get("code", "?"),
                                       short(blocker.get("subject", ""), 44)))
    rows = gaps if isinstance(gaps, list) else gaps.get("gaps", [])
    counts = {}
    for row in rows or []:
        code = row.get("code") or row.get("reason") or "?"
        counts[code] = counts.get(code, 0) + 1
    for code in sorted(counts, key=lambda name: -counts[name])[:12]:
        print("  gap      %-26s x%d" % (code, counts[code]))
    if not refusals and not result.get("blockers") and not counts:
        print("  none")

    rule("FORMULA")
    smt = os.path.join(final, "candidate.smt2")
    if os.path.exists(smt):
        with open(smt, encoding="utf-8", errors="replace") as handle:
            text = handle.read()
        print("  bytes          %d" % len(text))
        print("  asserts        %d" % text.count("(assert"))
        print("  declarations   %d" % (text.count("(declare-fun")
                                        + text.count("(declare-const")))
    else:
        print("  no composed formula")

    rule("STAGE TIMINGS (ms)")
    metrics = os.path.join(case, "schedule", "stage_metrics.tsv")
    try:
        with open(metrics, encoding="utf-8") as handle:
            for line in handle:
                parts = line.rstrip("\n").split("\t")
                if len(parts) == 2:
                    print("  %-52s %s" % (short(parts[0], 52), parts[1]))
    except OSError:
        print("  no stage metrics")
    print()


def main(argv):
    if not argv:
        print(__doc__)
        return 2
    for root in argv:
        found = cases(root)
        if not found:
            print("no case directory under %s" % root)
            continue
        for case in found:
            page(case)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

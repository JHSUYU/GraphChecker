#!/usr/bin/env python3
"""report.py <case> <case-dir> <work-dir>

Reads one finished case and writes the per-case markdown plus one TSV row.

The markdown is meant to be read, not scanned: it carries the claim and every
blocker, the valuation table with the case frontier each row was solved under,
the mechanism each witness names and how the claim layer read it, which root
the probe perturbed, and -- where fatalread.py could make its join -- the arms
of the fatal read with the one the model chose marked, so the causal chain can
be narrated from the model rather than inferred from a verdict.

A case passes when the claim layer accepted it AND the mechanism it concluded
is the one this case is known to fail by: claim SAT_CANDIDATE, no BLOCKING gap in gaps.json, not withheld,
finalStatus FINAL_READY, a findingKind among the five mechanisms a composition
may conclude, polarityDecides -- the seed disjunct unsat at the recorded
valuation -- the case's EXPECTED mechanism from the table at the top, and an
accepted valuation past the recorded one (ordinal >= 1) with at least one root
moved off the value the recording had -- except for CLOCK_SKEW, where ordinal 0
is legitimate because a clock has a floor and no window, so the witness sits at
the recorded valuation and the clock cells the model moved are its movedRoots.

The last two conditions are why that table exists.  Before them the gate asked
only whether the composer had concluded *something* it could name, so
hdfs-17960 passed with findingKind MESSAGE_PAIRING_FLIPPED at valuation 0, "no
root moved off its recorded value", on a case that has no wire rows at all --
a PASS that said nothing about snapshotDeletionOrdered, the one root the bug
turns on.  A finding at valuation 0 that moves nothing is the recording
restated: it names no difference between the run that failed and a run that
did not, whatever kind it is labelled with.

That last condition used to be re-derived here, by running z3 twice over
candidate.smt2 under each polarity of the declared Boolean roots.  It is not
re-derived any more.  ClaimPolicy computes exactly the same assertion
(polarityDecides = the ordinal-0 outcome is unsat) inside the composer, which
holds the formula, the domains and the arms; and it is already a CONDITION
there, not a note beside the claim -- MARKER_FLIPPED and CLOCK_SKEW are
refused outright without it, and a formula satisfiable at the recorded
valuation raises FORMULA_SAT_AT_RECORDED_VALUATION, which GapKind classes
BLOCKING.  A second implementation of one rule is the disagreement an
acceptance harness is least able to survive, so this reads the composer's
answer instead of forming its own.

RECORDED_FAILURE_EXPLAINED is exempt from the polarity condition because
ClaimPolicy constructs that kind with polarityDecides=false by definition: the
seed run itself observed the fatal arm, so there is no other polarity to
refute.  NO_SUPPORTED_WITNESS fails, naming the claimReason the policy gave.

The probe's plain/buggy/other columns are still printed when probe.tsv exists,
as a reported signal.  Nothing gates on them.
"""
import json, os, re, sys

# ---- the mechanism each case is known to fail by --------------------------
# DATA, declared once, at the top, for the six cases this harness runs.
# probe.sh's acc_root_kind_of splits the same six by the kind of root the
# PROBE has to spell (MARKER / CONFIG / CLOCK); this table names the witness
# kind the COMPOSER must publish for the case to count as explained, and it
# is the only place a case id appears in the gate.  A case this table does
# not name cannot be passed by this harness.
#
# Sources: the verification runbook's polarity row -- "17899x3/11741 marker
# true/false; 17960 ordered=false buggy vs true; 17897 clocks free vs pinned
# to recorded" -- and probe.sh's grep-backed note that
# /opt/hadoop-hdfs-11741 carries no Debug.makeSymbolicBoolean anywhere, so its
# declared roots are the same clock family 17897 declares and its witness is
# spelled CLOCK_SKEW.
#
#   kinds -- the witness kinds this case may conclude with.  The expiry family
#            (11741 and 17899 bug1/2/3) accepts both spellings of ONE
#            mechanism, because the runbook spells it both ways and the
#            difference is which root carries it: a stale BlockKey reaches the
#            consumer either because the refresh RPC's fault marker flipped
#            (MARKER_FLIPPED -- the hadoopIpcRequestFails hook exists in the
#            three 17899 checkouts) or because a clock root moved the key out
#            of allKeys (CLOCK_SKEW).  Both are the expiry mechanism; neither
#            is a pairing kind nor RECORDED_FAILURE_EXPLAINED.
#   root  -- a root that must appear in movedRoots with that value, declared
#            only where its spelling is stable.  17960's configured Boolean
#            is; the clock cases' roots are per-node, per-occurrence
#            Timer.now()/expiryDate terms and the 17899 fault markers are
#            per-case manual__MANUAL_* ids, so those rows declare the kind and
#            the "a root moved" requirement only.
EXPECTED_MECHANISM = {
    "hdfs-17960":      {"kinds": ("MARKER_FLIPPED",),
                        "root": "HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED",
                        "value": "false"},
    "hdfs-11741":      {"kinds": ("CLOCK_SKEW", "MARKER_FLIPPED")},
    "hdfs-17899-bug1": {"kinds": ("MARKER_FLIPPED", "CLOCK_SKEW")},
    "hdfs-17899-bug2": {"kinds": ("MARKER_FLIPPED", "CLOCK_SKEW")},
    "hdfs-17899-bug3": {"kinds": ("MARKER_FLIPPED", "CLOCK_SKEW")},
    # The tree now carries the symbolized RPC failure, as the rest of the
    # family does, so a witness may be the marker OR the clock.
    "hdfs-17897":      {"kinds": ("MARKER_FLIPPED", "CLOCK_SKEW")},
    # HDFS-17967's three paths share one annotated site and are told apart by
    # their target occurrence, so they share this row.  CLOCK_SKEW is the
    # mechanism the workloads are written for: the key the failing party puts
    # on the wire is serials behind the master's, and a witness has to move
    # the clock past its expiry.
    "hdfs-17967-pathA": {"kinds": ("CLOCK_SKEW", "MARKER_FLIPPED")},
    "hdfs-17967-pathB": {"kinds": ("CLOCK_SKEW", "MARKER_FLIPPED")},
    "hdfs-17967-pathC": {"kinds": ("CLOCK_SKEW", "MARKER_FLIPPED")},
}


case_id, case_dir, work = sys.argv[1], sys.argv[2], sys.argv[3]
final = os.path.join(case_dir, "schedule", "final")


def load(name):
    try:
        with open(os.path.join(final, name)) as handle:
            return json.load(handle)
    except Exception:
        return {}


result = load("result.json")


def short(term, keep=26):
    return term if len(term) <= keep else term[:keep] + "…"


def probe_rows():
    rows = {}
    path = os.path.join(work, "probe.tsv")
    if os.path.exists(path):
        for line in open(path):
            parts = line.rstrip("\n").split("\t")
            if len(parts) >= 2:
                rows[parts[0]] = parts[1]
    return rows




def blocker_name(row):
    return row.get("kind") or row.get("code") or "?"


def polarity_doc():
    """What probe.sh asserted, and where each polarity came from."""
    try:
        with open(os.path.join(work, "probe", "polarity.json")) as handle:
            return json.load(handle)
    except Exception:
        return {}


polarity = polarity_doc()

probes = probe_rows()
claim = result.get("claim", "MISSING")
final_status = result.get("finalStatus", "MISSING")
# A blocker row is the gap that refused the claim, published by
# ComposeMain.refusals() as {kind, subject, detail, sessionId} -- "kind", not
# "code": reading the wrong key named every refusal "?" and left the harness
# unable to say why a case failed.
# THE criterion's gap half is gaps.json, the one document every stage's gaps
# land in with the class their producer stated: a PLAN or REPLAY blocker is
# not in result.json's composer blockers, and reading only those printed PASS
# over runs the campaign itself withheld.
gaps_doc = load("gaps.json")
blocking = [g for g in (gaps_doc.get("gaps") or [])
            if g.get("class", "BLOCKING") == "BLOCKING"]
blocking_by_stage = {}
for gap in blocking:
    stage = gap.get("stage", "?")
    blocking_by_stage[stage] = blocking_by_stage.get(stage, 0) + 1
gaps = len(blocking) if gaps_doc else result.get("gapCount", "?")
# ...and the campaign's own acceptance: a candidate the campaign withheld is
# not a pass whatever else the result says.
withheld = result.get("accepted") is not True
# WHICH mechanism the composition concluded, and the condition it rests on.
# EMIT copies both out of the ClaimPolicy decision; "MISSING" here means the
# run predates that, and is reported as itself rather than read as a default.
finding_kind = result.get("findingKind", "MISSING")
polarity_decides = result.get("polarityDecides", False)
valuation_ordinal = result.get("valuationOrdinal", "?")
moved_roots = result.get("movedRoots", {}) or {}
plain = probes.get("plain", "-")
buggy = probes.get("buggy", "-")
other = probes.get("other", "-")

# ---- the witness findings the claim layer published ------------------------
# result.json is the one source: EMIT copies the ClaimPolicy decision into it,
# so there is nothing to fall back to and no second document to reconcile.
findings = result.get("witnessFindings") or []
reported = result.get("reportedFindings") or []


# ---- PASS criterion -------------------------------------------------------
# The claim layer is the whole gate.  Four conditions, all read off
# result.json, none of them re-derived here.
#
# The five mechanisms a composition may conclude.  NO_SUPPORTED_WITNESS is the
# sixth ClaimKind and is deliberately not among them: it is the honest answer
# that nothing in the corpus supports a witness, and a case that reaches it
# has not passed.
ACCEPTED_FINDINGS = {"MARKER_FLIPPED", "CLOCK_SKEW",
                     "MESSAGE_PAIRING_FLIPPED", "STATE_PAIRING_FLIPPED",
                     "RECORDED_FAILURE_EXPLAINED"}

def spell_kinds(kinds):
    return kinds[0] if len(kinds) == 1 else "one of " + "|".join(kinds)


expected = EXPECTED_MECHANISM.get(case_id)
reasons = []
if claim != "SAT_CANDIDATE":
    reasons.append("claim=%s" % claim)
if blocking:
    reasons.append("BLOCKING gaps=%d (%s)" % (len(blocking), ", ".join(
        "%s %d" % (stage, count)
        for stage, count in sorted(blocking_by_stage.items()))))
if withheld:
    reasons.append("candidate withheld (accepted=%s)"
                   % result.get("accepted", "MISSING"))
if final_status != "FINAL_READY":
    reasons.append("finalStatus=%s" % final_status)
if finding_kind == "NO_SUPPORTED_WITNESS":
    reasons.append("findingKind=NO_SUPPORTED_WITNESS (%s)"
                   % result.get("claimReason", "no reason published"))
elif finding_kind not in ACCEPTED_FINDINGS:
    reasons.append("findingKind=%s" % finding_kind)
elif not polarity_decides and finding_kind != "RECORDED_FAILURE_EXPLAINED":
    # The recording does not decide the mechanism, so the mechanism explains
    # nothing about the difference between the run that failed and the run
    # that did not.  RECORDED_FAILURE_EXPLAINED is the one kind for which
    # ClaimPolicy sets this false by construction.
    reasons.append("polarityDecides=false: the formula is satisfiable at the"
                   " recorded valuation, so %s explains nothing"
                   % finding_kind)

# The mechanism is read off the table, never off the run: a case the table
# does not name cannot be passed by this harness.
if expected is None:
    reasons.append("no expected mechanism declared for %s" % case_id)
else:
    if finding_kind not in expected["kinds"]:
        reasons.append("findingKind %s != expected %s"
                       % (finding_kind, spell_kinds(expected["kinds"])))
    # A CLOCK HAS A FLOOR AND NO WINDOW, so there is no perturbed valuation
    # for it to sit at: the witness stands at the recorded valuation and the
    # difference it names is which clock cells the model placed elsewhere,
    # which is exactly movedRoots.  Ordinal 0 is legitimate for CLOCK_SKEW
    # and for nothing else; movedRoots must still be non-empty, because a
    # finding that moves nothing at valuation 0 is the recording restated
    # whatever kind it carries.
    ordinal_ok = (finding_kind == "CLOCK_SKEW"
                  or (isinstance(valuation_ordinal, int)
                      and not isinstance(valuation_ordinal, bool)
                      and valuation_ordinal >= 1))
    if not moved_roots:
        # Valuation 0 is the recording.  A finding that moves nothing there
        # explains nothing, so it does not matter which kind it carries.
        reasons.append("valuation %s moved no root" % valuation_ordinal)
    else:
        if not ordinal_ok:
            reasons.append("valuation %s is the recorded valuation, not a"
                           " perturbed one" % valuation_ordinal)
        want = expected.get("root")
        if want and str(moved_roots.get(want, "")).lower() != expected["value"]:
            reasons.append("expected root %s=%s not moved (moved %s)"
                           % (want, expected["value"],
                              ", ".join("%s=%s" % (r, moved_roots[r])
                                        for r in sorted(moved_roots))))

verdict = "PASS" if not reasons else "FAIL"
reason = "; ".join(reasons) if reasons else "-"

# The finding column: the mechanism the composition concluded, the valuation
# that carried it, and the roots that had to move -- in the composer's own
# words, read off result.json.  It is deliberately not assembled from the
# probe's two polarities any more: the probe reports, the composer decides.
note = "%s at valuation %s" % (finding_kind, valuation_ordinal)
if moved_roots:
    note += " moving %s" % ", ".join(
        "%s=%s" % (root, moved_roots[root]) for root in sorted(moved_roots))
else:
    note += " with no root moved off its recorded value"
note += (" | the recorded valuation refutes the recording"
         if polarity_decides
         else " | the recorded valuation does not refute the recording")
if claim != "SAT_CANDIDATE" and result.get("claimReason"):
    note += " | %s" % result["claimReason"]
# The probe stays a reported signal, never a gate: an older corpus, or a probe
# taught the new names, still shows up here.
if buggy != "-" or other != "-":
    note += " | probe buggy=%s other=%s" % (buggy, other)
# One TSV cell, so one line and a bounded one. The whole narrative, with every
# mechanism row and every freedom, is in the report's "Witness findings".
note = " ".join(note.split())
if len(note) > 180:
    note = note[:177] + "..."

status_path = os.path.join(work, "status")
exit_code, elapsed = "?", "?"
if os.path.exists(status_path):
    text = open(status_path).read()
    exit_code = (re.search(r"exit=(\S+)", text) or [None, "?"])[1]
    elapsed = (re.search(r"elapsed=(\S+)", text) or [None, "?"])[1]
    elapsed = elapsed.rstrip("s")

with open(os.path.join(work, "row.tsv"), "w") as handle:
    handle.write("\t".join([
        case_id, str(exit_code), str(elapsed), claim, final_status,
        ("%d BLOCKING" % len(blocking)) if blocking else "-", str(gaps),
        plain, buggy, other,
        verdict, reason, note]) + "\n")

# ---- the readable report --------------------------------------------------
out = ["# %s" % case_id, "",
       "**%s** -- %s at valuation %s, polarity %s"
       % (verdict, finding_kind, valuation_ordinal,
          "decides" if polarity_decides else "does not decide"),
       "",
       "claim **%s**, finalStatus **%s**, gaps %s, exit %s, %ss"
       % (claim, final_status, gaps, exit_code, elapsed),
       "",
       "%s" % note, ""]
if expected:
    out += ["expected mechanism **%s**%s"
            % (spell_kinds(expected["kinds"]),
               ", moving `%s` to `%s`" % (expected["root"], expected["value"])
               if expected.get("root") else ""),
            "",
            "accepted at valuation %s, %s"
            % (valuation_ordinal,
               "moving " + ", ".join("`%s` = `%s`" % (r, moved_roots[r])
                                     for r in sorted(moved_roots))
               if moved_roots else "moving no root"),
            ""]
else:
    out += ["> no expected mechanism is declared for `%s`, so this harness"
            " cannot pass it" % case_id, ""]
if reason != "-":
    out += ["> %s" % reason, ""]
# The probe is reported, never required: it gates nothing, and on a corpus it
# cannot read it says so rather than contributing a dash to the verdict line.
if (plain, buggy, other) != ("-", "-", "-"):
    out += ["probe: plain `%s` | buggy `%s` | other `%s` (reported, not a"
            " gate)" % (plain, buggy, other), ""]

if polarity.get("otherMode") == "CLOCKS_PINNED":
    out += ["## What each polarity asserted", "",
            "* buggy: nothing asserted — every clock root free, so drift is"
            " allowed",
            "* other: every wall clock pinned to the value it recorded"
            " (%s root(s))" % polarity.get("pinnedClockRoots", "-"),
            ""]
elif polarity.get("terms"):
    names = polarity.get("identities") or polarity.get("terms") or []

    def spell(values):
        if not isinstance(values, list) or len(values) != len(names):
            return "-"
        return ", ".join("`%s` = `%s`" % (short(names[i], 46),
                                          str(values[i]).lower())
                         for i in range(len(names)))

    unstated = polarity.get("unstatedRecordedRootValues") or []

    def buggy_spelling():
        if polarity.get("buggyValues") is not None:
            return spell(polarity.get("buggyValues"))
        if polarity.get("source") == "UNSTATED_RECORDED_VALUE":
            return ("nothing — no recorded value is stated for %d declared"
                    " root(s), so neither polarity of them names anything"
                    " the recording had" % len(unstated))
        return ("each single-marker flip in turn (%s)"
                % ", ".join(polarity.get("flips") or []))

    out += ["## What each polarity asserted", "",
            "* buggy: %s" % buggy_spelling(),
            "    * source **%s**%s" % (
                polarity.get("source", "-"),
                " — `%s`" % polarity["acceptedWitnessKind"]
                if polarity.get("acceptedWitnessKind") else ""),
            "    * %s" % polarity.get("sourceDetail", "-")]
    if polarity.get("acceptedFindingKind"):
        # The mechanism the claim rests on, by name. A witness that names
        # none is not a finding, and the claim layer blocks it; printing the
        # kind here is what lets a reader see which of the four it was.
        out += ["    * finding kind **%s**"
                % polarity["acceptedFindingKind"]]
    if unstated:
        out += ["    * no recorded value observed for: %s"
                % ", ".join(short(name, 70) for name in unstated)]
    if polarity.get("buggyValues") is not None:
        moved = polarity.get("buggyMovesRoots") or []
        if moved:
            moves = ", ".join(short(name, 70) for name in moved)
        elif unstated:
            moves = ("nothing that can be called a move — no recorded value"
                     " is stated for these roots")
        else:
            moves = ("nothing — every declared root sits at the value the"
                     " recording had")
        out += ["    * moves: %s" % moves]
    out += [
            "* other: %s  (**%s**)" % (
                spell(polarity.get("otherValues"))
                if polarity.get("otherValues") is not None
                else "nothing asserted",
                polarity.get("otherMode", "-")),
            ""]

if blocking:
    out += ["## Blocking gaps", ""]
    for row in blocking:
        out.append("* **%s** %s `%s` -- %s" % (row.get("stage", "?"),
                                               row.get("code", "?"),
                                               row.get("subject", ""),
                                               row.get("detail", "")))
    out.append("")

if findings:
    out += ["## Witness findings", "",
            "What the composition concluded, in ClaimPolicy's own words: the"
            " mechanism, the valuation that carried it, the roots that had to"
            " move, and whether the recorded valuation refutes the recording"
            " (without that, the mechanism explains nothing about the"
            " difference between the run that failed and the run that did"
            " not).", ""]
    for row in findings:
        moved = row.get("movedRoots") or {}
        out.append("* **%s** at valuation %s -- %s; polarity %s"
                   % (row.get("findingKind", "?"),
                      row.get("valuationOrdinal", "?"),
                      ", ".join("`%s` = `%s`" % (r, moved[r])
                                for r in sorted(moved))
                      if moved else "no root moved off its recorded value",
                      "**decides**" if row.get("polarityDecides")
                      else "does not decide"))
    out.append("")

if reported:
    # rootSpace.reportedFindings carries FINDING rows, the same shape as
    # witnessFindings -- not gap rows.  Rendered as gaps they came out as
    # "* **?** `` -- " on every case.
    out += ["## Reported findings", "",
            "What the policy read as a finding without letting it carry the"
            " claim.", ""]
    for row in reported:
        moved = row.get("movedRoots") or {}
        out.append("* **%s** at valuation %s -- %s; polarity %s"
                   % (row.get("findingKind", "?"),
                      row.get("valuationOrdinal", "?"),
                      ", ".join("`%s` = `%s`" % (r, moved[r])
                                for r in sorted(moved))
                      if moved else "no root moved off its recorded value",
                      "**decides**" if row.get("polarityDecides")
                      else "does not decide"))
    out.append("")

# The valuations the composer enumerated and what z3 answered for each.
# Read off result.json, which EMIT copies from the composition manifest: the
# separate z3-result.json the old solver stage wrote no longer exists, and
# with it went the fault-marker and mechanism-necessity tables that only that
# document carried.  Nothing reconstructs them here.
valuations = result.get("valuations") or []
if valuations:
    out += ["## Valuations", ""]
    for ordinal, row in enumerate(valuations):
        out.append("* valuation %d `%s`%s"
                   % (row.get("ordinal", ordinal), row.get("status", "?"),
                      (" -- %s" % ", ".join(
                          "`%s` = `%s`" % (k, v) for k, v
                          in sorted((row.get("assignment") or {}).items())))
                      if row.get("assignment") else ""))
    out.append("")

arms_path = os.path.join(work, "fatal_arms.json")
if os.path.exists(arms_path):
    arms = json.load(open(arms_path))
    out += ["## Fatal read", ""]
    # A refusal, by name: fatalread.py states which publication the join it
    # makes is missing rather than reporting zero arms as if the read had none.
    if arms.get("unresolved"):
        out += ["> not read: %s" % arms["unresolved"], ""]
        arms = {"arms": []}
    else:
        out += ["`%s`" % arms.get("fatalSite", "-"), "",
                "carrier `%s`, %d arm(s)"
                % (arms.get("carrier", "-"), len(arms.get("arms", []))), ""]
    if arms.get("arms") and not any(
            arm.get("selected") for arm in arms.get("arms", [])):
        out.append("_(no arm marked: this report carries no"
                   " `fatalStateSelection`, so the model's choice is"
                   " unknown)_")
        out.append("")
    for arm in arms.get("arms", []):
        owner = arm.get("writerCaseOwner", "")
        # A writer owner names region, instance and case; the region is what a
        # reader needs to follow the chain, the rest is identity.
        region = re.sub(r"^region:", "", owner.split("/")[0]) if owner else ""
        out.append("* %s `%s` %s%s"
                   % ("**chosen**" if arm.get("selected") else "  \u00b7     ",
                      short(arm.get("selector", "-"), 30),
                      "INITIAL state" if arm.get("initialState")
                      else "writer",
                      " in `%s`" % short(region, 46) if region else ""))
    if arms.get("truncatedCarrier"):
        out.append("")
        out.append("> carrier `%s` has an INITIAL_CONTAINER_SNAPSHOT_TRUNCATED"
                   " gap: membership over its initial state is a free choice."
                   % arms.get("carrier"))
    out.append("")

with open(os.path.join(work, "report.md"), "w") as handle:
    handle.write("\n".join(out) + "\n")
print("%s: %s (%s)" % (case_id, verdict, reason))

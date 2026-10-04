#!/usr/bin/env python3
"""report.py <case> <case-dir> <work-dir>

Reads one finished case and writes the per-case markdown plus one TSV row.

The markdown is meant to be read, not scanned: it carries the claim and every
blocker, the valuation table with the case frontier each row was solved under,
the mechanism each witness names and how the claim layer read it, which root
and the probe's reading, so the causal chain can be narrated from the model
rather than inferred from a verdict.

A case passes when the claim layer accepted it, the formula carries the
causality the witness names (cone.py: every moved root in the causal cone of
the selected path, no unbound boundary variable), AND the mechanism it
concluded is the one this case is known to fail by: claim SAT_CANDIDATE, confirmed by
the CONFIRM replay (confirmation.confirmed=true), no BLOCKING gap in gaps.json, not withheld,
finalStatus FINAL_READY, a findingKind among the five mechanisms a composition
may conclude, polarityDecides -- the seed disjunct unsat at the recorded
valuation -- the case's EXPECTED mechanism from the table at the top, and an
accepted valuation past the recorded one (ordinal >= 1) with at least one root
moved off the value the recording had -- except for CLOCK_SKEW, where ordinal 0
is legitimate because a clock has a floor and no window, so the witness sits at
the recorded valuation and the clock cells the model moved are its movedRoots.

The last two conditions are why that table exists: without them the gate
asks only whether the composer concluded *something* it could name.  A
finding at valuation 0 that moves nothing is the recording restated: it names
no difference between the run that failed and a run that did not, whatever
kind it is labelled with.

The polarity condition is not re-derived here.  ClaimPolicy computes it
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

The probe's plain/buggy/other columns are printed when probe.tsv exists,
as a reported signal.  Nothing gates on them.
"""
import glob, json, os, re, sys

# ---- the mechanism each case is known to fail by --------------------------
# DATA, declared once, for the cases this harness runs; the only place a case
# id appears in the gate, and a case it does not name cannot pass.
#
#   kinds  -- the witness kinds this case may conclude with.
#   root   -- a root that must appear in movedRoots with that value, declared
#             where its spelling is stable (17960's configured Boolean, its
#             tree hook's source; CONFIG:<key>, causynth.ConfigRoots, once
#             the tree drops the hook).
#   fault  -- the moved roots must include a fault marker flipped to true
#             whose declared site is a door of this transport's client
#             class (the plan's input action states the site of every
#             marker root).
#   clocks -- False: no clock cell may move.  The witness is the fault alone,
#             with every clock where the recording read it.
#
# Every tree of the block-key family carries 11741's expiry check, so a key
# goes stale there ONLY through a failed RPC -- the request that never reached
# the NameNode, or the NameNode's reply to a DataNode or to an application
# that was lost after the NameNode applied it.  A clock witness for them moves
# one node's clock hours past another's inside one JVM, which no run of the
# cluster does: it is not a pass.  11741 is the bug that check fixes, so a
# branch flip reaches its fatal with no fault; 17960's mechanism is its
# configured Boolean.
RPC_FAILURE = {"kinds": ("MARKER_FLIPPED",),
               "fault": "org.apache.hadoop.ipc.Client", "clocks": False}
EXPECTED_MECHANISM = {
    "hdfs-17960":      {"kinds": ("MARKER_FLIPPED",),
                        "root": "HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED",
                        "value": "false"},
    # 11741 has no expiry check: a flipped branch with no fault already
    # reaches its fatal, and an RPC fault may too.
    "hdfs-11741":      {"kinds": ("CLOCK_SKEW", "MARKER_FLIPPED")},
    "hdfs-17899-bug1": RPC_FAILURE,
    "hdfs-17899-bug2": RPC_FAILURE,
    "hdfs-17899-bug3": RPC_FAILURE,
    "hdfs-17897":      RPC_FAILURE,
    "hdfs-17967-pathA": RPC_FAILURE,
    "hdfs-17967-pathB": RPC_FAILURE,
    "hdfs-17967-pathC": RPC_FAILURE,
    # Solr 8.11 fails by a clock.  SOLR-18413: the MIGRATE routing rule has
    # not expired yet (RoutingRule.isExpired, expireAt against
    # currentTimeMillis) when the source leader's update comes after the
    # target collection's deletion, so the update looks the deleted target
    # up.  SOLR-18406: the leader's commit reservation runs out before the
    # follower's filecontent request, so the leader has deleted the
    # generation the follower asks for.
    "solr-18413":      {"kinds": ("CLOCK_SKEW",)},
    "solr-18406":      {"kinds": ("CLOCK_SKEW",)},
    # ZooKeeper 3.9.  zk-bugs-quota-init: createQuota's limit node is
    # written and its client sees the request fail (a ZooKeeper write door's
    # fault), so the stat node is never created and the retried call's
    # update branch reads it; the witness is the fault alone.
    # zk-bugs-election-offer: the server's lookup of an offer the election
    # listed is paired with a competitor's delete of it.
    "zk-bugs-quota-init": {"kinds": ("MARKER_FLIPPED",),
                           "fault": "org.apache.zookeeper.ZooKeeper",
                           "clocks": False},
    "zk-bugs-election-offer": {"kinds": ("STATE_PAIRING_FLIPPED",)},
    # HDFS bug study #15: a detector turn that reads the slow-disk bound
    # before the reconfiguration to 0 lands (its INITIAL, 1) publishes the
    # SSD, which no later turn clears, so the ALL_SSD write has no volume.
    "hdfs-bugs-slowdisk-zero": {"kinds": ("STATE_PAIRING_FLIPPED",)},
    # HDFS bug study HDFS-2 #09: the re-encryption throttle's stopwatch
    # readings (nn0's clock) make its sleep negative, the handler dies, and
    # the zone's next START is refused as already submitted.
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


def root_kinds():
    """rootId -> kind, as the composition manifest publishes its roots."""
    manifest = load("candidate_composition_manifest.json")
    return {row.get("rootId", ""): row.get("kind", "")
            for row in (manifest.get("roots") or [])}


CELL = re.compile(r"^M_[A-Z]_field_(.+?)\.occ\.")


def root_of(moved, kinds):
    """The rootId a movedRoots key names: itself, or the root of a cell."""
    if moved in kinds:
        return moved
    found = CELL.match(moved)
    return found.group(1) if found else moved


def declared_sites():
    """rootId -> the declared site of that input, off the iteration's plan."""
    sites = {}
    for plan in sorted(glob.glob(os.path.join(
            case_dir, "schedule", "iteration-*",
            "execution_task_plan.jsonl"))):
        with open(plan) as handle:
            for line in handle:
                if "EXPLICIT_SYMBOLIC_FAULT" not in line:
                    continue
                row = json.loads(line)
                for action in row.get("inputActions") or []:
                    if action.get("sourceKind") != "EXPLICIT_SYMBOLIC_FAULT":
                        continue
                    port = action.get("portId") or action.get("symbol") or ""
                    if port:
                        sites[port] = action.get("siteId", "")
    return sites




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
# THE criterion's gap half is gaps.json, the one document every stage's gaps
# land in with the class their producer stated: a PLAN or REPLAY blocker is
# not in result.json's composer blockers.
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
# CONFIRM (PIPELINE §10): SAT says the model satisfies the formula, the
# confirmation replay says whether the program agrees.  EMIT copies
# confirm.json into result.json and downgrades an unconfirmed claim to
# SAT_UNCONFIRMED; a result with no confirmation at all is not confirmed.
confirmation = result.get("confirmation") or {}
confirmed = confirmation.get("confirmed") is True
# WHICH mechanism the composition concluded, and the condition it rests on.
# EMIT copies both out of the ClaimPolicy decision; "MISSING" here means the
# run predates that, and is reported as itself rather than read as a default.
finding_kind = result.get("findingKind", "MISSING")
polarity_decides = result.get("polarityDecides", False)
valuation_ordinal = result.get("valuationOrdinal", "?")
moved_roots = result.get("movedRoots", {}) or {}
# The arms the claimed valuation took that are no pairing the selected
# path's own run had, as COMPOSE states them (Composition#repaired): what a
# pairing kind moved.
repaired_arms = next((row.get("repairedArms") or []
                      for row in result.get("valuations") or []
                      if row.get("ordinal") == valuation_ordinal), [])
plain = probes.get("plain", "-")
buggy = probes.get("buggy", "-")
other = probes.get("other", "-")

# ---- the witness findings the claim layer published ------------------------
# result.json is the one source: EMIT copies the ClaimPolicy decision into it,
# so there is nothing to fall back to and no second document to reconcile.
findings = result.get("witnessFindings") or []


# ---- PASS criterion -------------------------------------------------------
# The claim layer is the whole gate: the conditions below, all read off
# result.json (and the cone gate's cone.json), none of them re-derived here.
#
# The five mechanisms a composition may conclude.  NO_SUPPORTED_WITNESS is the
# sixth ClaimKind and is deliberately not among them: it is the honest answer
# that nothing in the corpus supports a witness, and a case that reaches it
# has not passed.
ACCEPTED_FINDINGS = {"MARKER_FLIPPED", "CLOCK_SKEW",
                     "MESSAGE_PAIRING_FLIPPED", "STATE_PAIRING_FLIPPED",
                     "RECORDED_FAILURE_EXPLAINED"}
# What a pairing kind moves is a pairing, not a root: ClaimPolicy names it
# only where pinning the path's observed reads (or arrivals) refutes the
# witness, and the claimed valuation names the arms it re-paired
# (repairedArms), which CONFIRM held the run to.
PAIRING_FINDINGS = {"MESSAGE_PAIRING_FLIPPED", "STATE_PAIRING_FLIPPED"}

def spell_kinds(kinds):
    return kinds[0] if len(kinds) == 1 else "one of " + "|".join(kinds)


expected = EXPECTED_MECHANISM.get(case_id)
reasons = []
# A recording whose trace passed its bound was ended by its watcher, which
# left its marker beside the trace (run_engine.sh campaign_watch_workload):
# the verdict names it, before the claim it never reached.
bound_marker = os.path.join(case_dir, "runtime", "RECORDING_BOUND")
if os.path.isfile(bound_marker):
    with open(bound_marker) as marker:
        reasons.append(marker.read().strip())
if claim != "SAT_CANDIDATE":
    reasons.append("claim=%s" % claim)
if blocking:
    reasons.append("BLOCKING gaps=%d (%s)" % (len(blocking), ", ".join(
        "%s %d" % (stage, count)
        for stage, count in sorted(blocking_by_stage.items()))))
if withheld:
    reasons.append("candidate withheld (accepted=%s)"
                   % result.get("accepted", "MISSING"))
if not confirmed:
    reasons.append("unconfirmed: %s" % (
        confirmation.get("reason") or "no confirmation published"))
# The claims CONFIRM refuted before this one: filtered false positives,
# reported whatever the case concluded (## Refuted claims).
refuted = result.get("refutedClaims") or []
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
    # and a pairing kind (PAIRING_FINDINGS: it moves a pairing, the arm the
    # valuation selected) and for nothing else; any other kind's movedRoots
    # must still be non-empty, because a finding that moves nothing at
    # valuation 0 is the recording restated whatever kind it carries.
    pairing = finding_kind in PAIRING_FINDINGS
    ordinal_ok = (finding_kind == "CLOCK_SKEW" or pairing
                  or (isinstance(valuation_ordinal, int)
                      and not isinstance(valuation_ordinal, bool)
                      and valuation_ordinal >= 1))
    if pairing and not moved_roots:
        # The pairing alone moved: the valuation must name what it re-paired.
        if not repaired_arms:
            reasons.append("valuation %s names no re-paired arm"
                           % valuation_ordinal)
    elif not moved_roots:
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
        if expected.get("fault") or expected.get("clocks") is False:
            kinds = root_kinds()
            sites = declared_sites()
            moved_kinds = {moved: kinds.get(root_of(moved, kinds), "")
                           for moved in moved_roots}
            faults = [moved for moved, kind in moved_kinds.items()
                      if kind == "MARKER"
                      and str(moved_roots[moved]).lower() == "true"
                      and expected.get("fault", "") in sites.get(
                          root_of(moved, kinds), "")]
            clocks = [moved for moved, kind in moved_kinds.items()
                      if kind == "CLOCK"]
            if expected.get("fault") and not faults:
                reasons.append("no %s door fault flipped to true in the"
                               " witness (moved %s)"
                               % (expected["fault"], ", ".join(
                                   "%s[%s]=%s" % (r, moved_kinds[r] or "?",
                                                  moved_roots[r])
                                   for r in sorted(moved_roots))))
            if expected.get("clocks") is False and clocks:
                reasons.append("the witness moves %d clock cell(s); an RPC"
                               " failure has to reach the fatal with every"
                               " clock where the recording read it"
                               % len(clocks))

# THE CAUSALITY the witness rests on, checked in the formula itself
# (cone.py): every root it moved must be in the causal cone of the path the
# claim selected, and no fatal condition may name a boundary variable that no
# family binds.  A claim whose mechanism the fatal does not depend on, or
# whose fatal rests on a value no producer made, is not a finding.
try:
    with open(os.path.join(work, "cone.json")) as handle:
        cone = json.load(handle)
except Exception:
    cone = None
if cone is None:
    reasons.append("no causal cone published (cone.py)")
else:
    outside = sorted(r for r, inside in cone.get("moved", {}).items()
                     if not inside)
    if outside:
        reasons.append("moved root(s) outside the witness path's causal"
                       " cone: %s" % ", ".join(outside))
    if cone.get("unbound"):
        reasons.append("%d boundary variable(s) in a fatal condition that no"
                       " family binds" % len(cone["unbound"]))

verdict = "PASS" if not reasons else "FAIL"
reason = "; ".join(reasons) if reasons else "-"

# The finding column: the mechanism the composition concluded, the valuation
# that carried it, and the roots that had to move -- in the composer's own
# words, read off result.json.  It is deliberately not assembled from the
# probe's two polarities: the probe reports, the composer decides.
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
# The probe stays a reported signal, never a gate.
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

if polarity.get("terms"):
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
            "    * source **%s**" % polarity.get("source", "-"),
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
    if repaired_arms:
        out.append("* re-paired arms of valuation %s: %s"
                   % (valuation_ordinal, ", ".join(
                       "`%s`" % arm for arm in repaired_arms)))
    out.append("")

if cone:
    out += ["## Causal cone", "",
            "What the fatal condition of the selected path (`%s`) depends on"
            " in the published formula, closed over the message families"
            " bound under it (cone.py)." % (cone.get("selector") or "-"), ""]
    for root, inside in sorted(cone.get("moved", {}).items()):
        out.append("* moved `%s`: %s" % (root, "in the cone" if inside
                                         else "**not in the cone**"))
    out.append("* %d declared root(s) in the cone; %d unbound boundary"
               " variable(s)" % (len(cone.get("coneRoots") or []),
                                 len(cone.get("unbound") or [])))
    out.append("")


if refuted:
    out += ["## Refuted claims", "",
            "Models CONFIRM ran and disagreed with, each excluded from every"
            " composition after it (result.json refutedClaims).", ""]
    for row in refuted:
        model = row.get("model") or {}
        out.append("* **%s** on path `%s`, moving %s -- %s"
                   % (model.get("findingKind", "?"), model.get("pathId", "?"),
                      ", ".join("`%s` = `%s`" % (r, v) for r, v
                                in sorted((model.get("moved") or {}).items()))
                      or "nothing", row.get("reason", "")))
    out.append("")

# The valuations the composer enumerated and what z3 answered for each.
# Read off result.json, which EMIT copies from the composition manifest.
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

with open(os.path.join(work, "report.md"), "w") as handle:
    handle.write("\n".join(out) + "\n")
print("%s: %s (%s)" % (case_id, verdict, reason))

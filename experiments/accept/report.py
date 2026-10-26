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
the selected path; no unbound boundary variable, unless CONFIRM confirmed the
SAT, which then names them, WITNESS_CHAIN_OPEN), AND the mechanism it
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

NO_SUPPORTED_WITNESS fails, naming the claimReason the policy gave.

The probe's plain/buggy/other columns are printed when probe.tsv exists,
as a reported signal.  Nothing gates on them.
"""
import glob, json, os, re, sys

RPC_FAILURE = {"kinds": ("MARKER_FLIPPED",),
               "fault": ("org.apache.hadoop.ipc.Client",), "clocks": False}
SOLR_TRANSPORT_FAULT = {
    "kinds": ("MARKER_FLIPPED",),
    "fault": ("org.apache.solr.client.solrj.impl.HttpSolrClient",
              "org.apache.solr.client.solrj.impl.Http2SolrClient",
              "org.apache.solr.common.cloud.SolrZkClient",
              "org.apache.zookeeper.ZooKeeper"),
    "clocks": False}
EXPECTED_MECHANISM = {
    "hdfs-17960":      {"kinds": ("MARKER_FLIPPED",),
                        "root": "HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED",
                        "value": "false"},
    "hdfs-11741":      {"kinds": ("CLOCK_SKEW", "MARKER_FLIPPED")},
    "hdfs-17899-bug1": RPC_FAILURE,
    "hdfs-17899-bug2": RPC_FAILURE,
    "hdfs-17899-bug3": RPC_FAILURE,
    "hdfs-17897":      RPC_FAILURE,
    "hdfs-17967-pathA": RPC_FAILURE,
    "hdfs-17967-pathB": RPC_FAILURE,
    "hdfs-17967-pathC": RPC_FAILURE,
    "solr-18413":      {"kinds": ("CLOCK_SKEW",)},
    "solr-18406":      {"kinds": ("CLOCK_SKEW",)},
    "solr-bugs-reindex-cleanup": SOLR_TRANSPORT_FAULT,
    "solr-bugs-migrate-buffer-leak": SOLR_TRANSPORT_FAULT,
    "solr-bugs-overseer-lock-leak": {
        "kinds": ("MARKER_FLIPPED",),
        "fault": ("org.apache.solr.common.cloud.SolrZkClient",
                  "org.apache.zookeeper.ZooKeeper"),
        "clocks": False},
    "solr-bugs-restore-construction": SOLR_TRANSPORT_FAULT,
    "solr-bugs-snapshot-no-active": {"kinds": ("STATE_PAIRING_FLIPPED",)},
    "solr-bugs-tra-start-overwrite": {"kinds": ("STATE_PAIRING_FLIPPED",)},
    "zk-bugs-quota-init": {"kinds": ("MARKER_FLIPPED",),
                           "fault": ("org.apache.zookeeper.ZooKeeper",),
                           "clocks": False},
    "zk-bugs-election-offer": {"kinds": ("STATE_PAIRING_FLIPPED",)},
    "hdfs-bugs-slowdisk-zero": {"kinds": ("STATE_PAIRING_FLIPPED",)},
    "hbase-bugs-backup-lock-reply-lost": {
        "kinds": ("MARKER_FLIPPED",),
        "fault": ("org.apache.hadoop.hbase.ipc.RpcConnection",),
        "clocks": False},
    "hbase-adhoc-04": {
        "kinds": ("MARKER_FLIPPED",),
        "fault": ("org.apache.hadoop.hbase.ipc.AbstractRpcClient",),
        "clocks": False},
    "hbase-adhoc-22": {
        "kinds": ("STATE_PAIRING_FLIPPED",),
        "clocks": False},
    "hbase-bugs-ns-rsgroup-removal": {
        "kinds": ("MARKER_FLIPPED",),
        "fault": ("org.apache.hadoop.hbase.ipc.AbstractRpcClient",),
        "clocks": False},
    "hbase-bugs-master-active-time": {
        "kinds": ("MARKER_FLIPPED",),
        "clocks": False},
    "hbase-adhoc-34": {
        "kinds": ("MARKER_FLIPPED",),
        "fault": ("org.apache.hadoop.hbase.zookeeper.RecoverableZooKeeper",),
        "clocks": False},
    "hbase-buggy-20642": {
        "kinds": ("MARKER_FLIPPED",),
        "fault": ("org.apache.hadoop.hbase.ipc.RpcConnection",),
        "clocks": False},
    "hbase-buggy-15039": {
        "kinds": ("STATE_PAIRING_FLIPPED", "MARKER_FLIPPED"),
        "clocks": False},
}
for _case, _rule in EXPECTED_MECHANISM.items():
    if not isinstance(_rule.get("fault", ()), tuple):
        raise SystemExit("report.py: %s's fault rule must be a tuple of class"
                         " names, not %r" % (_case, _rule["fault"]))


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
gaps_doc = load("gaps.json")
blocking = [g for g in (gaps_doc.get("gaps") or [])
            if g.get("class", "BLOCKING") == "BLOCKING"]
blocking_by_stage = {}
for gap in blocking:
    stage = gap.get("stage", "?")
    blocking_by_stage[stage] = blocking_by_stage.get(stage, 0) + 1
gaps = len(blocking) if gaps_doc else result.get("gapCount", "?")
withheld = result.get("accepted") is not True
confirmation = result.get("confirmation") or {}
confirmed = confirmation.get("confirmed") is True
finding_kind = result.get("findingKind", "MISSING")
polarity_decides = result.get("polarityDecides", False)
valuation_ordinal = result.get("valuationOrdinal", "?")
moved_roots = result.get("movedRoots", {}) or {}
repaired_arms = next((row.get("repairedArms") or []
                      for row in result.get("valuations") or []
                      if row.get("ordinal") == valuation_ordinal), [])
plain = probes.get("plain", "-")
buggy = probes.get("buggy", "-")
other = probes.get("other", "-")

findings = result.get("witnessFindings") or []


ACCEPTED_FINDINGS = {"MARKER_FLIPPED", "CLOCK_SKEW",
                     "MESSAGE_PAIRING_FLIPPED", "STATE_PAIRING_FLIPPED"}
PAIRING_FINDINGS = {"MESSAGE_PAIRING_FLIPPED", "STATE_PAIRING_FLIPPED"}

def spell_kinds(kinds):
    return kinds[0] if len(kinds) == 1 else "one of " + "|".join(kinds)


expected = EXPECTED_MECHANISM.get(case_id)
reasons = []
end_marker = os.path.join(case_dir, "runtime", "RECORDING_ENDED")
if os.path.isfile(end_marker):
    with open(end_marker) as marker:
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
refuted = result.get("refutedClaims") or []
if final_status != "FINAL_READY":
    reasons.append("finalStatus=%s" % final_status)
if finding_kind == "NO_SUPPORTED_WITNESS":
    reasons.append("findingKind=NO_SUPPORTED_WITNESS (%s)"
                   % result.get("claimReason", "no reason published"))
elif finding_kind not in ACCEPTED_FINDINGS:
    reasons.append("findingKind=%s" % finding_kind)
elif not polarity_decides:
    reasons.append("polarityDecides=false: the formula is satisfiable at the"
                   " recorded valuation, so %s explains nothing"
                   % finding_kind)

if expected is None:
    reasons.append("no expected mechanism declared for %s" % case_id)
else:
    if finding_kind not in expected["kinds"]:
        reasons.append("findingKind %s != expected %s"
                       % (finding_kind, spell_kinds(expected["kinds"])))
    pairing = finding_kind in PAIRING_FINDINGS
    ordinal_ok = (finding_kind == "CLOCK_SKEW" or pairing
                  or (isinstance(valuation_ordinal, int)
                      and not isinstance(valuation_ordinal, bool)
                      and valuation_ordinal >= 1))
    if pairing and not moved_roots:
        if not repaired_arms:
            reasons.append("valuation %s names no re-paired arm"
                           % valuation_ordinal)
    elif not moved_roots:
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
                      and any(door in sites.get(root_of(moved, kinds), "")
                              for door in expected.get("fault", ()))]
            clocks = [moved for moved, kind in moved_kinds.items()
                      if kind == "CLOCK"]
            if expected.get("fault") and not faults:
                reasons.append("no %s door fault flipped to true in the"
                               " witness (moved %s)"
                               % (" or ".join(expected["fault"]), ", ".join(
                                   "%s[%s]=%s" % (r, moved_kinds[r] or "?",
                                                  moved_roots[r])
                                   for r in sorted(moved_roots))))
            if expected.get("clocks") is False and clocks:
                reasons.append("the witness moves %d clock cell(s); an RPC"
                               " failure has to reach the fatal with every"
                               " clock where the recording read it"
                               % len(clocks))

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
    if cone.get("unbound") and not confirmed:
        reasons.append("%d boundary variable(s) in a fatal condition that no"
                       " family binds" % len(cone["unbound"]))

verdict = "PASS" if not reasons else "FAIL"
reason = "; ".join(reasons) if reasons else "-"

note = "%s at valuation %s" % (finding_kind, valuation_ordinal)
if moved_roots:
    note += " moving %s" % ", ".join(
        "%s=%s" % (root, moved_roots[root]) for root in sorted(moved_roots))
else:
    note += " with no root moved off its recorded value"
if cone and cone.get("unbound") and confirmed:
    note += " (WITNESS_CHAIN_OPEN: %d boundary variable(s) no family binds)" \
        % len(cone["unbound"])
note += (" | the recorded valuation refutes the recording"
         if polarity_decides
         else " | the recorded valuation does not refute the recording")
bounded = result.get("bounded") or {}
if bounded:
    note += " | BOUNDED by %s" % ",".join(bounded.get("by", []))
if claim != "SAT_CANDIDATE" and result.get("claimReason"):
    note += " | %s" % result["claimReason"]
if buggy != "-" or other != "-":
    note += " | probe buggy=%s other=%s" % (buggy, other)
note = " ".join(note.split())
if len(note) > 180:
    note = note[:177] + "..."
reproduction = load("reproduce.json")
if reproduction.get("runs"):
    note += " | reproduced %s/%s natively" % (reproduction.get("reproduced", 0),
                                              reproduction.get("runs"))
fallback = load("fallback.json")
if fallback:
    note += " | FALLBACK %s" % ("stood: no later claim reproduced"
                                if fallback.get("stood")
                                else "kept aside: a later claim reproduced")

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
    out += ["## Defects", "",
            "Defects of the run or the engine, each a bug to fix: with one, an"
            " UNSAT formula is no verdict (RUN_DEFECT).", ""]
    for row in blocking:
        out.append("* **%s** %s `%s` -- %s" % (row.get("stage", "?"),
                                               row.get("code", "?"),
                                               row.get("subject", ""),
                                               row.get("detail", "")))
    out.append("")

concrete = result.get("concrete") or []
CONCRETE_SHOWN = 20
WORDS = {"FREE": "free (over-approximated)",
         "HELD": "held at its recorded value",
         "CONSTANT": "a constant of its version (its producer refused by rule)",
         "EXPORTED": "bound by its producer's export (its producer refused by rule)",
         "BOUNDED": "held past the daemon tick bound"}
witness = next((row for row in result.get("valuations") or []
                if row.get("ordinal") == valuation_ordinal), {})
witness_path = witness.get("selectedPathId") or ""
chosen = {arm.get("selector") for arm in witness.get("selectedArms") or []}
on_witness = [r for r in concrete
              if witness_path and r.get("pathId") == witness_path
              and (not r.get("arm") or r.get("arm") in chosen)]
pathless = [r for r in concrete if not r.get("pathId")]
others = [r for r in concrete if r.get("pathId")
          and r.get("pathId") != witness_path and not r.get("arm")]
unchosen = len(concrete) - len(on_witness) - len(pathless) - len(others)
if concrete:
    out += ["## Concrete", "",
            "What the decision rested on (result.json concrete[], %d row(s)):"
            " a FREE value is free (over-approximated), a HELD one held at"
            " its recorded value because no row states its producer;"
            " information, never a gap.%s" % (len(concrete),
            " The witness path's %d row(s) first." % len(on_witness)
            if on_witness else ""), ""]
    shown = on_witness + pathless + others[:CONCRETE_SHOWN]
    for row in shown:
        if row.get("kind") == "ANCHOR":
            out.append("* anchor `%s` decided on no symbol: %d of %d path(s)"
                       " decided it, %d read(s) of %s demanded, %d off the"
                       " cone" % (row.get("anchor", "?"),
                                  row.get("decided", 0), row.get("paths", 0),
                                  row.get("reads", 0),
                                  ", ".join(row.get("locations") or [])
                                  or "no location", row.get("offCone", 0)))
        else:
            out.append("* %s `%s`%s%s%s%s%s" % (
                WORDS.get(row.get("kind"), row.get("kind", "?")),
                row.get("subject", ""),
                " = `%s`" % row["value"] if row.get("value") else "",
                (" (moves with %s)" % ", ".join(row["movesWith"]))
                if row.get("movesWith") else "",
                " -- %s" % row["reason"] if row.get("reason") else "",
                " [arm %s]" % row["arm"] if row.get("arm") else "",
                "" if row.get("pathId") in ("", None, witness_path)
                else " [path %s]" % row["pathId"]))
    if len(others) > CONCRETE_SHOWN:
        out.append("* ... and %d more" % (len(others) - CONCRETE_SHOWN))
    if unchosen:
        out.append("* %d row(s) inside arms no witness chose, not shown"
                   % unchosen)
    out.append("")

if bounded:
    out += ["## Bounded", "",
            "Declared bounds cut this search (result.json bounded): the"
            " verdict is over what they left, and a bound is a named, rare"
            " last resort -- a closure that needs one is a defect to read.",
            "", "* %s -- %s" % (", ".join("`%s`" % key for key
                                          in bounded.get("by", [])),
                               bounded.get("detail", "")), ""]

rests = result.get("restsOnRefutations") or []
if rests:
    out += ["## Rests on excluded models", "",
            "The unsat core names models the formula excludes: refuted"
            " claims (refuted_claim__, false positives whose CONFIRM replay"
            " did not reach the fatal at the anchor), on which the UNSAT rests"
            " beside the corpus (result.json restsOnRefutations).", ""]
    for row in rests:
        out.append("* `%s` on path `%s`, moving %s -- %s" % (
            row.get("name", "?"), row.get("pathId", "?"),
            ", ".join("`%s` = `%s`" % (r, v) for r, v
                      in sorted((row.get("moved") or {}).items()))
            or "nothing", row.get("reason", "")))
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
    off = cone.get("unboundOffWitness") or []
    if off:
        out.append("* %d unbound boundary variable(s) on paths the witness"
                   " does not take (information): %s"
                   % (len(off), ", ".join("`%s`" % v for v in sorted(set(off)))))
    out.append("")


if fallback:
    out += ["## Fallback", "",
            "A confirmed claim that reproduced in 0 native runs is kept as the"
            " fallback verdict and excluded, and the claim loop composes on"
            " (fallback.json): %s -- %s" % (fallback.get("fallback", "?"),
                                          fallback.get("reason", "")), ""]

if refuted:
    out += ["## Refuted claims", "",
            "Models CONFIRM did not confirm (refuted, or undecided: no replay"
            " decided them), each excluded from every composition after it"
            " (result.json refutedClaims).", ""]
    for row in refuted:
        model = row.get("model") or {}
        out.append("* **%s** on path `%s`, moving %s -- %s"
                   % (model.get("findingKind", "?"), model.get("pathId", "?"),
                      ", ".join("`%s` = `%s`" % (r, v) for r, v
                                in sorted((model.get("moved") or {}).items()))
                      or "nothing", row.get("reason", "")))
    out.append("")

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

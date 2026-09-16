#!/usr/bin/env bash
# probe.sh <case> <case-dir> <work-dir>
#
# The PLAIN probe: z3 on the composition's own candidate.smt2, unpinned and with
# no case frontier fixed, so the verdict is a statement about the formula the
# campaign published rather than about a slice of it.
#
# Three runs per case: plain, the buggy polarity of the case's declared root,
# and the other polarity. What the probe is asked for is the buggy polarity:
# satisfiable on the composition's own formula, not only on the slice the
# campaign solved.
#
# "The buggy polarity" is THE ASSIGNMENT THE CLAIM LAYER ACCEPTED, whether or
# not it moves anything. That is the whole of the rule, and it is not a
# synonym for "some root flipped". Since fix/root-polarity-labels the claim
# layer publishes three kinds of accepted witness and two of them move no root
# at all:
#
#   FLIPPED_PLANTED_MARKER          a planted Debug.makeSymbolicBoolean marker
#                                   moved off what it recorded (17899)
#   RECORDED_ROOT_VALUES_REPRODUCED every declared root sits at its recorded
#                                   value and the target is still reached --
#                                   the witness REPRODUCES the recording
#                                   rather than counterfactualising it
#                                   (17960: the epoch-1 NameNode recorded
#                                   dfs.namenode.snapshot.deletion.ordered =
#                                   false, and false is the polarity that
#                                   reaches the target)
#   UNPLANTED_ROOT_MOVED            a root that is not a planted marker moved
#
# A probe that hard-wired "buggy = something flipped" read 17960 exactly
# backwards once the runtime began capturing the configured source's recorded
# value: it flipped ordered to true, got unsat, and failed a run the claim
# layer had accepted -- while the formula was right all along (false sat, true
# unsat). So the accepted assignment is read from result.json and asserted as
# it stands, and a run that accepted NO witness falls back to
#
#   (b) each single-marker flip in turn, which is the question "is this marker
#       the mechanism" asked once per marker. An experiment may plant more than
#       one and they need not all be the bug: hdfs-17899-bug1 plants two on the
#       Balancer, and failing the constructor's updateBlockKeys aborts the test,
#       so asserting "every marker true" asks a question whose answer is unsat
#       for a reason that has nothing to do with the bug.
#
# A flip is a move off a recorded value, so that fallback needs one: where the
# manifest states no recorded value for a declared root the probe writes
# source UNSTATED_RECORDED_VALUE and asks nothing. It used to read an unstated
# value as true, the same default ClaimPolicy carried, and enumerate flips
# against it. There was also a step (a) -- a per-case declared polarity, one
# row, hdfs-17960 = false -- and it is gone with the case table above it: a
# run whose claim layer accepted nothing is a run the policy refused, and
# asserting a hard-coded polarity there can only manufacture a PASS.
#
# The other polarity is the complement of the buggy assignment where the case
# has a single Boolean root (17960: ordered=true), and the all-recorded
# valuation where it has several -- with two markers the world as recorded is
# one valuation and not one per marker. It is run and reported and is not
# required to be unsat. Under the acceptance ruling a witness there is a
# legitimate finding whenever every mechanism it names is something the world
# does -- a key-rotation race, clock drift inside the recorded window -- and
# ClaimPolicy has already withheld the claim if any satisfying witness rested
# on freedom nobody accounted for. A probe that demanded unsat here would
# refuse, on a weaker reading of the same evidence, runs the policy accepted;
# report.py prints what the polarity named instead.
#
# For hdfs-17897 and hdfs-11741 there is no Boolean root: the mechanism is
# wall-clock skew, so "other polarity" is every clock root pinned to the value
# it recorded, i.e. the world as it happened. Free sat with pinned unsat says
# the skew is what reaches the target, which is worth reporting; pinned sat
# says the target is reached without any skew at all, which is worth reporting
# too.
#
# Both cases declare the same two root families (DelegationKey#expiryDate and
# <org.apache.hadoop.util.Timer: long now()>.return), so one code path serves
# both: the recorded values come from the composition manifest's
# recordedRootValues rows, whose "wallClock" flag the composer sets from
# ClockRootPhysics.clockCallee -- true for Timer.now(), Time.now(),
# Time.monotonicNow() and System.currentTimeMillis(). Nothing in the pinning is
# case-specific.
#
# Writes probe.tsv (label, verdict, seconds) and probe/polarity.json (what each
# polarity asserted and where it came from, which report.py reads back); it
# touches only copies of the published formula and never the case directory.
#
# Environment: Z3_BIN (default z3, from PATH) and Z3_TIMEOUT_SECONDS
# (default 600, z3's own -T: budget; the outer timeout is a hard backstop for
# a z3 that wedges before it arms its own timer).
set -uo pipefail

ACCEPT_Z3=${Z3_BIN:-z3}
ACCEPT_Z3_TIMEOUT=${Z3_TIMEOUT_SECONDS:-600}

# Which root decides this case, and how its two polarities are spelled.
#   MARKER  -- a Debug.makeSymbolicBoolean fault marker (17899 bug1/2/3)
#   CONFIG  -- a configured Boolean source (17960's snapshotDeletionOrdered)
#   CLOCK   -- no Boolean root at all; the mechanism is wall-clock skew
#              (17897, 11741)
#
# 11741 is a CLOCK case, not a MARKER one: /opt/hadoop-hdfs-11741 contains no
# Debug.makeSymbolicBoolean anywhere (grep over the whole checkout), so there
# is no fault marker to flip.  Its declared roots are the same two families
# 17897 declares -- DelegationKey#expiryDate and <org.apache.hadoop.util.Timer:
# long now()>.return -- and the mechanism is the same: a BlockKey ages out of
# allKeys under a symbolic clock while the Balancer's cached
# DataEncryptionKey keeps naming it.
#
# This table says how the PROBE spells a case's two polarities.  What the
# composition must have CONCLUDED for the case to pass is the other per-case
# table, EXPECTED_MECHANISM at the top of report.py, which is where the PASS
# criterion is computed.  Keep the two consistent: a case whose root kind
# changes here needs its expected witness kind revisited there.
acc_root_kind_of() {
  case "$1" in
    hdfs-17899-*)            echo MARKER ;;
    hdfs-17960)              echo CONFIG ;;
    hdfs-17897|hdfs-11741)   echo CLOCK ;;
    *)                       echo MARKER ;;
  esac
}

# The declared-polarity table that used to sit beside this one is gone.  It
# held one row -- hdfs-17960 = false, from that case's README.md -- as the last
# resort for a run whose claim layer accepted no witness.  The recorded value
# is now an observation the manifest carries (roots[].recordedValue), so "what
# did this root hold" is answered by the recording rather than by a table; and
# a run whose claim layer accepted nothing is a run the policy refused, where
# asserting a hard-coded polarity and reporting sat can only manufacture a PASS
# the evidence did not earn.  A probe that cannot read the recorded value says
# so (source UNSTATED_RECORDED_VALUE) instead of assuming one.

case_id=${1:?case}; dir=${2:?case dir}; work=${3:?work dir}
final="$dir/schedule/final"
C="$final/candidate.smt2"; M="$final/candidate_composition_manifest.json"
mkdir -p "$work/probe"
: >"$work/probe.tsv"

[[ -s "$C" ]] || { echo "no candidate.smt2 for $case_id" >&2; exit 1; }
# UNPINNED, which is what the header above says this probe is.  The composer
# writes the valuation it was asked about into the file it publishes --
# `(assert (! (= <root> true) :named valuation__<root>))` -- so a probe that
# kept those pins was asking about ONE valuation and not about the formula:
# 17960's candidate.smt2 carries ordered=true, which is why `plain` came back
# unsat, and asserting the other polarity on top of it is unsat whatever the
# formula says.  Each polarity below asserts its own.
grep -av '^(check-sat' "$C" | grep -av '^(get-value' \
  | grep -av ':named valuation__' >"$work/probe/body.smt2"

run() {  # run <label> <assert-file-or-empty>
  local label=$1 extra=${2:-} f t0 out
  f="$work/probe/$(printf '%s' "$label" | tr -c 'A-Za-z0-9._-' '_').smt2"
  cat "$work/probe/body.smt2" >"$f"
  [[ -n "$extra" && -s "$extra" ]] && cat "$extra" >>"$f"
  echo '(check-sat)' >>"$f"
  t0=$(date +%s)
  out=$(timeout $((ACCEPT_Z3_TIMEOUT+60)) "$ACCEPT_Z3" -T:"$ACCEPT_Z3_TIMEOUT" "$f" 2>&1 | tail -1)
  out=${out:-NO_OUTPUT}
  printf '%s\t%s\t%s\n' "$label" "$out" "$(( $(date +%s)-t0 ))" >>"$work/probe.tsv"
  printf 'PROBE %-22s %-10s %ss\n' "$label" "$out" "$(( $(date +%s)-t0 ))"
}

kind=$(acc_root_kind_of "$case_id")
printf '%s\n' "$kind" >"$work/probe/kind.txt"
echo "== $case_id plain probe (root kind: $kind)"
run plain ""

case "$kind" in
MARKER|CONFIG)
  # Read the accepted assignment out of the claim layer's own output and
  # spell it as asserts.
  #
  # THREE sources of Boolean roots are deleted here, not repaired.  Two were
  # already gone: z3-result.json's roots.booleanInputs (design 3's SOLVE
  # stage writes no such file) and a regex for one case's variable spelling
  # in candidate.smt2.  The third is manifest.booleanRoots, which this probe
  # read until now and which no stage has published since design 3 -- so the
  # probe reported `buggy NO_ROOT / other NO_ROOT` on every run, including
  # the accepted 17960 one.
  #
  # What replaces it is the field the composer DOES publish: manifest.roots,
  # one {rootId, kind, recordedValue} row per declared root.  recordedValue
  # is the recording's own observation, so recordedRootValues and the
  # configured-source materialization row go with booleanRoots.
  #
  # The question the deleted sources served -- does the recorded valuation
  # refute the recording -- is still ClaimPolicy.polarityDecides, computed by
  # the composer that holds the formula, the domains and the arms.  This
  # probe is a reported signal; it does not gate, and it does not re-derive
  # the composer's answer from its artifacts.
  python3 - "$final/result.json" "$M" "$C" "$work/probe" "$case_id" \
           <<'PY'
import json, os, re, sys

(result_path, manifest_path, smt_path, out, case_id) = sys.argv[1:6]


def load(path):
    try:
        with open(path) as handle:
            return json.load(handle)
    except Exception:
        return {}


result, manifest = load(result_path), load(manifest_path)
solver = manifest.get("solver") or {}
valuations = solver.get("valuations") or []


def write(name, text):
    with open(os.path.join(out, name), "w") as handle:
        handle.write(text)


def assignment_of(ordinal):
    for row in valuations:
        if row.get("ordinal") == ordinal:
            return row.get("assignment") or {}
    return {}


# ---- the declared roots, as the manifest PUBLISHES them -------------------
# One published shape: manifest.roots, one RootDomain row per declared root
# -- {rootId, kind, recordedValue}.  booleanRoots is what this probe read
# until now and no stage has published it since design 3; recordedRootValues
# and configuredSourceMaterializations went with it.  None of the three is
# replaced by a second source: the kind on the row says which roots are
# Boolean and the row states what the recording read.
roots = [row for row in (manifest.get("roots") or [])
         if row.get("kind") == "MARKER"]
recorded = {}
for row in roots:
    value = row.get("recordedValue", "")
    if value not in ("", None):
        recorded[row.get("rootId", "")] = str(value).lower()

# ---- each root's solver term, from the composer's own valuation pins ------
# The manifest names a root by rootId and never by its solver name, so the
# terms come from the pins the COMPOSER wrote into the file it published:
#   (assert (! (= <term> true|false) :named valuation__<term>))
# one per root of valuation 0, in the order that valuation's assignment has
# them.  The join is CHECKED and not assumed -- each pin's value must be the
# value valuation 0 states for the root at its own position -- so a probe
# that cannot line the two up refuses by name instead of asserting over a
# term it guessed.  (The old regex for one case's variable spelling is not
# coming back either.)
PIN = re.compile(r"^\(assert \(! \(= (.+?) (true|false)\) :named valuation__")
pins = []
try:
    with open(smt_path) as handle:
        for line in handle:
            found = PIN.match(line.rstrip("\n"))
            if found:
                pins.append((found.group(1), found.group(2)))
except Exception:
    pins = []

zero = assignment_of(0)
keys = list(zero.keys())
term_of, join_why = {}, ""
if len(pins) != len(keys):
    join_why = ("candidate.smt2 carries %d valuation pin(s) and valuation 0"
                " states %d root(s), so no term is joined to a root"
                % (len(pins), len(keys)))
else:
    for index, key in enumerate(keys):
        term, value = pins[index]
        if value != str(zero[key]).lower():
            term_of, join_why = {}, (
                "valuation pin %d asserts %s=%s and valuation 0 states"
                " %s=%s, so the pins do not line up with the assignment"
                % (index, term, value, key, str(zero[key]).lower()))
            break
        term_of[key] = term

markers = [row for row in roots if row.get("rootId") in term_of]
identities = [row.get("rootId", "?") for row in markers]
terms = [term_of[name] for name in identities]
recorded_stated = [name in recorded for name in identities]
every_value_stated = all(recorded_stated)
# Only meaningful where stated; None says "the recording did not say".
recorded_polarity = [recorded[name] != "false" if name in recorded else None
                     for name in identities]
# A declared Boolean root the composition publishes no pin for is one no
# admitted path's formula names -- the composer says so itself, as a
# DECLARATION_MISSING gap -- so there is nothing in this formula to assert
# about it, and it is named rather than counted.
unpinned = [row.get("rootId", "?") for row in roots
            if row.get("rootId") not in term_of]


def assertion(values):
    lines = []
    for term, value in zip(terms, values):
        lines.append("(assert %s)" % term if value
                     else "(assert (not %s))" % term)
    return "\n".join(lines) + ("\n" if lines else "")


def spell(values):
    return ", ".join("%s=%s" % (identities[i], str(values[i]).lower())
                     for i in range(len(terms)))


if not terms:
    why = (join_why or ("the composition manifest publishes no declared"
                        " Boolean root: %d root(s), %d of kind MARKER"
                        % (len(manifest.get("roots") or []), len(roots))))
    if unpinned:
        why += ("; no valuation pin names %s, so this formula says nothing"
                " about it" % ", ".join(unpinned))
    write("source.txt", "NO_ROOT\n")
    write("polarity.json", json.dumps(
        {"case": case_id, "source": "NO_ROOT", "sourceDetail": why,
         "terms": [], "identities": [],
         "why": "the polarity question is ClaimPolicy.polarityDecides, which"
                " the acceptance gate reads out of result.json directly"},
        indent=1) + "\n")
    print("  no Boolean root this probe can assert: %s" % why)
    raise SystemExit(0)

write("markers.txt", "".join(
    "%s  recorded=%s\n"
    % (identities[i],
       str(recorded_polarity[i]).lower() if recorded_stated[i]
       else "(nothing states one)")
    for i in range(len(terms))))

# ---- the assignment the claim layer accepted ------------------------------
# result.json publishes the claim's own valuation: findingKind names the
# mechanism, valuationOrdinal says which valuation carried it, and the
# manifest's solver.valuations row of that ordinal states the assignment.
# That IS the accepted witness; there is no separate witness ledger to scan
# and no row to identify by a flag.
finding_kind = result.get("findingKind") or ""
ordinal = result.get("valuationOrdinal")
buggy_values, source = None, None
if not isinstance(ordinal, int) or isinstance(ordinal, bool):
    detail = "result.json publishes no valuationOrdinal"
elif not finding_kind or finding_kind == "NO_SUPPORTED_WITNESS":
    detail = ("the claim layer accepted no witness (findingKind=%s)"
              % (finding_kind or "(absent)"))
else:
    accepted = assignment_of(ordinal)
    if all(name in accepted for name in identities):
        buggy_values = [str(accepted[name]).lower() != "false"
                        for name in identities]
        source = "ACCEPTED_WITNESS"
        detail = ("result.json findingKind=%s at valuation %d"
                  % (finding_kind, ordinal))
    else:
        detail = ("the accepted valuation %d states no value for every"
                  " declared root" % ordinal)

moved = []
if buggy_values is not None:
    # A move is a move off an observed value. A root nothing recorded is not
    # "moved" and not "left alone" either, so it is named separately.
    moved = [identities[i] for i in range(len(terms))
             if recorded_stated[i] and buggy_values[i] != recorded_polarity[i]]
unstated = [identities[i] for i in range(len(terms))
            if not recorded_stated[i]]

# ---- the other polarity ---------------------------------------------------
# One Boolean root has a complement and the probe asserts it, so the two runs
# are the two answers to one question.  Several markers have no complement:
# "other" is then the one valuation that moves none of them, which needs every
# recorded value to be an observation.
if buggy_values is not None and len(terms) == 1:
    other_values, other_mode = [not buggy_values[0]], "COMPLEMENT"
elif every_value_stated:
    other_values, other_mode = list(recorded_polarity), "ALL_RECORDED"
else:
    other_values, other_mode = None, "UNSTATED_RECORDED_VALUE"
if other_values is not None:
    write("other.assert", assertion(other_values))

polarity = {
    "case": case_id,
    "source": source or ("SINGLE_MARKER_ENUMERATION" if every_value_stated
                         else "UNSTATED_RECORDED_VALUE"),
    "sourceDetail": detail,
    "acceptedWitnessKind": "",
    "acceptedValuationOrdinal": ordinal,
    "terms": terms,
    "identities": identities,
    "recordedPolarity": recorded_polarity,
    "recordedPolarityStated": recorded_stated,
    "unstatedRecordedRootValues": unstated,
    "unpinnedDeclaredRoots": unpinned,
    "acceptedFindingKind": finding_kind,
    "buggyValues": buggy_values,
    "buggyMovesRoots": moved,
    "otherValues": other_values,
    "otherMode": other_mode,
}

if buggy_values is not None:
    write("buggy.assert", assertion(buggy_values))
    write("source.txt", source + "\n")
    write("accepted.txt", (", ".join(moved) or "(no root moved)") + "\n")
    write("polarity.json", json.dumps(polarity, indent=1) + "\n")
    print("  buggy  = %s [%s, %s]"
          % (spell(buggy_values), source, finding_kind))
    print("         %s" % detail)
    if moved:
        moves = "moves " + ", ".join(moved)
    elif unstated:
        moves = ("moves nothing that can be called a move: no recorded value"
                 " is stated for " + ", ".join(unstated))
    else:
        moves = ("moves nothing: every declared root sits at the value the"
                 " recording had")
    print("         %s" % moves)
    print("  other  = %s [%s]" % (spell(other_values), other_mode))
    raise SystemExit(0)

# (b) No accepted assignment to read: ask each marker on its own, which is the
# question "is this marker the mechanism" asked once per marker. A flip needs a
# value to be a flip off, so a root the recording did not state stops this
# before it guesses one.
if not every_value_stated:
    write("source.txt", "UNSTATED_RECORDED_VALUE\n")
    write("polarity.json", json.dumps(polarity, indent=1) + "\n")
    print("  %s" % detail)
    print("  no recorded value is stated for %d declared root(s) (%s), so"
          " neither polarity of them names anything the recording had"
          % (len(unstated), ", ".join(unstated)))
    raise SystemExit(0)
write("source.txt", "SINGLE_MARKER_ENUMERATION\n")
labels = []
for index, term in enumerate(terms):
    values = list(recorded_polarity)
    values[index] = not values[index]
    write("flip_%d.assert" % index, assertion(values))
    labels.append("%d\t%s" % (index, identities[index]))
write("flips.txt", "\n".join(labels) + "\n")
polarity["flips"] = list(identities)
write("polarity.json", json.dumps(polarity, indent=1) + "\n")
print("  %s: enumerating %d single-marker flip(s)" % (detail, len(terms)))
print("  other  = %s [%s]" % (spell(other_values), other_mode))
PY

  source=$(cat "$work/probe/source.txt" 2>/dev/null || echo NO_ROOT)
  case "$source" in
  NO_ROOT)
    printf 'buggy\tNO_ROOT\t0\nother\tNO_ROOT\t0\n' >>"$work/probe.tsv"
    exit 0
    ;;
  UNSTATED_RECORDED_VALUE)
    # Nothing observed what a declared root held, so there is no polarity to
    # call buggy and none to call other. Reported as the open question it is.
    printf 'buggy\tUNSTATED_RECORDED_VALUE\t0\n' >>"$work/probe.tsv"
    printf 'other\tUNSTATED_RECORDED_VALUE\t0\n' >>"$work/probe.tsv"
    exit 0
    ;;
  ACCEPTED_WITNESS)
    run buggy "$work/probe/buggy.assert"
    ;;
  SINGLE_MARKER_ENUMERATION)
    # Every flip is reported under its own marker, and "buggy" is the
    # question the case asks: is there a way to move one marker that reaches
    # the target. sat from any one of them answers it.
    best=unsat
    while IFS=$'\t' read -r index identity; do
      [[ -n "$index" ]] || continue
      run "buggy.${identity}" "$work/probe/flip_${index}.assert"
      verdict=$(awk -F'\t' -v l="buggy.${identity}" '$1==l{print $2}' \
                  "$work/probe.tsv" | tail -1)
      case "$verdict" in
        sat) best=sat ;;
        unsat) ;;
        *) [[ "$best" == unsat ]] && best=$verdict ;;
      esac
    done <"$work/probe/flips.txt"
    # One row named "buggy", so a reader and the report agree on what the
    # case's own question answered; the per-marker rows stay beside it.
    printf 'buggy\t%s\t0\n' "$best" >>"$work/probe.tsv"
    printf 'PROBE %-22s %-10s (from single-marker flips)\n' buggy "$best"
    ;;
  esac
  if [[ -s "$work/probe/other.assert" ]]; then
    run other "$work/probe/other.assert"
  else
    printf 'other\tUNSTATED_RECORDED_VALUE\t0\n' >>"$work/probe.tsv"
  fi
  ;;
CLOCK)
  # No Boolean root. Pin every wall clock to what it actually read: if the
  # target is then unreachable, the skew is the mechanism.
  #
  # A manifest that carries no recordedRootValues pins nothing, and then the
  # two polarities are the same query and the probe decides nothing. Say so
  # rather than reporting an accidental sat/sat as a verdict.
  #
  # That is the state of the pipeline as this lands: no stage publishes a
  # recordedRootValues row, and a clock root has no solver term in the manifest
  # (roots[] names it by rootId), so on a clock case this branch pins nothing
  # and warns by name.  The reading it would give is reported, never gated on:
  # whether the skew is the mechanism is ClaimPolicy's CLOCK_SKEW finding,
  # which report.py reads out of result.json.
  python3 - "$M" "$work/probe/pinned.assert" "$work/probe/polarity.json" \
           "$case_id" <<'PY'
import json, sys
manifest, out, polarity_out, case_id = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
rows = []
try:
    doc = json.load(open(manifest))
except Exception:
    doc = {}
for row in doc.get("recordedRootValues", []) or []:
    if not row.get("wallClock"):
        continue
    term, value = row.get("solverTerm", ""), str(row.get("recordedValue", ""))
    if not term or not value:
        continue
    literal = "(- %s)" % value[1:] if value.startswith("-") else value
    rows.append("(assert (= %s %s))" % (term, literal))
open(out, "w").write("\n".join(rows) + ("\n" if rows else ""))
json.dump({"case": case_id, "source": "CLOCKS_FREE", "terms": [],
           "otherMode": "CLOCKS_PINNED", "pinnedClockRoots": len(rows)},
          open(polarity_out, "w"), indent=1)
print("pinned %d wall-clock root(s)" % len(rows))
PY
  if [[ ! -s "$work/probe/pinned.assert" ]]; then
    echo "  WARN no wall-clock root pinned: the manifest carries no" \
         "recordedRootValues row with wallClock=true, so other would" \
         "repeat buggy and decide nothing"
  fi
  run buggy ""                              # clocks free: skew allowed
  run other "$work/probe/pinned.assert"     # clocks as recorded: no skew
  ;;
esac

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
# synonym for "some root flipped". The claim layer publishes three kinds of
# accepted witness and two of them move no root at all:
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
# A probe that hard-wired "buggy = something flipped" would read 17960 exactly
# backwards: it would flip ordered to true, get unsat, and fail a run the claim
# layer accepted while the formula is right (false sat, true unsat). So the
# accepted assignment is read from result.json and asserted as it stands, and
# a run that accepted NO witness falls back to
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
# source UNSTATED_RECORDED_VALUE and asks nothing. There is no per-case
# declared polarity either: a run whose claim layer accepted nothing is a run
# the policy refused, and asserting a hard-coded polarity there can only
# manufacture a PASS.
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
# A case whose manifest declares no Boolean root (hdfs-11741: its mechanism
# is wall-clock skew) has no second polarity to spell: the probe says NO_ROOT
# and the claim layer's CLOCK_SKEW finding, which report.py reads out of
# result.json, is the answer.
#
# Writes probe.tsv (label, verdict, seconds) and probe/polarity.json (what each
# polarity asserted and where it came from, which report.py reads back); it
# touches only copies of the published formula and never the case directory.
#
# Environment: Z3_BIN (default tools/lib/gc-env.sh's), Z3_TIMEOUT_SECONDS (default
# 600, z3's own -T: budget; the outer timeout is a hard backstop for a z3 that
# wedges before it arms its own timer) and PROBE_WHOLE_SECONDS (default 60,
# at most Z3_TIMEOUT_SECONDS): the budget of each question asked whole before
# it is asked one path at a time, as ClaimPolicy#byDisjunct does.
set -uo pipefail

# shellcheck source=../../tools/lib/gc-env.sh
source "$(dirname "${BASH_SOURCE[0]}")/../../tools/lib/gc-env.sh"
# shellcheck source=../../tools/lib/z3-race.sh
source "$(dirname "${BASH_SOURCE[0]}")/../../tools/lib/z3-race.sh"
ACCEPT_Z3_TIMEOUT=${Z3_TIMEOUT_SECONDS:-600}
ACCEPT_WHOLE=${PROBE_WHOLE_SECONDS:-60}
(( ACCEPT_WHOLE > ACCEPT_Z3_TIMEOUT )) && ACCEPT_WHOLE=$ACCEPT_Z3_TIMEOUT

case_id=${1:?case}; dir=${2:?case dir}; work=${3:?work dir}
final="$dir/schedule/final"
C="$final/candidate.smt2"; M="$final/candidate_composition_manifest.json"
mkdir -p "$work/probe"
: >"$work/probe.tsv"

[[ -s "$C" ]] || { echo "no candidate.smt2 for $case_id" >&2; exit 1; }
# UNPINNED, which is what the header above says this probe is.  The composer
# writes the valuation it was asked about into the file it publishes --
# `(assert (! (= <root> true) :named valuation__<root>))` -- so a probe that
# kept those pins would ask about ONE valuation and not about the formula, and
# asserting the other polarity on top of it would be unsat whatever the
# formula says.  Each polarity below asserts its own.
grep -av '^(check-sat' "$C" | grep -av '^(get-value' \
  | grep -av ':named valuation__' >"$work/probe/body.smt2"

solve() {  # solve <file> <seconds>: z3's verdict line, both arithmetic engines raced
  local out
  out=$(z3_race "$1" "$2" | tail -1)
  printf '%s' "${out:-NO_OUTPUT}"
}

# One path's text per path selector of the manifest, as ClaimPolicy asks a
# disjunction z3 left undecided whole (Composition#pathQuery): the body
# without the commands another path's selector guards -- (assert (=> <sel>
# ...)), named or not, vacuous once the partition forces that selector
# false -- and with its own selector asserted.  Written once, on first need.
split_paths() {
  [[ -e "$work/probe/paths/done" ]] && return
  mkdir -p "$work/probe/paths"
  python3 - "$work/probe/body.smt2" "$M" "$work/probe/paths" <<'PY'
import json, sys

body_path, manifest_path, out = sys.argv[1:4]
body = open(body_path).read()
try:
    selectors = [row["selector"] for row in
                 json.load(open(manifest_path)).get("paths") or []
                 if row.get("selector")]
except Exception:
    selectors = []
known = set(selectors)


def guard(command):
    for head in ("(assert (! (=> ", "(assert (=> "):
        if command.startswith(head):
            token = command[len(head):].split(" ", 1)[0]
            return token if token in known else None
    return None


# Top-level commands, skipping bar-quoted symbols, string literals ("" is an
# escaped quote) and comments whole, as Composer#commands does.
commands, start, depth, index = [], 0, 0, 0
while index < len(body):
    at = body[index]
    if at == "|":
        close = body.find("|", index + 1)
        index = len(body) if close < 0 else close + 1
        continue
    if at == '"':
        close = index + 1
        while close < len(body):
            if body[close] == '"':
                if close + 1 < len(body) and body[close + 1] == '"':
                    close += 2
                    continue
                break
            close += 1
        index = close + 1
        continue
    if at == ";":
        close = body.find("\n", index)
        index = len(body) if close < 0 else close
        continue
    if at == "(":
        depth += 1
    elif at == ")":
        depth -= 1
        if depth == 0:
            text = body[start:index + 1]
            commands.append((text, guard(text.lstrip())))
            start = index + 1
    index += 1
if start < len(body):
    commands.append((body[start:], None))

for number, selector in enumerate(selectors):
    with open("%s/%d.smt2" % (out, number), "w") as handle:
        for text, owner in commands:
            if owner is None or owner == selector:
                handle.write(text)
        handle.write("\n(assert %s)\n" % selector)
open("%s/done" % out, "w").close()
PY
}

# run <label> <assert-file-or-empty>: the whole formula within
# PROBE_WHOLE_SECONDS; undecided, one path at a time, each within z3's full
# budget: the first sat path answers, else the first undecided verdict, else
# unsat.  One row either way, as the engine's valuation asks are one answer.
run() {
  local label=$1 extra=${2:-} f t0 out name each verdict undecided
  name=$(printf '%s' "$label" | tr -c 'A-Za-z0-9._-' '_')
  f="$work/probe/$name.smt2"
  cat "$work/probe/body.smt2" >"$f"
  [[ -n "$extra" && -s "$extra" ]] && cat "$extra" >>"$f"
  echo '(check-sat)' >>"$f"
  t0=$(date +%s)
  out=$(solve "$f" "$ACCEPT_WHOLE")
  if [[ "$out" != sat && "$out" != unsat ]]; then
    split_paths
    undecided=""
    verdict=""
    for each in $(ls "$work/probe/paths" | grep '\.smt2$' | sort -n); do
      cat "$work/probe/paths/$each" >"$work/probe/paths/$name.$each.q"
      [[ -n "$extra" && -s "$extra" ]] \
        && cat "$extra" >>"$work/probe/paths/$name.$each.q"
      echo '(check-sat)' >>"$work/probe/paths/$name.$each.q"
      verdict=$(solve "$work/probe/paths/$name.$each.q" "$ACCEPT_Z3_TIMEOUT")
      rm -f "$work/probe/paths/$name.$each.q"
      [[ "$verdict" == sat ]] && break
      [[ "$verdict" != unsat && -z "$undecided" ]] && undecided=$verdict
    done
    if [[ -n "$verdict" ]]; then
      if [[ "$verdict" == sat ]]; then out=sat
      elif [[ -n "$undecided" ]]; then out=$undecided
      else out=unsat
      fi
    fi
  fi
  printf '%s\t%s\t%s\n' "$label" "$out" "$(( $(date +%s)-t0 ))" >>"$work/probe.tsv"
  printf 'PROBE %-22s %-10s %ss\n' "$label" "$out" "$(( $(date +%s)-t0 ))"
}

echo "== $case_id plain probe"
run plain ""

# Read the accepted assignment out of the claim layer's own output and
# spell it as asserts.
#
# The declared roots are the field the composer publishes: manifest.roots,
# one {rootId, kind, recordedValue} row per declared root.  recordedValue
# is the recording's own observation.
#
# Whether the recorded valuation refutes the recording is
# ClaimPolicy.polarityDecides, computed by the composer that holds the
# formula, the domains and the arms.  This probe is a reported signal; it
# does not gate, and it does not re-derive the composer's answer from its
# artifacts.
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
# -- {rootId, kind, recordedValue}.  The kind on the row says which roots are
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
# term it guessed.
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

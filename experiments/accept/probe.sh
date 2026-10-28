#!/usr/bin/env bash
set -uo pipefail

# shellcheck source=../../tools/lib/gc-env.sh
source "$(dirname "${BASH_SOURCE[0]}")/../../tools/lib/gc-env.sh"
# shellcheck source=../../tools/lib/z3-race.sh
source "$(dirname "${BASH_SOURCE[0]}")/../../tools/lib/z3-race.sh"
ACCEPT_Z3_TIMEOUT=${Z3_TIMEOUT_SECONDS:-600}
ACCEPT_WHOLE=${PROBE_WHOLE_SECONDS:-60}
# The probe re-decides what the campaign's DECIDE already decided, for the report alone: its per-path split stops at
# this budget over the whole probe (solr-adhoc-05, R3: 340 paths x up to 600 s each, serially, held its row for hours).
ACCEPT_BUDGET=${PROBE_BUDGET_SECONDS:-900}
# Each path's query repeats the shared body, so the split writes about body x paths: past this size it is not written
# and the probe says BUDGET (solr-adhoc-05, X1C: a 793 MB body x 349 paths had written 29 GB over NFS in 10 min).
ACCEPT_SPLIT_MAX_MB=${PROBE_SPLIT_MAX_MB:-2048}
probe_started=$(date +%s)
(( ACCEPT_WHOLE > ACCEPT_Z3_TIMEOUT )) && ACCEPT_WHOLE=$ACCEPT_Z3_TIMEOUT

case_id=${1:?case}; dir=${2:?case dir}; work=${3:?work dir}
final="$dir/schedule/final"
C="$final/candidate.smt2"; M="$final/candidate_composition_manifest.json"
mkdir -p "$work/probe"
: >"$work/probe.tsv"

[[ -s "$C" ]] || { echo "no candidate.smt2 for $case_id" >&2; exit 1; }
grep -av '^(check-sat' "$C" | grep -av '^(get-value' \
  | grep -av ':named valuation__' >"$work/probe/body.smt2"

solve() {  # solve <file> <seconds>: z3's verdict line, both arithmetic engines raced
  local out
  out=$(z3_race "$1" "$2" | tail -1)
  printf '%s' "${out:-NO_OUTPUT}"
}

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

run() {
  local label=$1 extra=${2:-} f t0 out name each verdict undecided
  name=$(printf '%s' "$label" | tr -c 'A-Za-z0-9._-' '_')
  f="$work/probe/$name.smt2"
  cat "$work/probe/body.smt2" >"$f"
  [[ -n "$extra" && -s "$extra" ]] && cat "$extra" >>"$f"
  echo '(check-sat)' >>"$f"
  t0=$(date +%s)
  out=$(solve "$f" "$ACCEPT_WHOLE")
  if [[ "$out" != sat && "$out" != unsat ]] \
      && (( $(stat -c %s "$work/probe/body.smt2") / 1048576 * $(python3 -c \
        'import json,sys; print(len(json.load(open(sys.argv[1])).get("paths") or []))' "$M" 2>/dev/null \
        || echo 0) > ACCEPT_SPLIT_MAX_MB )); then
    out=BUDGET
  elif [[ "$out" != sat && "$out" != unsat ]]; then
    split_paths
    undecided=""
    verdict=""
    for each in $(ls "$work/probe/paths" | grep '\.smt2$' | sort -n); do
      if (( $(date +%s) - probe_started >= ACCEPT_BUDGET )); then
        verdict=BUDGET
        [[ -n "$undecided" ]] || undecided=BUDGET
        break
      fi
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
  printf 'buggy\tUNSTATED_RECORDED_VALUE\t0\n' >>"$work/probe.tsv"
  printf 'other\tUNSTATED_RECORDED_VALUE\t0\n' >>"$work/probe.tsv"
  exit 0
  ;;
ACCEPTED_WITNESS)
  run buggy "$work/probe/buggy.assert"
  ;;
SINGLE_MARKER_ENUMERATION)
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
  printf 'buggy\t%s\t0\n' "$best" >>"$work/probe.tsv"
  printf 'PROBE %-22s %-10s (from single-marker flips)\n' buggy "$best"
  ;;
esac
if [[ -s "$work/probe/other.assert" ]]; then
  run other "$work/probe/other.assert"
else
  printf 'other\tUNSTATED_RECORDED_VALUE\t0\n' >>"$work/probe.tsv"
fi

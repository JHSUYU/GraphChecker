#!/usr/bin/env bash
#
# One gate for one shrink wave.  Run it ONCE after a large batch of deletions,
# never after each small cut: it prints the src/main line count against the
# README's 30,000 target, proves the P0 tombstone is still zero-hit, compiles,
# runs the unit suite, and -- when a finished RPC-matrix root is given -- checks
# that all twenty rows still PASS.  Exit status is the verdict.
#
# Usage:
#   experiments/shrink/gate.sh                       # count + P0 + compile + unit suite
#   experiments/shrink/gate.sh --matrix <matrix-root> # also require 20/20 in matrix-summary.json
#   experiments/shrink/gate.sh --matrix <new> --baseline <old>
#                                                     # also require the per-row symbolic
#                                                     # variable set to match the baseline
#   experiments/shrink/gate.sh --replay <matrix-root>
#                                                     # also recompose all 20 rows' candidate.smt2
#                                                     # and replay all recorded path-flip queries
#                                                     # against the current jar (~3.5 min, no VM run)
#   experiments/shrink/gate.sh --snapshot <name>      # also write per-file counts to counts-<name>.tsv
#   experiments/shrink/gate.sh --count-only           # just the line counts (seconds)
#
set -uo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
cd "${repo_root}" || exit 2
target=30000
matrix_root=""
baseline_root=""
replay_root=""
count_only=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --matrix) matrix_root=$2; shift 2 ;;
    --baseline) baseline_root=$2; shift 2 ;;   # matrix root to compare symbolic variables against
    --replay) replay_root=$2; shift 2 ;;       # matrix root to recompose + replay flips against (~3.5 min)
    --count-only) count_only=1; shift ;;
    --snapshot) snapshot=$2; shift 2 ;;      # write per-file nonblank counts to counts-<name>.tsv
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

# Per-wave attribution without commits: the working tree carries every wave
# uncommitted, so `git diff HEAD` mixes them.  A per-file count snapshot at
# each gate is what a lane's delta is measured against.
if [[ -n ${snapshot:-} ]]; then
  out="experiments/shrink/counts-${snapshot}.tsv"
  { printf 'file\tnonblank\n'
    find src/main/java -name '*.java' | sort | while read -r f; do
      printf '%s\t%s\n' "${f#src/main/java/edu/uva/liftlab/graphchecker/}" "$(grep -cv '^[[:space:]]*$' "$f")"
    done; } > "${out}"
  printf '[gate] snapshot: %s (%s files)\n' "${out}" "$(( $(wc -l < "${out}") - 1 ))"
fi

fail=0
say() { printf '[gate] %s\n' "$*"; }

main_lines=$(find src/main/java -name '*.java' -exec cat {} + | grep -cv '^[[:space:]]*$')
test_lines=$(find src/test/java -name '*.java' -exec cat {} + | grep -cv '^[[:space:]]*$')
# Two metrics, both reported: the README target is comment-stripped code; the
# owner counts every nonblank line.  A wave must move both.
code_lines=$(python3 - <<'PY'
import pathlib
def strip(s):
    o=[];i=0;n=len(s);q=None
    while i<n:
        c=s[i]
        if q:
            o.append(c)
            if c=='\\': o.append(s[i+1]); i+=2; continue
            if c==q: q=None
            i+=1; continue
        if c in '"\'': q=c;o.append(c);i+=1;continue
        if s.startswith('//',i):
            j=s.find('\n',i); i=n if j<0 else j; continue
        if s.startswith('/*',i):
            j=s.find('*/',i+2); seg=s[i:(n if j<0 else j+2)]
            o.append('\n'*seg.count('\n')); i=n if j<0 else j+2; continue
        o.append(c);i+=1
    return ''.join(o)
print(sum(1 for f in pathlib.Path('src/main/java').rglob('*.java')
          for l in strip(f.read_text(errors='ignore')).splitlines() if l.strip()))
PY
)
say "src/main nonblank lines: ${main_lines}  (target ${target}, $(( main_lines > target ? main_lines - target : 0 )) over)"
say "src/main code-only lines: ${code_lines}  (comments: $(( main_lines - code_lines )))"
say "src/test nonblank lines: ${test_lines}"
[[ ${count_only} -eq 1 ]] && exit 0

# P0 tombstone: six greps that must stay zero-hit (README "P0 complete").
for pattern in SegmentComposition continuationPort segmentIdentity rePair clientPrefix continuationWindow; do
  hits=$(grep -rn --include='*.java' "${pattern}" src/ | wc -l)
  if [[ ${hits} -ne 0 ]]; then say "P0 FAIL: ${pattern} has ${hits} hit(s)"; fail=1; fi
done
[[ ${fail} -eq 0 ]] && say "P0 tombstone: zero-hit on all six"

if ! mvn -q compile >/dev/null 2>&1; then
  say "COMPILE FAIL"; mvn -q compile 2>&1 | grep -E 'ERROR.*\.java' | head -20; exit 1
fi
say "compile: ok"

# The suite decides; strip ANSI so the totals line is greppable.
totals=$(mvn test 2>&1 | sed 's/\x1b\[[0-9;]*m//g' | grep -E '^\[(INFO|ERROR)\] Tests run: [0-9]+, Failures: [0-9]+, Errors: [0-9]+, Skipped: [0-9]+$' | tail -1)
say "unit suite: ${totals:-NO TOTALS LINE}"
if [[ -z ${totals} ]] || ! grep -qE 'Failures: 0, Errors: 0' <<<"${totals}"; then fail=1; fi

if [[ -n ${matrix_root} ]]; then
  summary=${matrix_root}/matrix-summary.json
  if [[ ! -f ${summary} ]]; then say "MATRIX FAIL: no ${summary}"; fail=1
  else
    pass=$(jq '[.[]|select(.status=="PASS")]|length' "${summary}")
    say "RPC matrix: ${pass}/20 PASS"
    if [[ ${pass} -ne 20 ]]; then
      jq -c '[.[]|select(.status!="PASS")|{scenario,status}]' "${summary}"; fail=1
    fi
  fi
  # PASS alone is not enough: a symbolic variable silently dropped from the
  # model can leave a row SAT.  Compare the per-row set of symbolic variable
  # names in z3-result.json against the baseline matrix, row by row.
  if [[ -n ${baseline_root} ]]; then
    # A variable's identity for this check is inputKind|sourceId|fieldSignature
    # per valuation.  sourcePhaseId/sourceOccurrenceId are name-UUIDs of the
    # hook SITE and legitimately change when a Hadoop hook signature moves, so
    # a difference there is reported, not failed.
    # The variable SET is the distinct (inputKind, sourceId, fieldSignature)
    # triples across all models; the model COUNT is reported separately so a
    # count change is named as such rather than showing up as a variable diff.
    vars_of() { jq -r '.symbolicVariableModels[]?.variables[]? | "\(.inputKind)|\(.sourceId)|\(.fieldSignature)"' "$1" 2>/dev/null | sort -u; }
    sites_of() { jq -r '.symbolicVariableModels[]?.variables[]? | "\(.sourceId)|\(.sourceOccurrenceId)|\(.sourcePhaseId)"' "$1" 2>/dev/null | sort -u; }
    models_of() { jq '.symbolicVariableModels | length' "$1" 2>/dev/null; }
    row_result() { find "$1" -maxdepth 3 -path "*/scenario-$(printf '%02d' "$2").*/final/z3-result.json" 2>/dev/null | head -1; }
    drift=0; counts=""
    for row in $(seq 1 20); do
      new=$(row_result "${matrix_root}" "${row}"); old=$(row_result "${baseline_root}" "${row}")
      [[ -f ${new} && -f ${old} ]] || { say "VARS row ${row}: missing z3-result.json (new=${new:-none} old=${old:-none})"; drift=1; continue; }
      # Symbolize-every-occurrence makes every configured field of every
      # occurrence a root, so a row may legitimately GAIN variables over an
      # older baseline; LOSING one is the regression.
      if diff <(vars_of "${old}") <(vars_of "${new}") | grep -q '^<'; then
        say "VARS FAIL row ${row}: symbolic variable lost vs baseline"
        diff <(vars_of "${old}") <(vars_of "${new}") | grep '^<' | sed 's/^/        /'; drift=1
      elif ! diff <(vars_of "${old}") <(vars_of "${new}") >/dev/null; then
        say "VARS note row ${row}: $(diff <(vars_of "${old}") <(vars_of "${new}") | grep -c '^>') variable(s) gained (every occurrence is a root)"
      elif ! diff <(sites_of "${old}") <(sites_of "${new}") >/dev/null; then
        say "VARS note row ${row}: same variables, different hook site ids (phase/occurrence UUIDs moved)"
      fi
      mn=$(models_of "${new}"); mo=$(models_of "${old}")
      if [[ ${mn} -lt ${mo} ]]; then say "MODELS row ${row}: ${mn} < baseline ${mo} -- fewer models is the alarming direction (README); explain before accepting"; counts="${counts} ${row}:${mn}<${mo}"
      elif [[ ${mn} -gt ${mo} ]]; then say "MODELS note row ${row}: ${mn} > baseline ${mo} (not a regression per README)"; fi
    done
    [[ ${drift} -eq 0 ]] && say "symbolic variables: identical to baseline on all 20 rows" || fail=1
    [[ -n ${counts} ]] && { say "MODELS: rows below baseline:${counts}"; fail=1; }
  fi
  # Wave-3 acceptance (symbolize-every-occurrence): every value a matrix row
  # reads is propagated, so the fail-open read rule must never fire here.
  # A non-empty freeSymbols on the matrix is a bug in where the rule was
  # placed, not a property of the workload.  Before wave 3 the member does
  # not exist and the check is skipped.
  free_total=0; free_rows=""
  for row in $(seq 1 20); do
    m=$(find "${matrix_root}" -maxdepth 3 -path "*/scenario-$(printf '%02d' "${row}").*/final/candidate_composition_manifest.json" 2>/dev/null | head -1)
    [[ -f ${m} ]] || continue
    n=$(jq '(.freeSymbols // []) | length' "${m}" 2>/dev/null || echo 0)
    if [[ ${n} -gt 0 ]]; then free_total=$(( free_total + n )); free_rows="${free_rows} ${row}:${n}"; fi
  done
  if [[ ${free_total} -gt 0 ]]; then say "FREE-SYMBOLS FAIL: ${free_total} free symbols on rows${free_rows} (matrix reads must all be propagated)"; fail=1
  elif jq -e 'has("freeSymbols")' "$(find "${matrix_root}" -maxdepth 3 -path "*/scenario-01.*/final/candidate_composition_manifest.json" | head -1)" >/dev/null 2>&1; then say "free symbols: none on any row"
  fi
fi

# Cheap drift checks against recorded artifacts: recompose every row's
# candidate.smt2 from its real inputs (~30 s) and replay every real path-flip
# query through the solver (~3 min).  They catch composer/solver drift without
# a matrix run -- but note they exercise only the expression families the
# matrix contains (no string ops, no boxed primitives); HDFS-11741 covers those.
# Likewise the matrix has NO argument-propagation dataflow rows and no
# configuredSourcePhaseObservations rows: static-analyzer propagation walks
# need the HDFS-11741 SEED differential, the observation ledger needs HDFS-11741.
if [[ -n ${replay_root} ]]; then
  if experiments/shrink/recompose-matrix.sh "${replay_root}" 2>&1 | tail -1 | tee /dev/stderr | grep -q "^RECOMPOSE 20/20"; then say "recompose: 20/20 identical"; else say "RECOMPOSE FAIL"; fail=1; fi
  if experiments/shrink/replay-flips.sh "${replay_root}" 2>&1 | tail -1 | tee /dev/stderr | grep -qE "^FLIPS ([0-9]+)/\1 identical"; then say "replay-flips: all identical"; else say "REPLAY-FLIPS FAIL"; fail=1; fi
fi

if [[ ${fail} -eq 0 ]]; then say "VERDICT: PASS"; else say "VERDICT: FAIL"; fi
exit ${fail}

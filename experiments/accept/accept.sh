#!/usr/bin/env bash
set -uo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)

ACCEPT_ALL_CASES=(hdfs-17899-bug3 hdfs-17899-bug2 hdfs-17899-bug1 \
                  hdfs-17967-pathA hdfs-17967-pathB hdfs-17967-pathC \
                  hdfs-17960 hdfs-17897 hdfs-11741)
ACCEPT_JAR_NAME=GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar
# shellcheck source=../../tools/lib/gc-env.sh
source "$here/../../tools/lib/gc-env.sh"
ACCEPT_Z3=${Z3_BIN}
ACCEPT_Z3_TIMEOUT=${Z3_TIMEOUT_SECONDS:-600}
ACCEPT_MIN_FREE_GB=${MIN_FREE_GB:-6}
ACCEPT_DISK_WAIT_S=${DISK_WAIT_SECONDS:-1800}
ACCEPT_CASE_CAP_MB=${CASE_CAP_MB:-300}
ACCEPT_PRUNE=${PRUNE:-0}

SELF_REPO=$(cd "$here/../.." && pwd -P)
DRY=${DRY:-0}
if [[ -n "${JAR:-}" ]]; then
  REPO=$(cd "$(dirname "$(dirname "$JAR")")" 2>/dev/null && pwd -P || echo "")
else
  REPO=$SELF_REPO
  JAR=$REPO/target/$ACCEPT_JAR_NAME
fi
IMG=${CAUSYNTH_CUSTOM_JDK_HOME:-}
ACCEPT_LIB="$REPO/experiments/lib"
OUT=${OUT:-$SELF_REPO/target/accept}
read -r -a CASE_LIST <<<"${CASES-${ACCEPT_ALL_CASES[*]}}"
CASE_TIMEOUT=${CASE_TIMEOUT_SECONDS:-21600}
SKIP_BUILD=${SKIP_BUILD:-0}

acc_log() { printf '%s %s\n' "$(date +%H:%M:%S)" "$*"; }
acc_free_gb() {
  local at=$OUT probe=""
  until [[ -d "$at" ]]; do at=$(dirname "$at"); done
  if ! probe=$(mktemp -p "$at" .accept-disk-probe.XXXXXX 2>/dev/null) \
      || ! head -c 1048576 /dev/zero 2>/dev/null >"$probe"; then
    rm -f -- "$probe"
    echo 0
    return
  fi
  rm -f -- "$probe"
  df --output=avail -BG "$at" | tail -1 | tr -dc 0-9
}
acc_dir_mb() { du -sm "$1" 2>/dev/null | cut -f1; }

# shellcheck source=../lib/case-id.sh
source "$here/../lib/case-id.sh"
acc_case() {
  case_dir_of "$REPO" "$1" || echo "$REPO/experiments/none/$1 -"
}
acc_case_dir() {
  local root=$1 c=$2 d
  for d in "$root/out/$c" "$root/$c"; do
    [[ -d "$d/schedule/final" ]] && { echo "$d"; return 0; }
  done
  echo "$root/out/$c"
}

acc_await_disk() {
  local need=$1 waited=0 free
  while :; do
    free=$(acc_free_gb)
    (( free >= need )) && { echo "$free"; return 0; }
    (( waited >= ACCEPT_DISK_WAIT_S )) && { echo "$free"; return 1; }
    acc_log "WAIT disk: ${free}G free, need ${need}G (waited ${waited}s)"
    sleep 60; waited=$((waited+60))
  done
}

acc_build_jar() {
  [[ "$SKIP_BUILD" == 1 ]] && { acc_log "SKIP_BUILD=1: using $JAR"; return 0; }
  acc_log "building $ACCEPT_JAR_NAME in $REPO"
  ( cd "$REPO" && nice -n 10 mvn -q -o -DskipTests package ) \
    >"$OUT/logs/mvn-package.log" 2>&1
  local rc=$?
  (( rc == 0 )) || acc_log "BUILD FAILED rc=$rc; see $OUT/logs/mvn-package.log"
  return $rc
}

acc_run_case() {  # acc_run_case <case-id>
  local case_id=$1 dir="" arg=""
  read -r dir arg < <(acc_case "$case_id")
  [[ "$arg" != - ]] || arg=""
  local out="$OUT/out/$case_id"
  local log="$OUT/logs/$case_id.log" rc

  rm -rf -- "$out"
  mkdir -p "$out"
  {
    echo "### repo=$REPO"
    echo "### experiment=$dir"
    echo "### case_arg=${arg:-<none>}"
    echo "### CAUSYNTH_OUTPUT_DIR=$out"
    echo "### CAUSYNTH_CUSTOM_JDK_HOME=$IMG"
    echo "### ---- validate ----"
  } >"$log"
  (
    cd "$dir" || exit 97
    export CAUSYNTH_OUTPUT_DIR="$out" CAUSYNTH_CUSTOM_JDK_HOME="$IMG"
    bash "$ACCEPT_LIB/run.sh" "$dir" "$arg" validate
  ) >>"$log" 2>&1
  rc=$?
  if (( rc == 0 )); then
    echo "### ---- campaign ----" >>"$log"
    (
      cd "$dir" || exit 97
      export CAUSYNTH_OUTPUT_DIR="$out" CAUSYNTH_CUSTOM_JDK_HOME="$IMG" \
        CAUSYNTH_CAMPAIGN_BUDGET_S=$(( CASE_TIMEOUT - SECONDS ))
      bash "$ACCEPT_LIB/run.sh" "$dir" "$arg" campaign
    ) >>"$log" 2>&1
    rc=$?
  else
    echo "### validate failed (rc=$rc); campaign not started" >>"$log"
  fi
  return $rc
}

ACCEPT_KEEP_GLOBS=(
  'schedule/final/result.json'
  'schedule/final/candidate.smt2'
  'schedule/final/candidate_composition_manifest.json'
  'schedule/final/gaps.json'
  'schedule/final/run-manifest.json'
  'schedule/final/compose.log'
  'schedule/final/reproduce.json'
  'schedule/final/fallback.json'
  'schedule/stage_metrics.tsv'
  'schedule/iteration-*/iteration_manifest.json'
  'static_scope_map.jsonl'
  'schedule/iteration-*/execution_task_plan.jsonl'
  'schedule/iteration-*/runtime_workflow_schedule_index.json'
  'schedule/iteration-*/sessions/*/*.jsonl.gz'
  'schedule/iteration-*/sessions/*/manifest.json'
  'schedule/iteration-*/session_census.jsonl'
  'schedule/iteration-*/slots.jsonl.gz'
  'schedule/iteration-*/obligations-*/slots.jsonl.gz'
  'schedule/iteration-*/planner.log'
  'schedule/iteration-*/obligation_results.jsonl'
  'schedule/iteration-*/campaign_gaps.jsonl'
  'schedule/iteration-*/obligations-*/obligations.jsonl'
  'schedule/iteration-*/obligations-*/growth.jsonl'
  'schedule/iteration-*/obligations-*/grown_plan.jsonl'
  'schedule/iteration-*/obligations-*/tasks.jsonl.gz'
  'schedule/iteration-*/obligations-*/gaps.jsonl.gz'
  'schedule/iteration-*/obligations-*/*/obligation_result.jsonl'
  'schedule/iteration-*/obligations-*/stdout.log'
  'schedule/iteration-*/obligations-*/stderr.log'
  'schedule/iteration-*/obligations-*/*/stdout.log'
  'schedule/iteration-*/obligations-*/*/stderr.log'
  'schedule/iteration-*/obligations-*/*/replay-stdout.log'
  'schedule/iteration-*/obligations-*/*/replay-stderr.log'
  'schedule/iteration-*/obligations-*/*/alone-stderr.log'
  'schedule/iteration-*/obligations-*/*/hard-stderr.log'
  'schedule/iteration-*/obligations-*/*/obligation_result.first.jsonl'
  'schedule/iteration-*/obligations-*/*/host.txt'
  'schedule/iteration-*/obligations-*/*/replay-host.txt'
  'schedule/iteration-*/obligations-*/*/alone-host.txt'
  'schedule/iteration-*/obligations-*/*/hard-host.txt'
  'schedule/iteration-*/obligations-*/explore_manifest.json'
)

acc_prune_case() {
  local dir=$1 keep before after f rel
  [[ -d "$dir" ]] || return 0
  if [[ "$ACCEPT_PRUNE" != 1 ]]; then
    acc_log "PRUNE $(basename "$dir"): skipped (PRUNE=0), $(acc_dir_mb "$dir")M"
    return 0
  fi
  before=$(acc_dir_mb "$dir")
  keep=$(mktemp) || return 0
  for rel in "${ACCEPT_KEEP_GLOBS[@]}"; do
    for f in "$dir"/$rel; do
      [[ -f "$f" ]] && printf '%s\n' "$f" >>"$keep"
    done
  done
  find "$dir" -type f \( -name '*telemetry*' -o -name 'replay.log' \
      -o -name 'stage_metrics.tsv' -o -name 'execution_task_plan.jsonl' \) \
      -print >>"$keep" 2>/dev/null
  while IFS= read -r -d '' f; do
    grep -qxF "$f" "$keep" || rm -f -- "$f"
  done < <(find "$dir" -type f -print0 2>/dev/null)
  rm -f "$keep"
  find "$dir" -type d -empty -delete 2>/dev/null
  after=$(acc_dir_mb "$dir")
  acc_log "PRUNE $(basename "$dir"): ${before}M -> ${after}M (cap ${ACCEPT_CASE_CAP_MB}M)"
  (( ${after:-0} > ACCEPT_CASE_CAP_MB )) && acc_log "WARN $(basename "$dir") over cap"
  return 0
}

if [[ "${1:-}" == "--run-case" ]]; then
  [[ -n "$IMG" ]] || { echo "CAUSYNTH_CUSTOM_JDK_HOME is unset" >&2; exit 2; }
  acc_run_case "${2:?usage: accept.sh --run-case <case-id>}"
  exit $?
fi

if [[ "$DRY" != 1 && "${ACCEPT_SESSION:-0}" != 1 ]]; then
  export ACCEPT_SESSION=1
  exec setsid bash "$0" "$@"
fi

acc_log "GraphChecker acceptance harness"
acc_log "  repo  $REPO"
acc_log "  jar   $JAR"
acc_log "  image ${IMG:-(unset)}"
acc_log "  out   $OUT"
acc_log "  cases ${CASE_LIST[*]:-(none)}"
acc_log "  per-case budget ${CASE_TIMEOUT}s, prune=$ACCEPT_PRUNE"

fail=0
check() { # check <label> <ok|no> <detail>
  if [[ "$2" == ok ]]; then printf '  OK    %-26s %s\n' "$1" "$3"
  else printf '  FAIL  %-26s %s\n' "$1" "$3"; fail=$((fail+1)); fi
}
echo "== preflight"
if [[ -z "$IMG" ]]; then
  check "vm image" no "CAUSYNTH_CUSTOM_JDK_HOME is unset: every case's execute.sh requires it and this harness will not guess an image"
elif [[ -x "$IMG/bin/java" ]]; then
  check "vm image" ok "$("$IMG/bin/java" -Xinternalversion 2>&1 | head -1 | cut -c1-70)"
else
  check "vm image" no "no executable at $IMG/bin/java"
fi
if [[ "$SKIP_BUILD" == 1 ]]; then
  [[ -s "$JAR" ]] && check jar ok "$(stat -c %s "$JAR") bytes (SKIP_BUILD=1)" \
                  || check jar no "missing, and SKIP_BUILD=1: $JAR"
else
  check jar ok "$JAR (built by this run)"
fi
[[ -n "$REPO" && -x "$REPO/run_engine.sh" && -d "$REPO/experiments/lib" ]] \
  && check "repo root" ok "$REPO ($(git -C "$REPO" rev-parse --short HEAD 2>/dev/null || echo 'not a git tree'))" \
  || check "repo root" no "no run_engine.sh and experiments/lib under '$REPO'"
[[ "$JAR" == "$REPO/target/$ACCEPT_JAR_NAME" ]] \
  && check "jar in repo" ok "the campaigns run out of the jar's own tree" \
  || check "jar in repo" no "$JAR is not $REPO/target/$ACCEPT_JAR_NAME"
command -v "$ACCEPT_Z3" >/dev/null \
  && check z3 ok "$("$ACCEPT_Z3" --version 2>&1 | head -1)" \
  || check z3 no "not on PATH: $ACCEPT_Z3"
for tool in jq python3 setsid timeout mvn; do
  command -v "$tool" >/dev/null && check "$tool" ok "$(command -v "$tool")" \
                                || check "$tool" no "not on PATH"
done
for c in "${CASE_LIST[@]}"; do
  read -r d arg < <(acc_case "$c")
  [[ "$arg" != - ]] || arg=""
  [[ -f "$d/case.sh" && -f "$d/workflow.properties" ]] \
    && check "experiment $c" ok "lib/run.sh $d $arg campaign" \
    || check "experiment $c" no "no case.sh + workflow.properties at $d"
done
free=$(acc_free_gb)
(( free >= ACCEPT_MIN_FREE_GB )) \
  && check disk ok "${free}G free where $OUT is written (need ${ACCEPT_MIN_FREE_GB}G)" \
  || check disk no "${free}G free where $OUT is written, need ${ACCEPT_MIN_FREE_GB}G (0: a 1 MB write there was refused, the disk or a quota is full)"

echo
echo "== commands per case"
for c in "${CASE_LIST[@]}"; do
  read -r d arg < <(acc_case "$c")
  [[ "$arg" != - ]] || arg=""
  cat <<CMD
  --- $c
  (d=$d; \\
     export CAUSYNTH_OUTPUT_DIR=$OUT/out/$c CAUSYNTH_CUSTOM_JDK_HOME=$IMG; \\
     bash $ACCEPT_LIB/run.sh \$d "$arg" validate && \\
     bash $ACCEPT_LIB/run.sh \$d "$arg" campaign)
  bash $here/probe.sh $c $(acc_case_dir "$OUT" "$c") $OUT/report/$c
  python3 $here/cone.py $c $(acc_case_dir "$OUT" "$c") $OUT/report/$c
  python3 $here/report.py $c $(acc_case_dir "$OUT" "$c") $OUT/report/$c
CMD
done

if [[ "$DRY" == 1 ]]; then
  echo
  echo "== dry run: nothing was executed; preflight failures: $fail"
  exit $(( fail > 0 ))
fi
(( fail > 0 )) && { acc_log "ABORT: $fail preflight failure(s)"; exit 2; }

mkdir -p "$OUT"/logs "$OUT"/out "$OUT"/report
echo $$ >"$OUT/pgid"
acc_log "process group $$ (stop the run by its OUT: tools/rounds/stop-run.sh)"
acc_build_jar || { acc_log "ABORT: build failed"; exit 2; }

TSV="$OUT/summary.tsv"
[[ -s "$TSV" ]] || printf 'case\texit\telapsed\tclaim\tfinalStatus\tblockers\tgaps\tplain\tbuggy\tother\tverdict\treason\tfinding\n' >"$TSV"

for c in "${CASE_LIST[@]}"; do
  free=$(acc_await_disk "$ACCEPT_MIN_FREE_GB") || {
    acc_log "SKIP $c: only ${free}G free where $OUT is written after waiting ${ACCEPT_DISK_WAIT_S}s"
    printf '%s\tskipped\t0\t-\t-\t-\t-\t-\t-\t-\tFAIL\tno disk\t-\n' "$c" >>"$TSV"
    continue
  }
  work="$OUT/report/$c"; mkdir -p "$work"
  acc_log "START $c (free=${free}G)"
  t0=$(date +%s)
  JAR="$JAR" OUT="$OUT" CAUSYNTH_CUSTOM_JDK_HOME="$IMG" \
    timeout "$CASE_TIMEOUT" bash "$here/accept.sh" --run-case "$c" \
    >>"$OUT/logs/$c.driver.log" 2>&1
  rc=$?
  (( rc == 124 )) && acc_log "TIMEOUT $c after ${CASE_TIMEOUT}s"
  elapsed=$(( $(date +%s)-t0 ))
  printf 'exit=%s elapsed=%ss\n' "$rc" "$elapsed" >"$work/status"
  acc_log "END $c rc=$rc elapsed=${elapsed}s (log $OUT/logs/$c.log)"

  dir=$(acc_case_dir "$OUT" "$c")
  Z3_BIN="$ACCEPT_Z3" Z3_TIMEOUT_SECONDS="$ACCEPT_Z3_TIMEOUT" \
    bash "$here/probe.sh" "$c" "$dir" "$work" >"$work/probe.log" 2>&1 \
    || acc_log "WARN $c: probe failed (see $work/probe.log)"
  python3 "$here/cone.py" "$c" "$dir" "$work" >"$work/cone.log" 2>&1 \
    || acc_log "WARN $c: causal cone failed (see $work/cone.log)"
  python3 "$here/report.py" "$c" "$dir" "$work" \
    || acc_log "WARN $c: report failed"
  [[ -s "$work/row.tsv" ]] && cat "$work/row.tsv" >>"$TSV"

  acc_prune_case "$dir"
  acc_log "after $c: free=$(acc_free_gb)G"
done

echo
echo "== summary"
column -t -s $'\t' "$TSV" 2>/dev/null || cat "$TSV"
acc_log "acceptance finished; reports under $OUT/report/<case>/report.md"

#!/usr/bin/env bash
# accept.sh -- the acceptance run: one case at a time, each campaign followed by
# the plain z3 probe and a readable report.
#
#   DRY=1 bash accept.sh        validate everything, run nothing
#   bash accept.sh              run it (re-execs itself under setsid)
#
# Nothing here decides what a case proved.  The campaign publishes
# schedule/final/result.json, report.py reads the claim out of it and compares
# the mechanism against this case's expected one; cone.py checks in the
# published formula that the witness's moved roots are causes of its fatal;
# probe.sh asks z3 about the published formula and is reported beside the
# verdict, never gating it.
#
# Environment (every path is an argument or an env var; none is baked in)
#   CAUSYNTH_CUSTOM_JDK_HOME  REQUIRED -- the concolic VM image.  Unset, this
#              script refuses by name rather than guessing an image: every
#              case's execute.sh reads exactly this variable.
#   JAR        the jar under test.  Default: <repo>/target/GraphChecker-1.0-
#              SNAPSHOT-jar-with-dependencies.jar, where <repo> is the
#              GraphChecker tree THIS script is committed in.  Setting JAR
#              moves the whole run to that jar's own repo (the jar's
#              grandparent): run_engine.sh resolves graphchecker_jar relative
#              to the tree it lives in, so the jar and the tree cannot be
#              chosen separately without the harness lying about what ran.
#   OUT        output root.  Default: <repo>/target/accept (target/ is
#              .gitignore'd, so a run leaves the work tree clean).
#   CASES      space-separated case ids.  Default: all nine.
#   CASE_TIMEOUT_SECONDS  per-case wall budget, default 21600 (6 h).  A
#              runaway guard, not a schedule: hdfs-17899-bug1 takes ~1.8 h.
#   SKIP_BUILD=1          use the jar already in <repo>/target, run no mvn
#   Z3_BIN / Z3_TIMEOUT_SECONDS   default z3 (from PATH) and 600
#   MIN_FREE_GB / DISK_WAIT_SECONDS   default 6 G and 1800 s, free on the
#              filesystem OUT is written to (acc_free_gb)
#   PRUNE=1 / CASE_CAP_MB DELETES every file of a finished case that is not
#              named in ACCEPT_KEEP_GLOBS below.  Off by default: what a case
#              publishes moves with the pipeline, and a keep list that has
#              fallen behind deletes the evidence of exactly the stage under
#              test.  Turn it on for a long campaign on a small disk, after
#              reading that list against the run you are pruning.
#
# Cases run one at a time.  A campaign already runs concolic_worker_count
# workers of its own, and the standing ruling is at most two campaign lanes on
# this host; a second lane is a second invocation of this script, not a knob.
#
# Process discipline: the run re-execs under setsid, so no signal meant for
# another run reaches this one; its group id is written to $OUT/pgid.  It is
# not the whole run -- a case runs under `timeout`, which takes a group of its
# own, and the engine gives each replay and remote worker one too -- so a run
# is stopped by its output directory (tools/rounds/stop-run.sh).  Nothing is
# ever killed by this script.
set -uo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)

ACCEPT_ALL_CASES=(hdfs-17899-bug3 hdfs-17899-bug2 hdfs-17899-bug1 \
                  hdfs-17967-pathA hdfs-17967-pathB hdfs-17967-pathC \
                  hdfs-17960 hdfs-17897 hdfs-11741)
ACCEPT_JAR_NAME=GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar
ACCEPT_Z3=${Z3_BIN:-z3}
ACCEPT_Z3_TIMEOUT=${Z3_TIMEOUT_SECONDS:-600}
ACCEPT_MIN_FREE_GB=${MIN_FREE_GB:-6}
ACCEPT_DISK_WAIT_S=${DISK_WAIT_SECONDS:-1800}
ACCEPT_CASE_CAP_MB=${CASE_CAP_MB:-300}
ACCEPT_PRUNE=${PRUNE:-0}

# This file lives at <repo>/experiments/accept/accept.sh.
SELF_REPO=$(cd "$here/../.." && pwd -P)
DRY=${DRY:-0}
if [[ -n "${JAR:-}" ]]; then
  REPO=$(cd "$(dirname "$(dirname "$JAR")")" 2>/dev/null && pwd -P || echo "")
else
  REPO=$SELF_REPO
  JAR=$REPO/target/$ACCEPT_JAR_NAME
fi
IMG=${CAUSYNTH_CUSTOM_JDK_HOME:-}
# Every case runs through the one launcher; a case directory is declarations.
ACCEPT_LIB="$REPO/experiments/lib"
OUT=${OUT:-$SELF_REPO/target/accept}
read -r -a CASE_LIST <<<"${CASES-${ACCEPT_ALL_CASES[*]}}"
CASE_TIMEOUT=${CASE_TIMEOUT_SECONDS:-21600}
SKIP_BUILD=${SKIP_BUILD:-0}

acc_log() { printf '%s %s\n' "$(date +%H:%M:%S)" "$*"; }
# The G free where the run writes: OUT's filesystem, or before the run makes
# OUT its nearest existing parent's (h4 wrote to a home `df /` never saw).  A
# 1 MB write there must succeed first, and a refused one is 0 G: a per-user
# quota on an NFS export is not in df's numbers (h4 lost three cases to
# "Disk quota exceeded" with the pool 32 T free).
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

# The experiment a case id lives in, under any system's directory: the
# longest "-"-prefix of the id that names one (hdfs-17899-bug1 lives in
# hadoop/hdfs-17899, adhoc-recv-seqno.mirror in hadoop/adhoc, solr-18413 in
# solr/solr-18413), as <system>/<experiment>.
acc_experiment_of() {
  local exp=$1 d
  while :; do
    for d in "$REPO"/experiments/*/"$exp"; do
      [[ -f "$d/case.sh" ]] && { echo "${d#"$REPO"/experiments/}"; return 0; }
    done
    [[ "$exp" == *-* ]] || break
    exp=${exp%-*}
  done
  echo "none/$1"
}
# The case id's rest after its experiment directory: the run.sh argument.
acc_case_arg_of() {
  local exp; exp=$(basename "$(acc_experiment_of "$1")")
  [[ "$exp" == "$1" ]] && echo "" || echo "${1#"$exp"-}"
}
acc_case_dir() {
  local root=$1 c=$2 d
  for d in "$root/out/$c" "$root/$c"; do
    [[ -d "$d/schedule/final" ]] && { echo "$d"; return 0; }
  done
  echo "$root/out/$c"
}

# Wait for headroom rather than racing another lane for it.
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

# ---------------------------------------------------------------------------
# One case, out of the experiment's own machinery
# ---------------------------------------------------------------------------
acc_build_jar() {
  [[ "$SKIP_BUILD" == 1 ]] && { acc_log "SKIP_BUILD=1: using $JAR"; return 0; }
  acc_log "building $ACCEPT_JAR_NAME in $REPO"
  ( cd "$REPO" && nice -n 10 mvn -q -o -DskipTests package ) \
    >"$OUT/logs/mvn-package.log" 2>&1
  local rc=$?
  (( rc == 0 )) || acc_log "BUILD FAILED rc=$rc; see $OUT/logs/mvn-package.log"
  return $rc
}

# The case directory holds declarations; experiments/lib/run.sh turns
# them into the campaign's environment and runs run_engine.sh with the case's
# workflow.properties.  This function starts that and states the two things a
# harness run must not inherit -- a fresh output directory and the VM image --
# and nothing else.
acc_run_case() {  # acc_run_case <case-id>
  local case_id=$1
  local exp; exp=$(acc_experiment_of "$case_id")
  local arg; arg=$(acc_case_arg_of "$case_id")
  local dir="$REPO/experiments/$exp"
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
      export CAUSYNTH_OUTPUT_DIR="$out" CAUSYNTH_CUSTOM_JDK_HOME="$IMG"
      bash "$ACCEPT_LIB/run.sh" "$dir" "$arg" campaign
    ) >>"$log" 2>&1
    rc=$?
  else
    echo "### validate failed (rc=$rc); campaign not started" >>"$log"
  fi
  return $rc
}

# ---------------------------------------------------------------------------
# Optional pruning
# ---------------------------------------------------------------------------
# Everything a later reading of a finished case needs, as globs relative to
# the case directory.  A name here is one the pipeline writes: read the list
# against the run you are pruning before you set PRUNE=1, because a name the
# pipeline has moved on from is the evidence this harness exists to read.
ACCEPT_KEEP_GLOBS=(
  'schedule/final/result.json'
  'schedule/final/candidate.smt2'
  'schedule/final/candidate_composition_manifest.json'
  'schedule/final/gaps.json'
  'schedule/final/run-manifest.json'
  'schedule/final/compose.log'
  'schedule/final/reproduce.json'
  'schedule/stage_metrics.tsv'
  'schedule/iteration-*/iteration_manifest.json'
  'static_scope_map.jsonl'
  'schedule/iteration-*/execution_task_plan.jsonl'
  'schedule/iteration-*/runtime_workflow_schedule_index.json'
  'schedule/iteration-*/sessions/*/*.jsonl'
  'schedule/iteration-*/sessions/*/manifest.json'
  'schedule/iteration-*/session_census.jsonl'
  'schedule/iteration-*/slots.jsonl'
  'schedule/iteration-*/obligation_results.jsonl'
  'schedule/iteration-*/campaign_gaps.jsonl'
  'schedule/iteration-*/obligations-*/obligations.jsonl'
  'schedule/iteration-*/obligations-*/growth.jsonl'
  'schedule/iteration-*/obligations-*/exposed_region_plan.jsonl'
  'schedule/iteration-*/obligations-*/tasks.jsonl'
  'schedule/iteration-*/obligations-*/gaps.jsonl'
  'schedule/iteration-*/obligations-*/*/obligation_result.jsonl'
  'schedule/iteration-*/obligations-*/stdout.log'
  'schedule/iteration-*/obligations-*/stderr.log'
  'schedule/iteration-*/obligations-*/*/stdout.log'
  'schedule/iteration-*/obligations-*/*/stderr.log'
)
# An ad-hoc batch case (run_engine.sh, causynth_static_root) keeps the same
# of each of its targets' campaigns, targets/<name>/, their logs, what its
# one recording said of each target, and its seed replays' groups and logs.
ACCEPT_KEEP_GLOBS+=("${ACCEPT_KEEP_GLOBS[@]/#/targets/*/}"
  'targets/*/campaign.log' 'runtime/record-summary.json'
  'schedule/groups/groups.json' 'schedule/groups/group-*.log')

acc_prune_case() {
  local dir=$1 keep before after f rel
  [[ -d "$dir" ]] || return 0
  if [[ "$ACCEPT_PRUNE" != 1 ]]; then
    acc_log "PRUNE $(basename "$dir"): skipped (PRUNE=0), $(acc_dir_mb "$dir")M"
    return 0
  fi
  before=$(acc_dir_mb "$dir")
  keep=$(mktemp) || return 0
  # A pattern that matches nothing stays literal and the -f test rejects it,
  # so no shell option is touched on the caller's behalf.
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

# ---------------------------------------------------------------------------
# Internal entry point
# ---------------------------------------------------------------------------
# `accept.sh --run-case <case-id>` runs exactly one case's validate+campaign
# and exits with its code.  The main loop below calls it this way because
# `timeout` needs a process of its own, and because a case must not be able to
# take the harness's own shell down with it.  The loop passes the resolved
# JAR, OUT and VM image in the environment, so the child derives the same
# repo, output root and image as its parent and guesses nothing.
if [[ "${1:-}" == "--run-case" ]]; then
  [[ -n "$IMG" ]] || { echo "CAUSYNTH_CUSTOM_JDK_HOME is unset" >&2; exit 2; }
  acc_run_case "${2:?usage: accept.sh --run-case <case-id>}"
  exit $?
fi

# One session of our own, so every child is in one group we may signal and no
# other lane's campaign ever is.
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

# ---- preflight ------------------------------------------------------------
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
  d="$REPO/experiments/$(acc_experiment_of "$c")"
  [[ -f "$d/case.sh" && -f "$d/workflow.properties" ]] \
    && check "experiment $c" ok "lib/run.sh $d $(acc_case_arg_of "$c") campaign" \
    || check "experiment $c" no "no case.sh + workflow.properties at $d"
done
free=$(acc_free_gb)
(( free >= ACCEPT_MIN_FREE_GB )) \
  && check disk ok "${free}G free where $OUT is written (need ${ACCEPT_MIN_FREE_GB}G)" \
  || check disk no "${free}G free where $OUT is written, need ${ACCEPT_MIN_FREE_GB}G (0: a 1 MB write there was refused, the disk or a quota is full)"

echo
echo "== commands per case"
for c in "${CASE_LIST[@]}"; do
  cat <<CMD
  --- $c
  (d=$REPO/experiments/$(acc_experiment_of "$c"); \\
     export CAUSYNTH_OUTPUT_DIR=$OUT/out/$c CAUSYNTH_CUSTOM_JDK_HOME=$IMG; \\
     bash $ACCEPT_LIB/run.sh \$d "$(acc_case_arg_of "$c")" validate && \\
     bash $ACCEPT_LIB/run.sh \$d "$(acc_case_arg_of "$c")" campaign)
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

# ---- run ------------------------------------------------------------------
mkdir -p "$OUT"/logs "$OUT"/out "$OUT"/report
echo $$ >"$OUT/pgid"
acc_log "process group $$ (stop the run by its OUT: tools/rounds/stop-run.sh)"
acc_build_jar || { acc_log "ABORT: build failed"; exit 2; }

TSV="$OUT/summary.tsv"
# Header once, rows appended: cases are run one at a time into the same OUT, so
# rewriting the header on every invocation would drop every row an earlier
# invocation wrote.
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

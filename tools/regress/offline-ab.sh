#!/usr/bin/env bash
# offline-ab.sh -- the offline regression gate: does a candidate jar compute
# anything different from a baseline jar on recorded HDFS campaigns?
#
#   tools/regress/offline-ab.sh [--round TAG|DIR]... <baseline-jar> <candidate-jar> [case...]
#
# No workload and no concolic replay runs.  Every stage below is a pure
# function of what a campaign recorded, run once per jar with the arguments
# run_engine.sh passes it (the function named beside it), and the two sides'
# outputs are compared by tools/regress/ab_compare.py:
#
#   chain     stage       mirrors                       reads
#   SEED      SEED.static do_analyze (static pass),     the case's scope, copied again from its tree,
#                         after the door step of        and the library doors' classes it calls
#                         campaign_analyze_grown_scope
#             SEED.trace  do_workload's aggregation     the recording's runtime/ + one set of static
#                                                       artifacts for both sides (ab_seed)
#             PLAN        do_schedule                   this side's SEED.trace plan
#             EXPLORE.0   campaign_explore, wave 0      the seed session + this side's PLAN
#             SOLVE.0     campaign_obligation_worker's  each EXPLORE.0 obligation (z3), no replay
#                         solver
#   IMPORT    IMPORT      campaign_import_gate          the recorded final corpus
#   EXPLORE.N EXPLORE.N   campaign_explore, last wave   the recorded final corpus, verdicts, slots
#   COMPOSE   COMPOSE     do_compose (+SOLVE, DECIDE)   the recorded final corpus (z3)
#             CONFIRM     campaign_confirm's ConfirmMain this side's COMPOSE claim, no replay
#
# The recorded runs are the rounds named (--round, first holding a case
# wins): a TAG is ${AB_ACCEPT_ROOT}/accept-<TAG>-<case without hdfs->, as
# tools/rounds writes them; a DIR is an accept.sh output (DIR/out/<case>).
# The default, "v94 v93 v92", is the accepted 9/9.  A round of a build whose
# row contract has moved on is read as the current engine reads it: main
# (2026-09-29) refuses every v92-v94 corpus row (IMPORT, COMPOSE) and their
# static artifacts, so give the gate a round produced by a current build.
#
# A stage that reads an iteration reads a private one: the recorded sessions
# and obligation waves linked, the files a stage rewrites (slots.jsonl)
# copied, so nothing under a recorded run is ever written.  Both jars are
# copied into the output first (a rebuild under a running gate changes
# nothing) and run under THIS checkout's case declarations and harness
# (experiments/): the jar is the one variable -- unless AB_BASELINE_REPO
# gives the baseline its own checkout's, for a change that moves a
# declaration's format together with the jar (a target spec).  The workload
# classpath is the one the run froze when it states one (its tree's report
# may be gone).
#
# Each case is one task, both sides inside it, placed by
# /bigtemp/vnr3ne/bin/onlift.sh on the lift with the most free memory for
# its load (a case peaks at four JVMs, under 3.2 GB each); the cases start
# AB_STAGGER_S apart so each placement sees the last one.
#
# Prints one table (case | stage | identical/DIFFERS/ERROR | baseline vs the
# recorded artifact | wall | summary) and writes it to $AB_OUT/report.tsv,
# the differing files' diffs to $AB_OUT/diffs/.  Exit 0: every gating stage
# identical; 1: one differs; 2: none differs but one could not be checked
# (it failed or timed out on the baseline too, lacked a recorded input, or
# never ran).
#
# Environment
#   AB_OUT        output root (default /bigtemp/vnr3ne/ab/<timestamp>), on a
#                 filesystem every lift shares
#   AB_HOSTS      "local": every case here, no onlift.sh (default: onlift.sh)
#   AB_CASE_GB    free memory a lift needs to take a case (default 14)
#   AB_STAGGER_S  seconds between two cases' placements (default 8)
#   AB_HEAP_MB    engine JVM heap cap (default 8192; a case's engine_memory_mb
#                 above it is lowered to it)
#   AB_SOLVE_JOBS concurrent SOLVE.0 solvers of one side (default 2)
#   AB_STAGE_TIMEOUT_S  wall bound of one JVM (default 1800)
#   AB_STAGES     the chains to run (default "SEED IMPORT EXPLORE.N COMPOSE")
#   AB_ACCEPT_ROOT  where round TAGs live (default $GC_OUT, tools/lib/gc-env.sh)
#   AB_Z3         the z3 both sides use (default: the case's z3_bin)
#   AB_BASELINE_REPO  the checkout whose experiments/ declare the baseline's
#                 cases (default: this one)
set -uo pipefail

ab_self=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)/$(basename "${BASH_SOURCE[0]}")
ab_self_repo=$(cd "$(dirname "${ab_self}")/../.." && pwd -P)
# shellcheck source=../lib/gc-env.sh
source "${ab_self_repo}/tools/lib/gc-env.sh"

AB_CASES=(hdfs-17899-bug1 hdfs-17899-bug2 hdfs-17899-bug3 hdfs-17967-pathA
  hdfs-17967-pathB hdfs-17967-pathC hdfs-17960 hdfs-17897 hdfs-11741)
AB_DEFAULT_ROUNDS=(v94 v93 v92)
AB_CHAINS=(SEED IMPORT EXPLORE.N COMPOSE)
AB_SIDES=(baseline candidate)

ab_log() { printf '%s %s\n' "$(date +%H:%M:%S)" "$*" >&2; }
ab_die() { ab_log "offline-ab: $*"; exit 2; }

# ---------------------------------------------------------------------------
# One case, both sides (run here or on a lift)
# ---------------------------------------------------------------------------

# The value of one key of this side's normalized workflow config.
ab_cfg() {
  sed -n "s/^$1=//p" "${ab_case_dir}/config.txt" | head -n 1
}

# The smaller of a case's stated heap (empty: the launcher's 8 GB) and the cap.
ab_heap() {
  local stated=${1:-8192}
  (( stated < AB_HEAP_MB )) && echo "${stated}" || echo "${AB_HEAP_MB}"
}

# ab_java <stage-dir> <heap-mb> <classpath> <main> [args...]: one engine JVM
# through the case's java_bin as run_java_main starts it (the loop bound;
# then ab_props), in the stage directory, bounded; its exit, wall time and
# peak RSS go to <stage-dir>/status.
ab_props=()
ab_java() {
  local dir=$1 heap=$2 cp=$3 main=$4 code=0 wall rss
  shift 4
  ( cd "${dir}" && GRAPH_CHECKER_ENGINE_MEMORY_MB=${heap} \
      timeout -k 30 "${AB_STAGE_TIMEOUT_S}" \
      /usr/bin/time -f '%e %M' -o "${dir}/time.txt" \
      "${ab_java_bin}" "-Dcausynth.loop.default.bound=${ab_loop_bound}" \
      "${ab_props[@]}" -cp "${cp}" "${main}" "$@" ) \
    >"${dir}/stdout.log" 2>"${dir}/stderr.log" || code=$?
  read -r wall rss < <(tail -n 1 "${dir}/time.txt" 2>/dev/null) || true
  printf 'exit=%s wall_s=%s rss_mb=%s host=%s\n' "${code}" "${wall:-?}" \
    "$(( ${rss:-0} / 1024 ))" "$(hostname -s)" >"${dir}/status"
  return "${code}"
}

# A stage that did not run, and why.
ab_skip() {
  mkdir -p "$1"
  printf 'exit=skipped reason=%s host=%s\n' "$2" "$(hostname -s)" >"$1/status"
  return 1
}

# A fresh directory for one stage.
ab_stage_dir() {
  rm -rf -- "${ab_case_dir:?}/$1"
  mkdir -p "${ab_case_dir}/$1"
  printf '%s\n' "${ab_case_dir}/$1"
}

ab_ok() { [[ "$(sed -n 's/^exit=\([^ ]*\).*/\1/p' "${ab_case_dir}/$1/status" 2>/dev/null)" == 0 ]]; }

# ab_iteration <dst> full|wave0 [plan | wave left out]: a private iteration
# over the recorded one.  full: every session and obligation wave linked
# (but the one named, which the stage writes), the iteration's files
# copied.  wave0: the sessions wave 0 was planned over (its roster, or the
# whole corpus of a run that planned no wave), the recorded schedule, and
# this side's PLAN as the iteration plan; no wave, no slot table.  A wave's
# output goes inside, where the planner reads the wave before it.
ab_iteration() {
  local dst=$1 mode=$2 extra=${3:-} name file wave
  mkdir -p "${dst}"
  [[ -f "${ab_acc_it}/recorded_schedule.jsonl" ]] \
    && cp "${ab_acc_it}/recorded_schedule.jsonl" "${dst}/"
  if [[ "${mode}" == wave0 ]]; then
    mkdir -p "${dst}/sessions"
    while IFS= read -r name; do
      [[ -n "${name}" ]] || continue
      [[ -d "${ab_acc_it}/sessions/${name}" ]] || return 1
      ln -s "${ab_acc_it}/sessions/${name}" "${dst}/sessions/${name}"
    done < <(if [[ -d "${ab_acc_it}/obligations-0000" ]]; then
        cat "${ab_acc_it}/obligations-0000/sessions-before.txt"
      else
        ls "${ab_acc_it}/sessions"
      fi)
    cp "${extra}" "${dst}/execution_task_plan.jsonl"
    : >"${dst}/obligation_results.jsonl"
    return 0
  fi
  ln -s "${ab_acc_it}/sessions" "${dst}/sessions"
  for wave in "${ab_acc_it}"/obligations-*; do
    [[ -d "${wave}" && "$(basename "${wave}")" != "${extra}" ]] || continue
    ln -s "${wave}" "${dst}/$(basename "${wave}")"
  done
  for file in execution_task_plan.jsonl slots.jsonl obligation_results.jsonl; do
    [[ -f "${ab_acc_it}/${file}" ]] && cp "${ab_acc_it}/${file}" "${dst}/"
  done
  touch "${dst}/obligation_results.jsonl"
}

# The explore bounds and root domains exactly as campaign_explore passes them.
ab_explore_args() {
  local value
  ab_explore=(--target-occurrence "${ab_declared}")
  [[ -z "${ab_root_domains}" ]] || ab_explore+=(--root-domains "${ab_root_domains}")
  value=$(ab_cfg region_path_max_paths_per_region)
  [[ -z "${value}" ]] || ab_explore+=(--max-paths-per-region "${value}")
  value=$(ab_cfg region_path_max_flips_per_path)
  [[ -z "${value}" ]] || ab_explore+=(--max-flips-per-path "${value}")
  value=$(ab_cfg region_path_max_tasks)
  [[ -z "${value}" ]] || ab_explore+=(--max-tasks "${value}")
  value=$(ab_cfg region_path_max_world_depth)
  [[ -z "${value}" ]] || ab_explore+=(--max-world-depth "${value}")
  [[ -z "$(ab_cfg region_path_stop_at_fatal)" ]] || ab_explore+=(--stop-at-fatal)
}

ab_stage_seed_static() {
  local dir classes out grown growth sha
  local -a roots=()
  dir=$(ab_stage_dir SEED.static)
  classes=${dir}/classes
  out=${dir}/out
  grown=${dir}/scope-classes
  growth=$(ab_cfg causynth_scope_growth_budget)
  [[ -z "${growth}" || "${growth}" == 0 ]] \
    || ab_skip "${dir}" "scope growth (budget ${growth}) is not mirrored" || return
  # The scope, copied out of the case's tree into this stage, never into the
  # per-host directory a running campaign of the case weaves from.
  (cd "${ab_case_decl}" && env CAUSYNTH_ANALYSIS_CLASSES_DIR="${classes}" \
      bash "${ab_side_repo}/experiments/lib/prepare-analysis.sh" \
      "${ab_case_decl}" "${ab_case_arg}") >"${dir}/prepare.log" 2>&1 \
    || ab_skip "${dir}" "the scope copy failed (prepare.log)" || return
  # campaign_kind_digest tree: whether the tree still holds the classes the
  # recording was seeded from (the base~acc column reads it).
  sha=$(cd "${classes}" && find . -type f -print0 | LC_ALL=C sort -z \
    | xargs -0 -r sha256sum | sha256sum | awk '{print $1}')
  printf '%s\n' "${sha}" >"${dir}/classes.sha256"
  mkdir -p "${out}" "${grown}"
  # campaign_analyze_grown_scope's door step, outside the budget: the class
  # families of the library catalog's doors the system calls join the scope
  # (doors/stdout.txt names them).  A jar that ships no catalog has no doors.
  IFS=: read -r -a roots <<<"$(ab_cfg causynth_lineage_roots)"
  if (( ${#roots[@]} > 0 )) && unzip -Z1 "${ab_jar}" \
      edu/uva/liftlab/graphchecker/library-catalog.jsonl >/dev/null 2>&1; then
    mkdir -p "${dir}/doors"
    ab_java "${dir}/doors" "$(ab_heap "$(ab_cfg engine_memory_mb)")" \
      "${ab_jar}" edu.uva.liftlab.graphchecker.plan.ScopeGrowth --doors \
      "${grown}" "${classes}" "${ab_project_cp}" "${roots[@]}" \
      || ab_skip "${dir}" "the door scope failed (doors/stderr.log)" || return
    cp "${dir}/doors/stdout.log" "${dir}/doors/stdout.txt"
  fi
  ab_props=(
    "-Dcausynth.output.dir=${out}"
    "-Dcausynth.target.spec=$(ab_cfg causynth_target_spec)"
    "-Dcausynth.loop.bounds=$(ab_cfg causynth_loop_bounds)"
    "-Dcausynth.region.skeletons=${out}/region_skeletons.jsonl.gz"
  )
  [[ ! -s "${grown}/GROWN" ]] \
    || ab_props+=("-Dcausynth.process.dirs=${grown}")
  [[ -z "$(ab_cfg causynth_communication_mappings)" ]] || ab_props+=(
    "-Dcausynth.communication.mappings=$(ab_cfg causynth_communication_mappings)")
  ab_java "${dir}" "$(ab_heap "$(ab_cfg engine_memory_mb)")" \
    "${ab_jar}:${ab_project_cp}" edu.uva.liftlab.graphchecker.GraphCheckerMain \
    -i "${classes}" -x "${ab_project_cp}" -o "${out}/instrumented-classes"
  ab_props=()
}

# The recording's trace, aggregated over the static artifacts in ${ab_static}.
ab_stage_seed_trace() {
  local dir
  dir=$(ab_stage_dir SEED.trace)
  [[ -s "${ab_acc}/runtime/runtime_trace.jsonl" ]] \
    || ab_skip "${dir}" "the run recorded no trace" || return
  printf '%s\n' "${ab_static}" >"${dir}/static-from.txt"
  ab_java "${dir}" "$(ab_heap "$(ab_cfg engine_memory_mb)")" \
    "${ab_jar}:${ab_project_cp}" \
    edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder \
    --trace-dir "${ab_acc}/runtime" \
    --candidate-graph "${ab_static}/candidate_dataflow_edges.jsonl.gz" \
    --region-skeletons "${ab_static}/region_skeletons.jsonl.gz" \
    --static-scope-map "${ab_static}/static_scope_map.jsonl" \
    --test "$(ab_cfg trace_test)" --output-dir "${dir}"
}

ab_stage_plan() {
  local dir
  local -a args
  dir=$(ab_stage_dir PLAN)
  args=(--region-plan "${ab_case_dir}/SEED.trace/concolic_region_plan.jsonl"
    --output-dir "${dir}"
    --candidate-graph "${ab_static}/candidate_dataflow_edges.jsonl.gz"
    --static-scope-map "${ab_static}/static_scope_map.jsonl"
    --max-jobs "$(ab_cfg schedule_max_jobs)")
  [[ -z "${ab_declared}" ]] || args+=(--target-occurrence "${ab_declared}")
  ab_java "${dir}" "$(ab_heap "$(ab_cfg engine_memory_mb)")" "${ab_jar}" \
    edu.uva.liftlab.graphchecker.plan.ConcolicScheduler "${args[@]}"
}

ab_stage_explore0() {
  local dir
  dir=$(ab_stage_dir EXPLORE.0)
  ab_iteration "${dir}/iteration-0000" wave0 \
      "${ab_case_dir}/PLAN/execution_task_plan.jsonl" \
    || ab_skip "${dir}" "a wave-0 session is not in the recorded corpus" \
    || return
  ab_explore_args
  ab_java "${dir}" "$(ab_heap "$(ab_cfg engine_memory_mb)")" "${ab_jar}" \
    edu.uva.liftlab.graphchecker.explore.ExploreMain \
    --sessions "${dir}/iteration-0000/sessions" \
    --results "${dir}/iteration-0000/obligation_results.jsonl" \
    --static-scope-map "${ab_static}/static_scope_map.jsonl" \
    --topology-epoch iteration-0000 --wave 0 \
    --output-dir "${dir}/iteration-0000/obligations-0000" "${ab_explore[@]}"
}

# One solver per wave-0 obligation, over the iteration EXPLORE.0 left (its
# slot table included), each into its own worker directory: the solver half
# of campaign_obligation_worker, whose failure the campaign records as that
# obligation's NOT_ADMITTED -- an outcome, compared by each worker's own
# status.  The replay half is what this gate is not.
ab_stage_solve0() {
  local dir wave id running=0 start=${SECONDS}
  local -a domains=() ids=()
  dir=$(ab_stage_dir SOLVE.0)
  wave=${ab_case_dir}/EXPLORE.0/iteration-0000/obligations-0000
  [[ -z "${ab_root_domains}" ]] || domains=(--root-domains "${ab_root_domains}")
  mapfile -t ids < <(jq -r '.obligationId' "${wave}/obligations.jsonl")
  for id in "${ids[@]}"; do
    mkdir -p "${dir}/${id}"
    ab_java "${dir}/${id}" "$(ab_heap "")" "${ab_jar}" \
      edu.uva.liftlab.graphchecker.explore.ObligationSolverMain \
      --obligations "${wave}/obligations.jsonl" --obligation-id "${id}" \
      --sessions "${ab_case_dir}/EXPLORE.0/iteration-0000/sessions" \
      --output-dir "${dir}/${id}" --z3 "${ab_z3}" \
      --solver-timeout-ms "$(ab_cfg solver_timeout_ms)" "${domains[@]}" &
    running=$((running + 1))
    if (( running >= AB_SOLVE_JOBS )); then
      wait -n
      running=$((running - 1))
    fi
  done
  while (( running > 0 )); do
    wait -n
    running=$((running - 1))
  done
  printf 'exit=0 wall_s=%s rss_mb=- host=%s obligations=%s\n' \
    "$(( SECONDS - start ))" "$(hostname -s)" "${#ids[@]}" >"${dir}/status"
}

# The recorded corpus a stage over the final iteration needs, or a skip.
ab_corpus() {
  [[ -n "$(ls -A "${ab_acc_it}/sessions" 2>/dev/null)" ]] \
    || ab_skip "$1" "the run published no session"
}

ab_stage_import() {
  local dir code=0
  dir=$(ab_stage_dir IMPORT)
  ab_corpus "${dir}" || return
  ab_iteration "${dir}/iteration-0000" full
  ab_java "${dir}" "$(ab_heap "$(ab_cfg engine_memory_mb)")" "${ab_jar}" \
    edu.uva.liftlab.graphchecker.contract.ImportGateMain \
    --sessions "${dir}/iteration-0000/sessions" \
    --out "${dir}/campaign_gaps.jsonl" --topology-epoch iteration-0000 \
    || code=$?
  cp "${dir}/stdout.log" "${dir}/import_gate.json"
  return "${code}"
}

# The closing wave over the corpus as the campaign left it, and under the
# static map that corpus was explored with.
ab_stage_exploren() {
  local dir last
  dir=$(ab_stage_dir EXPLORE.N)
  ab_corpus "${dir}" || return
  last=$(cd "${ab_acc_it}" && ls -d obligations-* 2>/dev/null | LC_ALL=C sort | tail -n 1)
  [[ -n "${last}" ]] || ab_skip "${dir}" "the run planned no wave" || return
  ab_iteration "${dir}/iteration-0000" full "${last}"
  ab_explore_args
  ab_java "${dir}" "$(ab_heap "$(ab_cfg engine_memory_mb)")" "${ab_jar}" \
    edu.uva.liftlab.graphchecker.explore.ExploreMain \
    --sessions "${dir}/iteration-0000/sessions" \
    --results "${dir}/iteration-0000/obligation_results.jsonl" \
    --static-scope-map "${ab_acc}/static_scope_map.jsonl" \
    --topology-epoch iteration-0000 --wave "$((10#${last#obligations-}))" \
    --output-dir "${dir}/iteration-0000/${last}" "${ab_explore[@]}"
}

ab_stage_compose() {
  local dir
  local -a selection=(--anchor "${ab_declared}")
  dir=$(ab_stage_dir COMPOSE)
  ab_corpus "${dir}" || return
  ab_iteration "${dir}/iteration-0000" full
  mkdir -p "${dir}/final"
  [[ -z "${ab_root_domains}" ]] || selection+=(--root-domains "${ab_root_domains}")
  ab_java "${dir}" "$(ab_heap "$(ab_cfg engine_memory_mb)")" "${ab_jar}" \
    edu.uva.liftlab.graphchecker.compose.ComposeMain \
    --sessions "${dir}/iteration-0000/sessions" \
    --static-scope-map "${ab_acc}/static_scope_map.jsonl" \
    --output "${dir}/final/candidate.smt2" \
    --manifest "${dir}/final/candidate_composition_manifest.json" \
    --solver-timeout-ms "$(ab_cfg solver_timeout_ms)" \
    --max-valuations "$(ab_cfg compose_max_valuations)" \
    --z3 "${ab_z3}" "${selection[@]}"
}

# CONFIRM's planning half: what the confirmation replay would be handed, or
# that the selected session already realized the claim.  A refusal (exit 1,
# "CONFIRM refused:") is an outcome, compared like any other.
ab_stage_confirm() {
  local dir compose=${ab_case_dir}/COMPOSE claim code=0
  dir=$(ab_stage_dir CONFIRM)
  claim=$(jq -r '.solver.campaignClaim.claim // ""' \
    "${compose}/final/candidate_composition_manifest.json")
  if [[ "${claim}" != SAT_CANDIDATE ]]; then
    printf 'exit=0 wall_s=- rss_mb=- host=%s\n' "$(hostname -s)" >"${dir}/status"
    printf 'claim=%s: nothing to confirm\n' "${claim}" >"${dir}/confirm_skipped.txt"
    return 0
  fi
  ab_java "${dir}" "$(ab_heap "$(ab_cfg engine_memory_mb)")" "${ab_jar}" \
    edu.uva.liftlab.graphchecker.explore.ConfirmMain \
    --iteration "${compose}/iteration-0000" \
    --claim "${compose}/final/claim.json" \
    --manifest "${compose}/final/candidate_composition_manifest.json" \
    --output "${dir}/final/confirm/worker" || code=$?
  cp "${dir}/stdout.log" "${dir}/confirm_summary.json"
  return "${code}"
}

# One side of one case: its jar, its recorded run and its config.
ab_side_env() {
  local out=$1 side=$2 case_id=$3
  ab_case_dir=${out}/${side}/${case_id}
  ab_jar=${out}/jars/${side}.jar
  read -r ab_acc ab_case_decl ab_case_arg ab_side_repo \
    <"${ab_case_dir}/inputs.txt"
  [[ "${ab_case_arg}" == - ]] && ab_case_arg=""
  ab_acc_it=${ab_acc}/schedule/iteration-0000
  ab_java_bin=$(ab_cfg java_bin)
  ab_loop_bound=$(ab_cfg causynth_loop_default_bound)
  ab_project_cp=$(ab_cfg project_classpath)
  ab_root_domains=$(ab_cfg causynth_root_domains)
  ab_z3=${AB_Z3:-$(ab_cfg z3_bin)}
  ab_declared=$(ab_cfg declared_target_occurrence)
  # A sweep's "first" is what PLAN resolved it to (campaign_plan).
  [[ "${ab_declared}" != first ]] || ab_declared=$(jq -r '.target.occurrenceId' \
    "${ab_acc_it}/runtime_workflow_schedule_index.json")
}

# The rest of a side's SEED chain after SEED.trace, over ${ab_static}.
ab_trace_rest() {
  ab_ok SEED.trace || ab_skip "${ab_case_dir}/PLAN" "SEED.trace failed" \
    || ab_skip "${ab_case_dir}/EXPLORE.0" "SEED.trace failed" \
    || ab_skip "${ab_case_dir}/SOLVE.0" "SEED.trace failed" || return 0
  ab_stage_plan
  ab_ok PLAN || ab_skip "${ab_case_dir}/EXPLORE.0" "PLAN failed" \
    || ab_skip "${ab_case_dir}/SOLVE.0" "PLAN failed" || return 0
  ab_stage_explore0
  ab_ok EXPLORE.0 || ab_skip "${ab_case_dir}/SOLVE.0" "EXPLORE.0 failed" \
    || return 0
  ab_stage_solve0
}

# The SEED chain: each side's static pass, then each side's trace chain
# over ONE set of static artifacts -- the recording's own when the baseline
# still aggregates the trace over them, else the baseline's fresh ones (a
# v92 run's skeletons declare ports main refuses, while 17960's fresh ones
# open a region its v92 trace never addressed).  The static pass is not
# deterministic, so neither side reads its own.
ab_seed() {
  local out=$1 case_id=$2 side fresh
  for side in "${AB_SIDES[@]}"; do
    ( ab_side_env "${out}" "${side}" "${case_id}"; ab_stage_seed_static ) &
  done
  wait
  fresh=${out}/baseline/${case_id}/SEED.static/out
  ab_side_env "${out}" baseline "${case_id}"
  ab_static=${ab_acc}
  ab_stage_seed_trace
  if ! ab_ok SEED.trace && [[ -s "${ab_acc}/runtime/runtime_trace.jsonl" ]] \
      && ab_ok SEED.static && [[ -s "${fresh}/static_scope_map.jsonl" ]]; then
    ab_static=${fresh}
    ab_stage_seed_trace
  fi
  ( ab_trace_rest ) &
  ( ab_side_env "${out}" candidate "${case_id}"
    ab_stage_seed_trace
    ab_trace_rest ) &
  wait
}

# --task <out> <case>: every chain AB_STAGES names, for both sides.
ab_task() {
  local out=$1 case_id=$2 side chain
  # shellcheck source=/dev/null
  source "${out}/env.sh"
  [[ " ${AB_STAGES} " != *" SEED "* ]] || ab_seed "${out}" "${case_id}" &
  for side in "${AB_SIDES[@]}"; do
    ( ab_side_env "${out}" "${side}" "${case_id}"
      for chain in ${AB_STAGES}; do
        case "${chain}" in
          IMPORT) ab_stage_import ;;
          EXPLORE.N) ab_stage_exploren ;;
          COMPOSE)
            if ab_stage_compose; then ab_stage_confirm
            else ab_skip "${ab_case_dir}/CONFIRM" "COMPOSE failed or did not run"
            fi ;;
        esac
      done ) &
  done
  wait
}

# ---------------------------------------------------------------------------
# The driver
# ---------------------------------------------------------------------------

# The experiment a case id lives in (accept.sh acc_experiment_of): the longest
# "-"-prefix naming a case directory; prints "<dir> <case-arg or ->".
ab_experiment_of() {
  local repo=$1 case_id=$2 exp=$2 dir
  while :; do
    for dir in "${repo}"/experiments/*/"${exp}"; do
      if [[ -f "${dir}/case.sh" ]]; then
        local arg=${case_id#"${exp}"}
        arg=${arg#-}
        printf '%s %s\n' "${dir}" "${arg:--}"
        return 0
      fi
    done
    [[ "${exp}" == *-* ]] || return 1
    exp=${exp%-*}
  done
}

# The recorded run of a case: the first round naming one.
ab_recorded_run() {
  local case_id=$1 round dir
  for round in "${ab_rounds[@]}"; do
    if [[ -d "${round}" ]]; then
      dir=${round}/out/${case_id}
    else
      dir=${AB_ACCEPT_ROOT}/accept-${round}-${case_id#hdfs-}/out/${case_id}
    fi
    [[ -d "${dir}/runtime" ]] && { readlink -f "${dir}"; return 0; }
  done
  return 1
}

# The workload classpath the run froze (EMIT's manifest, else the iteration
# manifest EXPLORE left), or nothing.
ab_recorded_classpath() {
  local file
  for file in "$1/schedule/final/run-manifest.json" \
      "$1/schedule/iteration-0000/iteration_manifest.json"; do
    [[ -f "${file}" ]] && jq -r '.provenance.workload.classpath // empty' "${file}" \
      && return 0
  done
}

ab_main() {
  ab_rounds=()
  while [[ "${1:-}" == --round ]]; do
    ab_rounds+=("${2:?--round needs a tag or a directory}")
    shift 2
  done
  (( ${#ab_rounds[@]} > 0 )) || ab_rounds=("${AB_DEFAULT_ROUNDS[@]}")
  local baseline=${1:-} candidate=${2:-}
  [[ -f "${baseline}" && -f "${candidate}" ]] || ab_die "usage: offline-ab.sh \
[--round TAG|DIR]... <baseline-jar> <candidate-jar> [case...]"
  shift 2
  local -a cases=("$@") pids=() override
  local case_id dir side acc decl arg chain classpath onlift repo base_repo
  AB_OUT=${AB_OUT:-/bigtemp/vnr3ne/ab/$(date +%Y%m%d-%H%M%S)}
  AB_ACCEPT_ROOT=${AB_ACCEPT_ROOT:-${GC_OUT}}
  AB_STAGES=${AB_STAGES:-${AB_CHAINS[*]}}
  for chain in ${AB_STAGES}; do
    [[ " ${AB_CHAINS[*]} " == *" ${chain} "* ]] \
      || ab_die "AB_STAGES names ${chain}; the chains are ${AB_CHAINS[*]}"
  done
  (( ${#cases[@]} > 0 )) || cases=("${AB_CASES[@]}")
  [[ ! -e "${AB_OUT}" || -z "$(ls -A "${AB_OUT}")" ]] \
    || ab_die "AB_OUT already holds a run: ${AB_OUT}"
  base_repo=$(cd "${AB_BASELINE_REPO:-${ab_self_repo}}" && pwd -P) \
    || ab_die "AB_BASELINE_REPO is not a directory: ${AB_BASELINE_REPO}"
  mkdir -p "${AB_OUT}/jars" "${AB_OUT}/logs"
  local t0=${SECONDS}

  # Both jars, frozen, and what every task reads.
  cp "${baseline}" "${AB_OUT}/jars/baseline.jar"
  cp "${candidate}" "${AB_OUT}/jars/candidate.jar"
  printf 'AB_HEAP_MB=%q\nAB_SOLVE_JOBS=%q\nAB_STAGE_TIMEOUT_S=%q\nAB_STAGES=%q\n' \
    "${AB_HEAP_MB:-8192}" "${AB_SOLVE_JOBS:-2}" "${AB_STAGE_TIMEOUT_S:-1800}" \
    "${AB_STAGES}" >"${AB_OUT}/env.sh"
  [[ -z "${AB_Z3:-}" ]] || printf 'AB_Z3=%q\n' "${AB_Z3}" >>"${AB_OUT}/env.sh"
  printf '%s\n' ${AB_STAGES} >"${AB_OUT}/chains.txt"
  printf 'baseline\t%s\t%s\ncandidate\t%s\t%s\n' \
    "$(readlink -f "${baseline}")" "${base_repo}" \
    "$(readlink -f "${candidate}")" "${ab_self_repo}" >"${AB_OUT}/sides.tsv"

  # Each case: its recorded run, each side's declarations of it, and the
  # config run_engine.sh reads -- with the classpath the run froze, when it
  # states one.
  for case_id in "${cases[@]}"; do
    acc=$(ab_recorded_run "${case_id}") \
      || ab_die "no round of ${ab_rounds[*]} recorded ${case_id}"
    printf '%s\t%s\n' "${case_id}" "${acc}" >>"${AB_OUT}/accepted.tsv"
    classpath=$(ab_recorded_classpath "${acc}")
    override=()
    [[ -z "${classpath}" ]] || override=("CAUSYNTH_CLASSPATH_OVERRIDE=${classpath}")
    for side in "${AB_SIDES[@]}"; do
      repo=${ab_self_repo}
      [[ "${side}" == candidate ]] || repo=${base_repo}
      read -r decl arg < <(ab_experiment_of "${repo}" "${case_id}") \
        || ab_die "${repo} declares no experiment for ${case_id}"
      dir=${AB_OUT}/${side}/${case_id}
      mkdir -p "${dir}"
      printf '%s %s %s %s\n' "${acc}" "${decl}" "${arg}" "${repo}" \
        >"${dir}/inputs.txt"
      (cd "${decl}" && env -i HOME="${HOME}" PATH="${PATH}" \
          CAUSYNTH_OUTPUT_DIR="${dir}/SEED.static/out" "${override[@]}" \
          bash "${repo}/experiments/lib/run.sh" "${decl}" \
          "$([[ ${arg} == - ]] || echo "${arg}")" config) \
        >"${dir}/config.txt" 2>"${dir}/config.log" \
        || ab_die "${case_id}: run.sh config failed (${dir}/config.log)"
    done
  done

  # One task per case, heaviest corpus first, each on the lift onlift.sh
  # picks for it; a lift it cannot place a case on yet is waited for.
  onlift=/bigtemp/vnr3ne/bin/onlift.sh
  ab_log "offline A/B: ${#cases[@]} case(s) [${AB_STAGES}] from rounds \
${ab_rounds[*]} -> ${AB_OUT}"
  trap 'kill ${pids[*]} 2>/dev/null; exit 130' INT TERM
  for case_id in $(for case_id in "${cases[@]}"; do
        acc=$(awk -F'\t' -v c="${case_id}" '$1 == c {print $2}' "${AB_OUT}/accepted.tsv")
        printf '%s %s\n' "$(du -sk "${acc}/schedule/iteration-0000/sessions/" \
          2>/dev/null | cut -f1)" "${case_id}"
      done | sort -rn | awk '{print $2}'); do
    (( ${#pids[@]} == 0 )) || sleep "${AB_STAGGER_S:-8}"
    if [[ "${AB_HOSTS:-}" == local ]]; then
      bash "${ab_self}" --task "${AB_OUT}" "${case_id}" \
        >"${AB_OUT}/logs/${case_id}.log" 2>&1 &
    else
      ( until "${onlift}" -g "${AB_CASE_GB:-14}" bash "${ab_self}" --task \
            "${AB_OUT}" "${case_id}"; do
          (( $? == 75 )) || exit 1
          sleep 30
        done ) >"${AB_OUT}/logs/${case_id}.log" 2>&1 &
    fi
    pids+=("$!")
  done
  wait
  trap - INT TERM
  ab_log "stages done in $(( SECONDS - t0 )) s ($(for case_id in "${cases[@]}"; do
      printf '%s@%s ' "${case_id}" "$(sed -n 's/^onlift: running on //p' \
        "${AB_OUT}/logs/${case_id}.log" | tail -n 1)"; done)); comparing"
  python3 "$(dirname "${ab_self}")/ab_compare.py" "${AB_OUT}" "${cases[@]}"
  local verdict=$?
  ab_log "offline A/B finished in $(( SECONDS - t0 )) s: $(case ${verdict} in
    0) echo identical ;; 1) echo DIFFERS ;; *) echo 'NOT CHECKED' ;; esac)"
  return "${verdict}"
}

if [[ "${1:-}" == --task ]]; then
  shift
  ab_task "$@"
else
  ab_main "$@"
fi

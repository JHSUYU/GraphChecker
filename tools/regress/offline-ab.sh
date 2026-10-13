#!/usr/bin/env bash
# offline-ab.sh -- the offline regression gate: does a candidate jar compute
# anything different from a baseline jar on recorded campaigns?
#
#   tools/regress/offline-ab.sh --round TAG|DIR [--round TAG|DIR]... <baseline-jar> <candidate-jar> [case...]
#
# No workload and no concolic replay runs.  Every stage below is a pure
# function of what a campaign recorded, run once per jar with the arguments
# run_engine.sh passes it (the function named beside it), and the two sides'
# outputs are compared by tools/regress/ab_compare.py:
#
#   chain     stage       mirrors                       reads
#   SEED      SEED.static do_analyze (static pass) in   the case's scope, copied again from its tree,
#                         campaign_analyze_grown_scope's the library doors' classes it calls and the
#                         loop (door step, pass, scope  classes its frontier grows (within the
#                         growth, until none is added)  case's causynth_scope_growth_budget)
#             SEED.trace  do_workload's aggregation     the recording's runtime/ + one set of static
#                                                       artifacts for both sides (ab_seed)
#             PLAN        do_schedule                   this side's SEED.trace plan
#             EXPLORE.0   campaign_explore, round 0     the seed session + this side's PLAN
#             SOLVE.0     campaign_obligation_worker's  each EXPLORE.0 obligation (z3), no replay
#                         solver
#   IMPORT    IMPORT      campaign_import_gate          the recorded final corpus
#   EXPLORE.N EXPLORE.N   campaign_explore, last round  the recorded final corpus, verdicts, slots
#   COMPOSE   COMPOSE     do_compose (+SOLVE, DECIDE)   the recorded final corpus (z3)
#             CONFIRM     campaign_confirm's ConfirmMain this side's COMPOSE claim, no replay
#
# The chain SEED.static is SEED's static pass alone: what a slice change
# costs (wall, edges, methods, scope rows, chosen keys) on cases whose
# recording no later stage of this checkout reads.  The chains EXPLORE.drift
# and EXPLORE.serve replay the run's landing order (ab_stage_landings): every
# recorded round planned again, in one iteration that evolves as the run's
# did, over the sessions landed before its planner started, with no answer
# and nothing in flight, so every flip it offers is keyed.  EXPLORE.drift
# plans each round in a JVM of its own on both sides: a flip offered under
# two ids is an arm the run asks again -- what a change to an arm's key does
# to the re-asks (the run's own answers are keyed by the jar that recorded
# it).  EXPLORE.serve's baseline side plans each round in a JVM of its own
# and its candidate side asks every round of ONE served planner (ExploreMain
# --serve): whether a served planner's rounds are a fresh planner's (pass one
# jar as both); each side's per-round walls are its walls.tsv.
#
# The recorded runs are the rounds named (--round, at least one; the first
# holding a case wins): a TAG is ${AB_ACCEPT_ROOT}/accept-<TAG>-<case without
# hdfs->, as tools/rounds writes them; a DIR is an accept.sh output
# (DIR/out/<case>).  AB_STAGES=SEED.static reads no recording, so a case no
# round recorded runs too.  A round is read as the current engine reads it, so name
# rounds recorded by a build whose row contract HEAD still reads.
#
# A stage that reads an iteration reads a private one: the recorded sessions
# and obligation rounds linked (a round's slot-table changes with it, so the
# closing round folds the rounds before it), the iteration's files copied,
# so nothing under a recorded run is ever written.  A stage's slot table is
# compared folded (ab_compare.py).  Both jars are
# copied into the output first (a rebuild under a running gate changes
# nothing) and run under THIS checkout's case declarations and harness
# (experiments/): the jar is the one variable -- unless AB_BASELINE_REPO
# gives the baseline its own checkout's, for a change that moves a
# declaration's format together with the jar (a target spec).  The workload
# classpath is the one the run froze when it states one (its tree's report
# may be gone).
#
# Each case is one task, both sides inside it, run here.  Gates run beside
# live rounds, so every engine JVM of a stage is placed through the host
# ledger every campaign charges (run_engine.sh campaign_host_try_start): on
# the host of AB_HOSTS with the most room for its heap, charged that for its
# whole run, and waited for when none has it -- no host passes
# CAUSYNTH_HOST_MAX_USED_PCT (70) percent, and a campaign's starts see the
# gate's JVMs as theirs (two 16 GB composers of one case once shared a lift
# placed for 20 GB, at 91 %).
#
# Prints one table (case | stage | identical/DIFFERS/ERROR | baseline vs the
# recorded artifact | wall | summary) and writes it to $AB_OUT/report.tsv,
# the differing files' diffs to $AB_OUT/diffs/.  Exit 0: every gating stage
# identical; 1: one differs; 2: none differs but one could not be checked
# (it failed or timed out on the baseline too, lacked a recorded input, or
# never ran).
#
# Environment
#   AB_OUT        output root (default $GC_BULK/ab/<timestamp>), on a
#                 filesystem every lift shares
#   AB_HOSTS      the hosts an engine JVM may be placed on (default LIFTS,
#                 tools/lib/gc-env.sh; localhost: this machine only)
#   AB_HEAP_MB    engine JVM heap cap (default 8192; a case's engine_memory_mb
#                 above it is lowered to it)
#   AB_SOLVE_JOBS concurrent SOLVE.0 solvers of one side (default 1)
#   AB_STAGE_TIMEOUT_S  wall bound of one JVM (default 1800)
#   AB_STAGES     the chains to run (default "SEED IMPORT EXPLORE.N COMPOSE";
#                 SEED.static: the static pass alone)
#   AB_ACCEPT_ROOT  where round TAGs live (default $GC_OUT, tools/lib/gc-env.sh)
#   AB_Z3         the z3 both sides use (default: the case's z3_bin)
#   AB_BASELINE_REPO  the checkout whose experiments/ declare the baseline's
#                 cases (default: this one)
#   AB_FRESH_SLICE  1: each side's SEED.trace, PLAN and EXPLORE.0 read its own
#                 fresh SEED.static (default 0: one shared set, ab_seed)
set -uo pipefail

ab_self=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)/$(basename "${BASH_SOURCE[0]}")
ab_self_repo=$(cd "$(dirname "${ab_self}")/../.." && pwd -P)
# shellcheck source=../lib/gc-env.sh
source "${ab_self_repo}/tools/lib/gc-env.sh"
# The host ledger's helpers (campaign_host_try_start and its kin), as
# tools/adhoc/fanout.sh takes them.
# shellcheck source=../../run_engine.sh
source "${ab_self_repo}/run_engine.sh"
# shellcheck source=../../experiments/lib/case-id.sh
source "${ab_self_repo}/experiments/lib/case-id.sh"
set +e

AB_CASES=(hdfs-17899-bug1 hdfs-17899-bug2 hdfs-17899-bug3 hdfs-17967-pathA
  hdfs-17967-pathB hdfs-17967-pathC hdfs-17960 hdfs-17897 hdfs-11741)
AB_CHAINS=(SEED IMPORT EXPLORE.N COMPOSE)
# Chains AB_STAGES may name beside the default ones.
AB_EXTRA_CHAINS=(SEED.static EXPLORE.drift EXPLORE.serve)
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
# through the case's java_bin as run_java_main starts it (the loop bound, the
# system's own doors file -- which views its system publishes,
# LibraryCatalog#publishedView, decides COMPOSE's and CONFIRM's held views:
# without it a Solr COMPOSE offered no node view a version choice -- then
# ab_props), in the stage directory, bounded, on the host ab_place
# charged its heap on (every path it reads and writes is shared); its exit,
# wall time, peak RSS and host go to <stage-dir>/status.
ab_props=()
ab_java() {
  local dir=$1 heap=$2 cp=$3 main=$4 code=0 wall rss
  shift 4
  local -a run=(env "GRAPH_CHECKER_ENGINE_MEMORY_MB=${heap}"
    timeout -k 30 "${AB_STAGE_TIMEOUT_S}"
    /usr/bin/time -f '%e %M' -o "${dir}/time.txt"
    "${ab_java_bin}" "${campaign_engine_stack}"
    "-Dcausynth.loop.default.bound=${ab_loop_bound}"
    "-Dcausynth.system.doors=$(ab_cfg causynth_system_doors)"
    "${ab_props[@]}" -cp "${cp}" "${main}" "$@")
  ab_place "${heap}"
  if campaign_host_is_local "${ab_placed_host}"; then
    (cd "${dir}" && "${run[@]}") \
      >"${dir}/stdout.log" 2>"${dir}/stderr.log" </dev/null || code=$?
  else
    ssh -o BatchMode=yes "${ab_placed_host}" "cd $(printf '%q' "${dir}") \
&& $(printf '%q ' "${run[@]}")" \
      >"${dir}/stdout.log" 2>"${dir}/stderr.log" </dev/null || code=$?
  fi
  campaign_host_release "${ab_placed_host}" "${ab_placed_charge}"
  read -r wall rss < <(tail -n 1 "${dir}/time.txt" 2>/dev/null) || true
  printf 'exit=%s wall_s=%s rss_mb=%s host=%s\n' "${code}" "${wall:-?}" \
    "$(( ${rss:-0} / 1024 ))" "${ab_placed_host}" >"${dir}/status"
  return "${code}"
}

# ab_place <need-mb>: the host of AB_HOSTS with the most room for <need-mb>
# on the ledger (run_engine.sh campaign_host_room), charged it until ab_java
# releases it; waited for while no host has it.  The host
# is ab_placed_host, its charge ab_placed_charge.
ab_placed_host=""
ab_placed_charge=""
ab_place() {
  local need=$1 host room best best_room
  while true; do
    best=""
    best_room=-1
    for host in ${AB_HOSTS}; do
      room=$(campaign_host_room "${host}") || continue
      (( room >= need && room > best_room )) || continue
      best=${host}
      best_room=${room}
    done
    if [[ -n "${best}" ]] && campaign_host_try_start "${best}" "${need}"; then
      ab_placed_host=${best}
      ab_placed_charge=${campaign_host_charge_id}
      return 0
    fi
    sleep "${campaign_host_poll_s}"
  done
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

# ab_iteration <dst> full|wave0 [plan | round left out]: a private iteration
# over the recorded one.  full: every session and obligation round linked
# (but the one named, which the stage writes), the iteration's files
# copied, the models CONFIRM refuted or gave no verdict on among them (the
# final COMPOSE excluded them) but the last claim's own.  wave0: the sessions round 0 was planned over -- the seed alone,
# the one session whose manifest states SEED -- the recorded schedule, and
# this side's PLAN as the iteration plan; no round, no slot table.  A
# round's output goes inside, where the planner reads the round before it.
ab_iteration() {
  local dst=$1 mode=$2 extra=${3:-} name file wave
  mkdir -p "${dst}"
  [[ -f "${ab_acc_it}/recorded_schedule.jsonl" ]] \
    && cp "${ab_acc_it}/recorded_schedule.jsonl" "${dst}/"
  if [[ "${mode}" == wave0 ]]; then
    mkdir -p "${dst}/sessions"
    for name in "${ab_acc_it}"/sessions/*/manifest.json; do
      jq -e '.role == "SEED"' "${name}" >/dev/null 2>&1 || continue
      name=$(basename "$(dirname "${name}")")
      ln -s "${ab_acc_it}/sessions/${name}" "${dst}/sessions/${name}"
    done
    [[ -n "$(ls "${dst}/sessions")" ]] || return 1
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
  # The models CONFIRM refuted, which the last COMPOSE excluded: all but the
  # last claim's own row, written after that COMPOSE.
  local last="" final
  final=$(dirname "${ab_acc_it}")/final
  [[ ! -s "${final}/claim.json" ]] \
    || last=$(campaign_claim_model "${final}/claim.json")
  for file in refuted_claims.jsonl; do
    [[ -f "${ab_acc_it}/${file}" ]] || continue
    jq -c --argjson last "${last:-null}" "${campaign_model_key}"'
      select(((.claimed // "") | endswith("/final")) and $last != null
        and (.model | key) == ($last | key) | not)' \
      "${ab_acc_it}/${file}" >"${dst}/${file}"
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
}

ab_stage_seed_static() {
  local dir classes out grown growth sha step=0 changes summary heap
  local -a roots=() pass=()
  dir=$(ab_stage_dir SEED.static)
  classes=${dir}/classes
  out=${dir}/out
  grown=${dir}/scope-classes
  growth=$(ab_cfg causynth_scope_growth_budget)
  heap=$(ab_heap "$(ab_cfg engine_memory_mb)")
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
  IFS=: read -r -a roots <<<"$(ab_cfg causynth_lineage_roots)"
  pass=(
    "-Dcausynth.output.dir=${out}"
    "-Dcausynth.target.spec=$(ab_cfg causynth_target_spec)"
    "-Dcausynth.loop.bounds=$(ab_cfg causynth_loop_bounds)"
    "-Dcausynth.region.skeletons=${out}/region_skeletons.jsonl.gz"
  )
  [[ -z "$(ab_cfg causynth_lineage_roots)" ]] || pass+=(
    "-Dcausynth.lineage.roots=$(ab_cfg causynth_lineage_roots)")
  [[ -z "$(ab_cfg causynth_communication_mappings)" ]] || pass+=(
    "-Dcausynth.communication.mappings=$(ab_cfg causynth_communication_mappings)")
  # campaign_analyze_grown_scope: the door step, then the static pass and
  # scope growth over its frontier until nothing is added or the budget is
  # spent, the door step again after every growth; a pass that chose more
  # demanded doors runs again over them.  The stage's wall is the whole
  # loop's; each step's directory names what it grew.
  local doors=0 chosen
  pass+=("-Dcausynth.io.doors=${out}/io_doors.jsonl")
  ab_seed_doors "${dir}/doors" || { ab_props=(); return; }
  while :; do
    ab_props+=("${pass[@]}")
    [[ ! -s "${grown}/GROWN" ]] \
      || ab_props+=("-Dcausynth.process.dirs=${grown}")
    ab_java "${dir}" "${heap}" "${ab_jar}" \
      edu.uva.liftlab.graphchecker.GraphCheckerMain \
      -i "${classes}" -x "${ab_project_cp}" -o "${out}/instrumented-classes" \
      || break
    ab_seed_wall "${dir}"
    ab_props=()
    chosen=$(grep -c . "${out}/io_doors.jsonl" 2>/dev/null || true)
    if (( ${chosen:-0} > doors )); then
      doors=${chosen}
      continue
    fi
    [[ "${growth:-0}" != 0 ]] && (( ${#roots[@]} > 0 )) || break
    step=$(( step + 1 ))
    mkdir -p "${dir}/growth-${step}"
    ab_java "${dir}/growth-${step}" "${heap}" "${ab_jar}" \
      edu.uva.liftlab.graphchecker.plan.ScopeGrowth "${grown}" \
      "${out}/scope_frontier.jsonl" "${growth}" "${classes}" "${roots[@]}" \
      || { ab_skip "${dir}" "scope growth failed (growth-${step}/stderr.log)"
           break; }
    ab_seed_wall "${dir}/growth-${step}"
    read -r changes summary <"${dir}/growth-${step}/stdout.log"
    [[ "${changes}" =~ ^[1-9][0-9]*$ ]] || break
    ab_seed_doors "${dir}/doors-${step}" || break
  done
  ab_props=()
  # The loop's wall in place of the last pass's.
  [[ ! -f "${dir}/status" ]] || sed -i "s/ wall_s=[^ ]* / wall_s=${ab_seed_total} /" \
    "${dir}/status"
  ab_seed_total=0
}

# The door step (campaign_scope_doors) into the stage's grown scope: the
# class families of the library doors the analysis scope calls join it
# (<dir>/stdout.txt names them).  A jar that ships no catalog has no doors.
ab_seed_doors() {
  local step=$1
  (( ${#roots[@]} > 0 )) && unzip -Z1 "${ab_jar}" \
    edu/uva/liftlab/graphchecker/library-catalog.jsonl >/dev/null 2>&1 \
    || return 0
  mkdir -p "${step}"
  ab_java "${step}" "${heap}" "${ab_jar}" \
    edu.uva.liftlab.graphchecker.plan.ScopeGrowth --doors \
    "${grown}" "${classes}" "${ab_project_cp}" "${roots[@]}" \
    || ab_skip "${dir}" "the door scope failed ($(basename "${step}")/stderr.log)" \
    || return
  ab_seed_wall "${step}"
  cp "${step}/stdout.log" "${step}/stdout.txt"
}

# Adds one step's wall (its time.txt) to the SEED.static loop's.
ab_seed_total=0
ab_seed_wall() {
  local wall
  read -r wall _ < <(tail -n 1 "$1/time.txt" 2>/dev/null) || return 0
  ab_seed_total=$(awk -v a="${ab_seed_total}" -v b="${wall:-0}" \
    'BEGIN {printf "%.2f", a + b}')
}

# The recording's trace, aggregated over the static artifacts in ${ab_static}.
ab_stage_seed_trace() {
  local dir
  dir=$(ab_stage_dir SEED.trace)
  [[ -s "${ab_acc}/runtime/runtime_trace.jsonl" ]] \
    || ab_skip "${dir}" "the run recorded no trace" || return
  printf '%s\n' "${ab_static}" >"${dir}/static-from.txt"
  local -a declared=()
  [[ -z "$(ab_cfg declared_target_occurrence)" ]] || declared=(
    --target-occurrence "$(ab_cfg declared_target_occurrence)")
  ab_java "${dir}" "$(ab_heap "$(ab_cfg engine_memory_mb)")" \
    "${ab_jar}:${ab_project_cp}" \
    edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder \
    --trace-dir "${ab_acc}/runtime" --test "$(ab_cfg trace_test)" \
    "${declared[@]}" \
    --target "ab=${ab_static}/candidate_dataflow_edges.jsonl.gz,\
${ab_static}/static_scope_map.jsonl,${ab_static}/region_skeletons.jsonl.gz,\
${dir}"
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
    || ab_skip "${dir}" "the recorded corpus states no seed session" \
    || return
  ab_explore_args
  ab_java "${dir}" "$(ab_heap "$(ab_cfg engine_memory_mb)")" "${ab_jar}" \
    edu.uva.liftlab.graphchecker.explore.ExploreMain \
    --sessions "${dir}/iteration-0000/sessions" \
    --results "${dir}/iteration-0000/obligation_results.jsonl" \
    --static-scope-map "${ab_static}/static_scope_map.jsonl" \
    --topology-epoch iteration-0000 --round 0 \
    --output-dir "${dir}/iteration-0000/obligations-0000" "${ab_explore[@]}"
}

# One solver per round-0 obligation, over the iteration EXPLORE.0 left (its
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

# The closing round over the corpus as the campaign left it, and under the
# static map that corpus was explored with.
ab_stage_exploren() {
  local dir last
  dir=$(ab_stage_dir EXPLORE.N)
  ab_corpus "${dir}" || return
  last=$(cd "${ab_acc_it}" && ls -d obligations-* 2>/dev/null | LC_ALL=C sort | tail -n 1)
  [[ -n "${last}" ]] || ab_skip "${dir}" "the run planned no round" || return
  ab_iteration "${dir}/iteration-0000" full "${last}"
  ab_explore_args
  ab_java "${dir}" "$(ab_heap "$(ab_cfg engine_memory_mb)")" "${ab_jar}" \
    edu.uva.liftlab.graphchecker.explore.ExploreMain \
    --sessions "${dir}/iteration-0000/sessions" \
    --results "${dir}/iteration-0000/obligation_results.jsonl" \
    --static-scope-map "${ab_acc}/static_scope_map.jsonl" \
    --topology-epoch iteration-0000 --round "$((10#${last#obligations-}))" \
    --output-dir "${dir}/iteration-0000/${last}" "${ab_explore[@]}"
}

# The landing order replayed (EXPLORE.drift, EXPLORE.serve): this side's
# whole loop (ab_landings) on the host of AB_HOSTS with the most room for
# the planner's heap, charged that while it runs (ab_place) -- there, since a
# host lists at once only the links it made itself in the iteration.
ab_stage_landings() {
  local chain=$1 dir heap mode=fresh code=0
  dir=$(ab_stage_dir "${chain}")
  [[ "${chain}" != EXPLORE.serve || "${ab_side}" != candidate ]] \
    || mode=served
  heap=$(ab_heap "$(ab_cfg engine_memory_mb)")
  ab_place "${heap}"
  local -a loop=(bash "${ab_self}" --landings "${ab_out}" "${ab_side}"
    "${ab_case_id}" "${chain}" "${mode}" "${heap}")
  if campaign_host_is_local "${ab_placed_host}"; then
    "${loop[@]}" >"${dir}/stdout.log" 2>"${dir}/stderr.log" </dev/null \
      || code=$?
  else
    ssh -o BatchMode=yes "${ab_placed_host}" "$(printf '%q ' "${loop[@]}")" \
      >"${dir}/stdout.log" 2>"${dir}/stderr.log" </dev/null || code=$?
  fi
  campaign_host_release "${ab_placed_host}" "${ab_placed_charge}"
  printf 'exit=%s wall_s=%s rss_mb=- host=%s\n' "${code}" \
    "$(awk '{w += $2} END {printf "%.2f", w}' "${dir}/walls.tsv" \
      2>/dev/null)" "${ab_placed_host}" >"${dir}/status"
  return "${code}"
}

# --landings <out> <side> <case> <chain> fresh|served <heap_mb>: the
# landing order replayed, here.  Before each recorded round its iteration
# gains what the run had when that round's planner started: the sessions
# landed by then (a session lands by a rename, so its directory's ctime is
# its landing; the round's in_flight.jsonl is copied as its planner starts),
# the workers of the round before (linked into this replay's own round
# directory), the plan generation then current.  fresh: the round planned
# by a JVM of its own; served: asked of the one planner served from the
# start (run_engine.sh campaign_planner_ask).  Each round's wall, from its
# start to its files, is a row of walls.tsv.
ab_landings() {
  local out=$1 side=$2 case_id=$3 chain=$4 mode=$5 heap=$6
  local dir it wave round start name plan prev="" t0 served="" code=0
  # shellcheck source=/dev/null
  source "${out}/env.sh"
  ab_side_env "${out}" "${side}" "${case_id}"
  ab_explore_args
  dir=${ab_case_dir}/${chain}
  it=${dir}/iteration-0000
  mkdir -p "${it}/sessions"
  [[ ! -f "${ab_acc_it}/recorded_schedule.jsonl" ]] \
    || cp "${ab_acc_it}/recorded_schedule.jsonl" "${it}/"
  : >"${it}/obligation_results.jsonl"
  local -a planner=(env "GRAPH_CHECKER_ENGINE_MEMORY_MB=${heap}"
    "${ab_java_bin}" -XX:+ExitOnOutOfMemoryError "${campaign_engine_stack}"
    "-Dcausynth.loop.default.bound=${ab_loop_bound}" -cp "${ab_jar}"
    edu.uva.liftlab.graphchecker.explore.ExploreMain
    --sessions "${it}/sessions" --results "${it}/obligation_results.jsonl"
    --static-scope-map "${ab_acc}/static_scope_map.jsonl"
    --topology-epoch iteration-0000 "${ab_explore[@]}")
  if [[ "${mode}" == served ]]; then
    served=$(campaign_planner_dir "${it}/sessions" ab)
    rm -rf -- "${served}"
    mkdir -p "${served}/requests"
    "${planner[@]}" --serve "${served}" >>"${dir}/planner.log" 2>&1 &
    ab_served_jvm=$!
    ab_served_dir=${served}
    printf '%s\n' "${ab_served_jvm}" >"${served}/server"
    trap ab_landings_end EXIT
  fi
  for wave in "${ab_acc_it}"/obligations-*; do
    round=$(basename "${wave}")
    start=$(stat -c %Y "${wave}/in_flight.jsonl" 2>/dev/null) \
      || start=$(stat -c %Y "${wave}/obligations.jsonl") || continue
    for name in "${ab_acc_it}"/sessions/*; do
      [[ ! -e "${it}/sessions/$(basename "${name}")" ]] || continue
      (( $(stat -c %Z "${name}") < start )) && ln -s "${name}" "${it}/sessions/"
    done
    if [[ -n "${prev}" ]]; then
      for name in "${ab_acc_it}/${prev}"/*/; do
        [[ -d "${name}" ]] && ln -s "${name%/}" "${it}/${prev}/"
      done
    fi
    prev=${round}
    plan=${ab_acc_it}/execution_task_plan.jsonl
    for name in "${ab_acc_it}"/generations/g*/execution_task_plan.jsonl; do
      [[ -f "${name}" ]] && (( $(stat -c %Y "${name}") < start )) && plan=${name}
    done
    cp "${plan}" "${it}/execution_task_plan.jsonl"
    mkdir -p "${it}/${round}"
    t0=$(date +%s.%N)
    if [[ "${mode}" == served ]]; then
      campaign_planner_ask "${it}/sessions" ab \
        "$((10#${round#obligations-}))" "" "${it}/${round}" \
        2>>"${dir}/planner.log" || code=$?
    else
      "${planner[@]}" --round "$((10#${round#obligations-}))" \
        --output-dir "${it}/${round}" >/dev/null 2>>"${dir}/planner.log" \
        || code=$?
    fi
    printf '%s\t%s\n' "${round}" "$(awk -v a="${t0}" \
      -v b="$(date +%s.%N)" 'BEGIN {printf "%.2f", b - a}')" \
      >>"${dir}/walls.tsv"
    (( code == 0 )) || break
  done
  ab_landings_end
  return "${code}"
}

# The served planner of ab_landings, ended with its loop (or the loop's
# shell): a planner left serving holds a host's memory no ledger charges.
ab_served_jvm=""
ab_served_dir=""
ab_landings_end() {
  if [[ -n "${ab_served_jvm}" ]]; then
    kill "${ab_served_jvm}" 2>/dev/null
    wait "${ab_served_jvm}" 2>/dev/null
  fi
  [[ -z "${ab_served_dir}" ]] || rm -rf -- "${ab_served_dir}"
  ab_served_jvm=""
  ab_served_dir=""
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
# "CONFIRM refused:", or "CONFIRM refutes:" for the run as recorded) is an
# outcome, compared like any other.
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
  ab_out=${out}
  ab_side=${side}
  ab_case_id=${case_id}
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
  # Every stage after the seed's aggregation reads the declaration as the
  # recorded PLAN resolved it (campaign_plan_read): a sweep's "first", a
  # selector's k-th match among the observed target occurrences -- handed on
  # raw, a selector was matched again against every activation of its
  # region (zk-bugs-election-offer's "#2" named a create, not a getData).
  ab_declared=""
  [[ ! -d "${ab_acc_it}" ]] || ab_declared=$(jq -r '.target.occurrenceId' \
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
# open a region its v92 trace never addressed) -- or, with AB_FRESH_SLICE=1,
# over each side's own fresh slice: what a slice change does to the region
# plan and PLAN's closure.  The static pass is not deterministic, so by
# default neither side reads its own.
ab_seed() {
  local out=$1 case_id=$2 side fresh
  for side in "${AB_SIDES[@]}"; do
    ( ab_side_env "${out}" "${side}" "${case_id}"; ab_stage_seed_static ) &
  done
  wait
  fresh=${out}/baseline/${case_id}/SEED.static/out
  ab_side_env "${out}" baseline "${case_id}"
  ab_static=${ab_acc}
  [[ "${AB_FRESH_SLICE:-0}" != 1 ]] || ab_static=${fresh}
  ab_stage_seed_trace
  if [[ "${ab_static}" != "${fresh}" ]] && ! ab_ok SEED.trace \
      && [[ -s "${ab_acc}/runtime/runtime_trace.jsonl" ]] \
      && ab_ok SEED.static && [[ -s "${fresh}/static_scope_map.jsonl" ]]; then
    ab_static=${fresh}
    ab_stage_seed_trace
  fi
  ( ab_trace_rest ) &
  ( ab_side_env "${out}" candidate "${case_id}"
    [[ "${AB_FRESH_SLICE:-0}" != 1 ]] \
      || ab_static=${out}/candidate/${case_id}/SEED.static/out
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
  if [[ " ${AB_STAGES} " == *" SEED.static "* ]]; then
    for side in "${AB_SIDES[@]}"; do
      ( ab_side_env "${out}" "${side}" "${case_id}"; ab_stage_seed_static ) &
    done
  fi
  for side in "${AB_SIDES[@]}"; do
    ( ab_side_env "${out}" "${side}" "${case_id}"
      for chain in ${AB_STAGES}; do
        case "${chain}" in
          IMPORT) ab_stage_import ;;
          EXPLORE.N) ab_stage_exploren ;;
          EXPLORE.drift|EXPLORE.serve) ab_stage_landings "${chain}" ;;
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
  local baseline=${1:-} candidate=${2:-}
  (( ${#ab_rounds[@]} > 0 )) && [[ -f "${baseline}" && -f "${candidate}" ]] \
    || ab_die "usage: offline-ab.sh --round TAG|DIR [--round TAG|DIR]... \
<baseline-jar> <candidate-jar> [case...]"
  shift 2
  local -a cases=("$@") pids=() override
  local case_id dir side acc decl arg chain classpath repo base_repo
  AB_OUT=${AB_OUT:-${GC_BULK}/ab/$(date +%Y%m%d-%H%M%S)}
  AB_ACCEPT_ROOT=${AB_ACCEPT_ROOT:-${GC_OUT}}
  AB_STAGES=${AB_STAGES:-${AB_CHAINS[*]}}
  for chain in ${AB_STAGES}; do
    [[ " ${AB_CHAINS[*]} ${AB_EXTRA_CHAINS[*]} " == *" ${chain} "* ]] \
      || ab_die "AB_STAGES names ${chain}; the chains are ${AB_CHAINS[*]} \
${AB_EXTRA_CHAINS[*]}"
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
  printf 'AB_HEAP_MB=%q\nAB_SOLVE_JOBS=%q\nAB_STAGE_TIMEOUT_S=%q\nAB_STAGES=%q\nAB_HOSTS=%q\nAB_FRESH_SLICE=%q\n' \
    "${AB_HEAP_MB:-8192}" "${AB_SOLVE_JOBS:-1}" "${AB_STAGE_TIMEOUT_S:-1800}" \
    "${AB_STAGES}" "${AB_HOSTS:-${LIFTS}}" "${AB_FRESH_SLICE:-0}" \
    >"${AB_OUT}/env.sh"
  [[ -z "${AB_Z3:-}" ]] || printf 'AB_Z3=%q\n' "${AB_Z3}" >>"${AB_OUT}/env.sh"
  printf '%s\n' ${AB_STAGES} >"${AB_OUT}/chains.txt"
  printf 'baseline\t%s\t%s\ncandidate\t%s\t%s\n' \
    "$(readlink -f "${baseline}")" "${base_repo}" \
    "$(readlink -f "${candidate}")" "${ab_self_repo}" >"${AB_OUT}/sides.tsv"

  # Each case: its recorded run, each side's declarations of it, and the
  # config run_engine.sh reads -- with the classpath the run froze, when it
  # states one.
  for case_id in "${cases[@]}"; do
    # The static pass alone reads no recording: a case no round recorded
    # runs against none (its base~acc is "-").
    acc=$(ab_recorded_run "${case_id}") || acc=-
    [[ "${acc}" != - || "${AB_STAGES}" == SEED.static ]] \
      || ab_die "no round of ${ab_rounds[*]} recorded ${case_id}"
    printf '%s\t%s\n' "${case_id}" "${acc}" >>"${AB_OUT}/accepted.tsv"
    classpath=$(ab_recorded_classpath "${acc}")
    override=()
    [[ -z "${classpath}" ]] || override=("CAUSYNTH_CLASSPATH_OVERRIDE=${classpath}")
    for side in "${AB_SIDES[@]}"; do
      repo=${ab_self_repo}
      [[ "${side}" == candidate ]] || repo=${base_repo}
      read -r decl arg < <(case_dir_of "${repo}" "${case_id}") \
        || ab_die "${repo} declares no experiment for ${case_id}"
      dir=${AB_OUT}/${side}/${case_id}
      mkdir -p "${dir}"
      printf '%s %s %s %s\n' "${acc}" "${decl}" "${arg}" "${repo}" \
        >"${dir}/inputs.txt"
      # run.sh derives the target spec of a case its tree marks into the
      # output directory it is given (declared-target.yaml): one no stage
      # clears, or SEED.static's fresh directory deletes the spec it reads.
      (cd "${decl}" && env -i HOME="${HOME}" PATH="${PATH}" \
          CAUSYNTH_OUTPUT_DIR="${dir}/declared" "${override[@]}" \
          bash "${repo}/experiments/lib/run.sh" "${decl}" \
          "$([[ ${arg} == - ]] || echo "${arg}")" config) \
        >"${dir}/config.txt" 2>"${dir}/config.log" \
        || ab_die "${case_id}: run.sh config failed (${dir}/config.log)"
    done
  done

  # One task per case, heaviest corpus first, all here: each places its
  # JVMs (ab_java).
  ab_log "offline A/B: ${#cases[@]} case(s) [${AB_STAGES}] from rounds \
${ab_rounds[*]} -> ${AB_OUT}"
  trap 'kill ${pids[*]} 2>/dev/null; exit 130' INT TERM
  for case_id in $(for case_id in "${cases[@]}"; do
        acc=$(awk -F'\t' -v c="${case_id}" '$1 == c {print $2}' "${AB_OUT}/accepted.tsv")
        # A recording no session came of (a SEED-only run) weighs 0.
        printf '%s %s\n' "$(du -sk "${acc}/schedule/iteration-0000/sessions/" \
          2>/dev/null | cut -f1 | grep . || echo 0)" "${case_id}"
      done | sort -rn | awk '{print $2}'); do
    bash "${ab_self}" --task "${AB_OUT}" "${case_id}" \
      >"${AB_OUT}/logs/${case_id}.log" 2>&1 &
    pids+=("$!")
  done
  wait
  trap - INT TERM
  ab_log "stages done in $(( SECONDS - t0 )) s; comparing"
  python3 "$(dirname "${ab_self}")/ab_compare.py" "${AB_OUT}" "${cases[@]}"
  local verdict=$?
  ab_log "offline A/B finished in $(( SECONDS - t0 )) s: $(case ${verdict} in
    0) echo identical ;; 1) echo DIFFERS ;; *) echo 'NOT CHECKED' ;; esac)"
  return "${verdict}"
}

# Sourced (the shell test), it only defines.
[[ "${BASH_SOURCE[0]}" == "$0" ]] || return 0
if [[ "${1:-}" == --task ]]; then
  shift
  ab_task "$@"
elif [[ "${1:-}" == --landings ]]; then
  shift
  ab_landings "$@"
else
  ab_main "$@"
fi

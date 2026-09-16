#!/usr/bin/env bash
# Parse-before-execute guard.  bash reads a script incrementally from its file
# descriptor, so overwriting this file in place while a gate run is executing it
# (e.g. `cp -p` of an identical copy over it) makes bash resume at a stale byte
# offset in the new content and execute a word fragment -- the run then aborts
# with a bogus "<fragment>: command not found" at a line number that no longer
# corresponds to anything, after a complete DIGESTS.txt has already been written.
# Wrapping the whole body in one { ... } group forces bash to parse the entire
# file before running any of it.  Nothing else changes: the group is not a
# subshell, so variables, functions, traps, `exit` and the exit status all behave
# exactly as before.  Do not remove the braces.
{
# gate3.sh <jar> <outdir>
#
# One offline regression gate for GraphChecker cleanup round 3.  It re-runs the
# four offline owners of the engine -- explore.ExploreMain, compose.ComposeMain,
# runtime.CausynthTraceRecorder, plan.ConcolicScheduler and the static pass
# GraphCheckerMain -- over two frozen corpora, and writes one digest line per
# artifact.  No workload is executed, no campaign is started, nothing under a
# corpus or under a hadoop tree is written.
#
# Every case-specific value (anchor, bounds, root domains, symbolic inputs,
# trace test, solver limits) is read from the case's own workflow.properties,
# whose sha256 is checked against the sha256 the corpus recorded in its
# iteration_manifest.json provenance.  Nothing is hard-coded per case.
set -euo pipefail

usage() { echo "usage: gate3.sh <jar> <outdir>" >&2; exit 2; }
[[ $# -eq 2 ]] || usage
JAR=$(readlink -f -- "$1") || usage
OUT=$2
[[ -f "${JAR}" ]] || { echo "no such jar: ${JAR}" >&2; exit 2; }

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
NORM="${HERE}/norm.py"

# --- environment (configuration, never engine policy) ----------------------
SPO=${GATE3_SPO:-/tmp/claude-20003/-opt-GraphChecker/99c84a54-86ac-44a4-a030-760f664ae2a1/scratchpad}
MY=${GATE3_MY:-/tmp/claude-20003/-opt-GraphChecker/10153a9a-290a-45d1-b3c9-072f259e090e/scratchpad}
REPO=${GATE3_REPO:-${SPO}/wt-stage}
JAVA=${GATE3_JAVA:-/usr/lib/jvm/java-8-openjdk-amd64/bin/java}
Z3=${GATE3_Z3:-/usr/local/bin/z3}
XMX=${GATE3_XMX:--Xmx8g}
SUBGATES=${GATE3_SUBGATES:-wave0 compose plan static}
STATIC_BUDGET=${GATE3_STATIC_BUDGET:-900}
# r3/PC2: run wave0 and the scheduler against a scope map produced by the jar
# under test instead of the corpus's, so a map that GAINS rows can be shown
# not to change wave 0.  <dir>/<corpus id>/static_scope_map.jsonl.
SCOPE_MAP_DIR=${GATE3_SCOPE_MAP_DIR:-}

# corpus id : corpus out dir : experiment dir
CORPORA=${GATE3_CORPORA:-"17960|${MY}/final-f651c4879/out/hdfs-17960|${REPO}/experiments/hadoop/hdfs-17960
11741|${MY}/final-e33e72351-11741/out/hdfs-11741|${REPO}/experiments/hadoop/hdfs-11741"}

for tool in "${JAVA}" "${Z3}" /usr/bin/jq /usr/bin/python3; do
  [[ -x "${tool}" ]] || { echo "missing tool: ${tool}" >&2; exit 2; }
done
[[ -f "${NORM}" ]] || { echo "missing normaliser: ${NORM}" >&2; exit 2; }

mkdir -p "${OUT}"
OUT=$(cd "${OUT}" && pwd -P)
DIGESTS="${OUT}/DIGESTS.txt"
TIMES="${OUT}/TIMES.txt"
: >"${DIGESTS}"
: >"${TIMES}"
mkdir -p "${OUT}/.sorttmp"

# --- helpers ---------------------------------------------------------------
row() { printf '%s %s %s %s %s\n' "$1" "$2" "$3" "$4" "$5" >>"${DIGESTS}"; }
skip() { row "$1" "$2" "$3" SKIPPED "$4"; echo "  SKIPPED ${1}/${2}/${3}: $4" >&2; }
timed() { printf '%s\t%s\t%s\n' "$1" "$2" "$3" >>"${TIMES}"; }

# The engine's offline JVMs, as run_engine.sh's run_java_main launches them:
# the case's java_bin (stock JDK 8 + -Xmx8g) and the case's loop bound, with
# every path absolute.  nice(1) keeps the gate off a running campaign's back.
gc_java() { # <extra-classpath-or-empty> <main-class> <args...>
  local extra=$1 main=$2; shift 2
  local cp="${JAR}"
  [[ -z "${extra}" ]] || cp="${JAR}:${extra}"
  # run_engine.sh:run_java_main passes the case's declaration to every stage
  # under this key; the region finalizer's demand walk reads it.
  local decl=()
  [[ -z "${SYMBOLIC_INPUTS:-}" ]] \
    || decl=("-Dcausynth.symbolic.inputs=${SYMBOLIC_INPUTS}")
  ( cd "${OUT}" && nice -n 10 "${JAVA}" "${XMX}" \
      "-Dcausynth.loop.default.bound=${LOOP_BOUND}" \
      "${decl[@]+"${decl[@]}"}" \
      -cp "${cp}" "${main}" "$@" </dev/null )
}

prop() { # <key> -- last assignment wins, exactly as load_config_file does
  sed -n "s/^$1=//p" "${CASE_DIR}/workflow.properties" | tail -n 1
}
resolve() { # @config/x -> <case dir>/x ; project-relative -> <repo>/x
  local raw=$1
  case "${raw}" in
    "") ;;
    /*) printf '%s\n' "${raw}" ;;
    @config/*) printf '%s\n' "${CASE_DIR}/${raw#@config/}" ;;
    @project/*) printf '%s\n' "${REPO}/${raw#@project/}" ;;
    *) printf '%s\n' "${REPO}/${raw}" ;;
  esac
}

# Normalise then hash.  Masks remove the only run-local text in these
# artifacts (the gate's own output directory and the jar under test); --strip
# removes the fields that two runs of the identical inputs disagree on.
STRIP_JSON=${GATE3_STRIP:-}
digest_norm() { # <file> <jsonl:0|1>
  local file=$1 jsonl=$2
  local -a flags=(--mask "${OUT}=<OUT>" --mask "${JAR}=<JAR>"
                  --mask "${CORPUS}=<CORPUS>" --mask "${CASE_DIR}=<CASE>")
  [[ "${jsonl}" == 1 ]] && flags+=(--jsonl)
  [[ -z "${STRIP_JSON}" ]] || flags+=(--strip "${STRIP_JSON}")
  python3 "${NORM}" "${file}" "${flags[@]}" \
    | LC_ALL=C sort -S 128M -T "${OUT}/.sorttmp" \
    | sha256sum | cut -d' ' -f1
}
digest_raw() { sha256sum "$1" | cut -d' ' -f1; }

# --- per-corpus ------------------------------------------------------------
while IFS='|' read -r ID CORPUS CASE_DIR; do
  [[ -n "${ID}" ]] || continue
  echo "== corpus ${ID}"
  [[ -d "${CORPUS}" ]] || { echo "no such corpus: ${CORPUS}" >&2; exit 2; }
  [[ -f "${CASE_DIR}/workflow.properties" ]] \
    || { echo "no such case: ${CASE_DIR}" >&2; exit 2; }

  SCOPE_MAP="${CORPUS}/static_scope_map.jsonl"
  [[ -z "${SCOPE_MAP_DIR}" ]] \
    || SCOPE_MAP="${SCOPE_MAP_DIR}/${ID}/static_scope_map.jsonl"
  [[ -f "${SCOPE_MAP}" ]] || { echo "no such scope map: ${SCOPE_MAP}" >&2; exit 2; }
  IT="${CORPUS}/schedule/iteration-0000"
  SESSIONS="${IT}/sessions"
  MANIFEST="${CORPUS}/schedule/final/candidate_composition_manifest.json"
  W0M="${IT}/obligations-0000/explore_manifest.json"

  # Which declarations this gate is running against, checked against the
  # sha256 the corpus recorded for the same file in its own provenance.  A
  # NO here is why a sub-gate can differ from the kept run without the
  # engine having changed at all.
  meta_decl() { # <provenance key or "-"> <file>
    local key=$1 file=$2 now run
    [[ -n "${file}" && -f "${file}" ]] || return 0
    now=$(sha256sum "${file}" | cut -d' ' -f1)
    run=""
    [[ "${key}" == "-" ]] || run=$(jq -r --arg k "${key}" \
      '.provenance[$k].sha256 // ""' "${IT}/iteration_manifest.json")
    if [[ -z "${run}" ]]; then
      row "${ID}" meta "$(basename "${file}")" "${now}" \
        "matches-corpus=UNRECORDED"
    elif [[ "${now}" == "${run}" ]]; then
      row "${ID}" meta "$(basename "${file}")" "${now}" "matches-corpus=yes"
    else
      row "${ID}" meta "$(basename "${file}")" "${now}" \
        "matches-corpus=NO(corpus=${run})"
      echo "  WARNING ${ID}: $(basename "${file}") differs from the corpus run" >&2
    fi
  }
  meta_decl config "${CASE_DIR}/workflow.properties"

  ANCHOR=$(prop declared_target_occurrence)
  [[ -n "${ANCHOR}" ]] || { echo "${ID}: no declared_target_occurrence" >&2; exit 2; }
  LOOP_BOUND=$(prop causynth_loop_default_bound)
  ROOT_DOMAINS=$(resolve "$(prop causynth_root_domains)")
  SYMBOLIC_INPUTS=$(resolve "$(prop causynth_symbolic_inputs)")
  TARGET_SPEC=$(resolve "$(prop causynth_target_spec)")
  LOOP_BOUNDS=$(resolve "$(prop causynth_loop_bounds)")
  COMM_MAPPINGS=$(resolve "$(prop causynth_communication_mappings)")
  TRACE_TEST=$(prop trace_test)
  MAX_JOBS=$(prop schedule_max_jobs)
  MAX_VALUATIONS=$(prop compose_max_valuations)
  SOLVER_TIMEOUT=$(prop solver_timeout_ms)
  MAX_TASKS=$(prop region_path_max_tasks)
  MAX_PATHS=$(prop region_path_max_paths_per_region)
  MAX_FLIPS=$(prop region_path_max_flips_per_path)
  PROJECT_CLASSES=$(prop project_classes_dir)
  EPOCH=$(jq -r '.topologyEpoch // "iteration-0000"' "${W0M}" 2>/dev/null \
    || echo iteration-0000)
  meta_decl targetSpec "${TARGET_SPEC}"
  meta_decl loopBounds "${LOOP_BOUNDS}"
  meta_decl symbolicInputs "${SYMBOLIC_INPUTS}"
  meta_decl communicationMappings "${COMM_MAPPINGS}"
  meta_decl - "${ROOT_DOMAINS}"
  row "${ID}" meta anchor "$(printf '%s' "${ANCHOR}" | sha256sum | cut -d' ' -f1)" \
    "epoch=${EPOCH} loopBound=${LOOP_BOUND}"

  # =======================================================================
  # wave0 -- explore.ExploreMain, wave 0 of iteration-0000
  # =======================================================================
  if [[ " ${SUBGATES} " == *" wave0 "* ]]; then
    W="${OUT}/${ID}/wave0"
    rm -rf -- "${W}"; mkdir -p "${W}/sessions" "${W}/obligations-0000"
    # The session set wave 0 actually read: the seed replay only.  Every other
    # session in the kept corpus is named after a wave-0 obligation and was
    # written by that obligation's worker, after this JVM had already run.
    seeds=0
    for s in "${SESSIONS}"/seed-result-*; do
      [[ -d "${s}" ]] || continue
      ln -s "${s}" "${W}/sessions/$(basename "${s}")"
      seeds=$((seeds + 1))
    done
    if [[ "${seeds}" -eq 0 ]]; then
      skip "${ID}" wave0 obligations.jsonl "no seed-result-* session under ${SESSIONS}"
    else
      : >"${W}/obligation_results.jsonl"
      declare -a EARGS=(
        --sessions "${W}/sessions"
        --results "${W}/obligation_results.jsonl"
        --static-scope-map "${SCOPE_MAP}"
        --topology-epoch "${EPOCH}"
        --wave 0
        --output-dir "${W}/obligations-0000"
        --target-occurrence "${ANCHOR}"
      )
      [[ -z "${ROOT_DOMAINS}" ]] || EARGS+=(--root-domains "${ROOT_DOMAINS}")
      [[ -z "${MAX_PATHS}" ]] || EARGS+=(--max-paths-per-region "${MAX_PATHS}")
      [[ -z "${MAX_FLIPS}" ]] || EARGS+=(--max-flips-per-path "${MAX_FLIPS}")
      [[ -z "${MAX_TASKS}" ]] || EARGS+=(--max-tasks "${MAX_TASKS}")
      t0=$(date +%s)
      status=0
      gc_java "" edu.uva.liftlab.graphchecker.explore.ExploreMain \
        "${EARGS[@]}" >"${W}/stdout.log" 2>"${W}/stderr.log" || status=$?
      timed "${ID}" wave0 "$(( $(date +%s) - t0 ))s"
      if [[ "${status}" -ne 0 ]]; then
        skip "${ID}" wave0 obligations.jsonl "ExploreMain exit ${status}, see ${W}/stderr.log"
      else
        O="${W}/obligations-0000"
        n=$(wc -l <"${O}/obligations.jsonl" | tr -d ' ')
        row "${ID}" wave0 obligations.jsonl "$(digest_norm "${O}/obligations.jsonl" 1)" \
          "obligations=${n} sessionsRead=${seeds}"
        row "${ID}" wave0 explore_manifest.json \
          "$(digest_norm "${O}/explore_manifest.json" 0)" \
          "$(jq -r '"state="+(.state//"")+" tasks="+((.tasks//0)|tostring)
             +" proposed="+((.proposed//0)|tostring)
             +" answered="+((.answered//0)|tostring)
             +" gaps="+((.gaps//{})|to_entries|map(.key+":"+(.value|tostring))|join(",")|
                if .=="" then "none" else . end)' "${O}/explore_manifest.json")"
        for extra in tasks.jsonl gaps.jsonl; do
          [[ -f "${O}/${extra}" ]] || continue
          row "${ID}" wave0 "${extra}" "$(digest_norm "${O}/${extra}" 1)" \
            "rows=$(wc -l <"${O}/${extra}" | tr -d ' ')"
        done
      fi
    fi
  fi

  # =======================================================================
  # compose -- compose.ComposeMain over every session of iteration-0000
  # =======================================================================
  if [[ " ${SUBGATES} " == *" compose "* ]]; then
    C="${OUT}/${ID}/compose"
    rm -rf -- "${C}"; mkdir -p "${C}"
    declare -a CARGS=(
      --sessions "${SESSIONS}"
      --output "${C}/candidate.smt2"
      --manifest "${C}/candidate_composition_manifest.json"
      --solver-timeout-ms "${SOLVER_TIMEOUT}"
      --max-valuations "${MAX_VALUATIONS}"
      --z3 "${Z3}"
      --anchor "${ANCHOR}"
    )
    [[ -z "${ROOT_DOMAINS}" ]] || CARGS+=(--root-domains "${ROOT_DOMAINS}")
    t0=$(date +%s)
    status=0
    gc_java "" edu.uva.liftlab.graphchecker.compose.ComposeMain \
      "${CARGS[@]}" >"${C}/compose.log" 2>&1 || status=$?
    timed "${ID}" compose "$(( $(date +%s) - t0 ))s"
    if [[ "${status}" -ne 0 || ! -s "${C}/candidate.smt2" ]]; then
      skip "${ID}" compose candidate.smt2 "ComposeMain exit ${status}, see ${C}/compose.log"
    else
      M="${C}/candidate_composition_manifest.json"
      row "${ID}" compose candidate.smt2 "$(digest_raw "${C}/candidate.smt2")" \
        "bytes=$(stat -c '%s' "${C}/candidate.smt2") asserts=$(grep -c '^(assert' "${C}/candidate.smt2" || true)"
      row "${ID}" compose manifest "$(digest_norm "${M}" 0)" \
        "$(jq -r '"paths="+((.paths//[])|length|tostring)
           +" families="+((.families//[])|length|tostring)
           +" roots="+((.roots//[])|length|tostring)
           +" valuations="+((.valuations//[])|length|tostring)
           +" gaps="+((.gaps//[])|length|tostring)
           +" finalStatus="+(.finalStatus//"")' "${M}")"
      row "${ID}" compose claim "$(jq -r '
          [.solver.campaignClaim.claim // "",
           .solver.campaignClaim.findingKind // "",
           ((.solver.campaignClaim.movedRoots // {})|to_entries
             |map(.key+"="+(.value|tostring))|sort|join(";")),
           (.solver.campaignClaim.valuationOrdinal // -1 |tostring),
           (.solver.campaignClaim.polarityDecides // false |tostring),
           (.solver.state // ""), (.solver.reachability // "")]
          |join("|")' "${M}" | sha256sum | cut -d' ' -f1)" \
        "$(jq -r '"claim="+(.solver.campaignClaim.claim//"")
           +" findingKind="+(.solver.campaignClaim.findingKind//"")
           +" movedRoots="+(((.solver.campaignClaim.movedRoots//{})|to_entries
                |map(.key+"="+(.value|tostring))|sort|join(";"))
                |if .=="" then "none" else . end)
           +" valuationOrdinal="+((.solver.campaignClaim.valuationOrdinal//-1)|tostring)
           +" polarityDecides="+((.solver.campaignClaim.polarityDecides//false)|tostring)
           +" z3="+(.solver.state//"")+"/"+(.solver.reachability//"")
           +" blockers="+((.solver.campaignClaim.blockerCount//0)|tostring)' "${M}")"
    fi
  fi

  # =======================================================================
  # plan -- runtime.CausynthTraceRecorder aggregation, then
  #         plan.ConcolicScheduler, over the kept seed recording
  # =======================================================================
  if [[ " ${SUBGATES} " == *" plan "* ]]; then
    P="${OUT}/${ID}/plan"
    rm -rf -- "${P}"; mkdir -p "${P}/trace"
    trace="${CORPUS}/runtime/runtime_trace.jsonl"
    tman="${CORPUS}/runtime/streaming_trace_manifest.json"
    skel="${CORPUS}/runtime/skeleton-pass/region_skeletons.jsonl"
    graph="${CORPUS}/candidate_dataflow_edges.jsonl.gz"
    missing=""
    for f in "${trace}" "${tman}" "${skel}" "${graph}"; do
      [[ -s "${f}" ]] || missing="${missing}${missing:+,}${f}"
    done
    if [[ -n "${missing}" ]]; then
      skip "${ID}" plan concolic_region_plan.jsonl "pruned input(s): ${missing}"
      skip "${ID}" plan execution_task_plan.jsonl "pruned input(s): ${missing}"
    else
      # The recorder reads (and the engine lets it rewrite) its trace
      # directory, so the kept recording is copied out first: nothing under a
      # corpus is ever written by this gate.
      # The kept corpora are read-only; the recorder's trace directory is
      # its own working directory, so the copies must be writable here.
      cp "${trace}" "${tman}" "${P}/trace/"
      chmod u+w "${P}/trace/$(basename "${trace}")" \
        "${P}/trace/$(basename "${tman}")"
      # run_java_main puts the production classes on the recorder's classpath
      # for boundary-scalar validation; the case states them the same way.
      pcp=""
      if [[ -x "${CASE_DIR}/classpath.sh" ]]; then
        pcp=$("${CASE_DIR}/classpath.sh" 2>"${P}/classpath.err") || pcp=""
      fi
      if [[ -z "${pcp}" ]]; then
        pcp="$(resolve "${PROJECT_CLASSES}"):$(resolve "$(prop project_test_classes_dir)")"
      fi
      # r3/PC item (a): the REGION_SKELETON aggregation publishes the gaps
      # pass 1 stated, and the REGION_STATE aggregation -- the pass that
      # writes the plan -- files them with its own, so pass 1 is re-run here
      # exactly as run_engine.sh:do_regions runs it.  A jar that predates the
      # channel accepts and ignores --recording-gaps and writes no gap
      # artifact, so an empty one stands in and the baseline stays runnable.
      mkdir -p "${P}/strace" "${P}/skeleton-pass"
      cp -p "${CORPUS}/runtime/skeleton-pass/runtime_trace.jsonl" \
            "${CORPUS}/runtime/skeleton-pass/streaming_trace_manifest.json" \
            "${P}/strace/"
      t0=$(date +%s)
      status=0
      gc_java "${pcp}" edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder \
        --trace-dir "${P}/strace" \
        --region-skeletons "${CORPUS}/region_skeletons.jsonl.gz" \
        --region-skeleton-only true \
        --output-dir "${P}/skeleton-pass" \
        --test "${TRACE_TEST}" \
        >"${P}/skeleton.log" 2>&1 || status=$?
      timed "${ID}" plan.skeleton "$(( $(date +%s) - t0 ))s"
      RG="${P}/skeleton-pass/recording_gaps.jsonl"
      if [[ -f "${RG}" ]]; then
        row "${ID}" plan recording_gaps.jsonl "$(digest_raw "${RG}")" \
          "rows=$(wc -l <"${RG}" | tr -d ' ')"
      else
        : >"${RG}"
        row "${ID}" plan recording_gaps.jsonl ABSENT "this jar writes none"
      fi
      if [[ -s "${P}/skeleton-pass/region_skeletons.jsonl" ]]; then
        row "${ID}" plan region_skeletons.jsonl \
          "$(digest_norm "${P}/skeleton-pass/region_skeletons.jsonl" 1)" \
          "rows=$(wc -l <"${P}/skeleton-pass/region_skeletons.jsonl" | tr -d ' ') sameAsCorpus=$(cmp -s "${P}/skeleton-pass/region_skeletons.jsonl" "${skel}" && echo yes || echo NO)"
      fi
      t0=$(date +%s)
      status=0
      gc_java "${pcp}" edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder \
        --trace-dir "${P}/trace" \
        --candidate-graph "${graph}" \
        --region-skeletons "${skel}" \
        --static-scope-map "${SCOPE_MAP}" \
        --refined-graph "${P}/refined_dataflow_edges.jsonl.gz" \
        --recording-gaps "${RG}" \
        --test "${TRACE_TEST}" \
        --output-dir "${P}" \
        >"${P}/aggregate.log" 2>&1 || status=$?
      timed "${ID}" plan.aggregate "$(( $(date +%s) - t0 ))s"
      RP="${P}/concolic_region_plan.jsonl"
      if [[ "${status}" -ne 0 || ! -s "${RP}" ]]; then
        skip "${ID}" plan concolic_region_plan.jsonl \
          "CausynthTraceRecorder exit ${status}, see ${P}/aggregate.log"
        skip "${ID}" plan execution_task_plan.jsonl \
          "no region plan to schedule"
      else
        row "${ID}" plan concolic_region_plan.jsonl "$(digest_norm "${RP}" 1)" \
          "rows=$(wc -l <"${RP}" | tr -d ' ')"
        row "${ID}" plan refined_dataflow_edges "$(zcat "${P}/refined_dataflow_edges.jsonl.gz" | LC_ALL=C sort -S 128M -T "${OUT}/.sorttmp" | sha256sum | cut -d' ' -f1)" \
          "rows=$(zcat "${P}/refined_dataflow_edges.jsonl.gz" | wc -l | tr -d ' ')"
        S="${P}/schedule"
        mkdir -p "${S}"
        declare -a SARGS=(
          --region-plan "${RP}"
          --output-dir "${S}"
          --candidate-graph "${graph}"
          --static-scope-map "${SCOPE_MAP}"
          --max-jobs "${MAX_JOBS}"
          --closure-mode candidate
        )
        [[ -z "${SYMBOLIC_INPUTS}" ]] || SARGS+=(--symbolic-inputs "${SYMBOLIC_INPUTS}")
        SARGS+=(--target-occurrence "${ANCHOR}")
        t0=$(date +%s)
        status=0
        gc_java "" edu.uva.liftlab.graphchecker.plan.ConcolicScheduler \
          "${SARGS[@]}" >"${P}/schedule.log" 2>&1 || status=$?
        timed "${ID}" plan.schedule "$(( $(date +%s) - t0 ))s"
        TP="${S}/execution_task_plan.jsonl"
        IX="${S}/runtime_workflow_schedule_index.json"
        if [[ "${status}" -ne 0 || ! -s "${TP}" ]]; then
          skip "${ID}" plan execution_task_plan.jsonl \
            "ConcolicScheduler exit ${status}, see ${P}/schedule.log"
        else
          row "${ID}" plan execution_task_plan.jsonl "$(digest_norm "${TP}" 1)" \
            "rows=$(wc -l <"${TP}" | tr -d ' ') symbolize=$(python3 - "${TP}" <<'PY'
import json, sys, collections
kinds = collections.Counter()
total = 0
with open(sys.argv[1]) as handle:
    for line in handle:
        line = line.strip()
        if not line:
            continue
        for action in json.loads(line).get("inputActions") or []:
            if str(action.get("mode", "")).upper() != "SYMBOLIC":
                continue
            total += 1
            kinds[str(action.get("rootKind")
                      or action.get("sourceKind") or "?")] += 1
print("%d[%s]" % (total, ",".join("%s:%d" % kv for kv in sorted(kinds.items()))))
PY
)"
          [[ -s "${IX}" ]] && row "${ID}" plan schedule_index.json \
            "$(digest_norm "${IX}" 0)" \
            "$(jq -r '"members="+((.members//[])|length|tostring)
               +" target="+((.target.taskId)//"")' "${IX}")"
        fi
      fi
    fi
  fi

  # =======================================================================
  # static -- the SEED stage's first do_analyze: GraphCheckerMain over the
  #           case's frozen production classes (read-only), no workload
  # =======================================================================
  if [[ " ${SUBGATES} " == *" static "* ]]; then
    T="${OUT}/${ID}/static"
    rm -rf -- "${T}"; mkdir -p "${T}/out" "${T}/instrumented-classes"
    pcd=$(resolve "${PROJECT_CLASSES}")
    pcp=""
    if [[ -x "${CASE_DIR}/classpath.sh" ]]; then
      pcp=$("${CASE_DIR}/classpath.sh" 2>"${T}/classpath.err") || pcp=""
    fi
    if [[ -z "${pcp}" ]]; then
      pcp="${pcd}:$(resolve "$(prop project_test_classes_dir)")"
    fi
    if [[ ! -d "${pcd}" ]]; then
      skip "${ID}" static static_scope_map.jsonl "no production classes at ${pcd}"
    else
      declare -a SPROPS=(
        "-Dcausynth.output.dir=${T}/out"
        "-Dcausynth.target.spec=${TARGET_SPEC}"
        "-Dcausynth.trace.test=${TRACE_TEST}"
        "-Dcausynth.loop.bounds=${LOOP_BOUNDS}"
        "-Dcausynth.loop.default.bound=${LOOP_BOUND}"
        "-Dcausynth.region.skeletons=${T}/out/runtime/skeleton-pass/region_skeletons.jsonl"
      )
      [[ -z "${COMM_MAPPINGS}" ]] \
        || SPROPS+=("-Dcausynth.communication.mappings=${COMM_MAPPINGS}")
      [[ -z "${SYMBOLIC_INPUTS}" ]] \
        || SPROPS+=("-Dcausynth.symbolic.inputs=${SYMBOLIC_INPUTS}")
      t0=$(date +%s)
      status=0
      ( cd "${OUT}" && timeout "${STATIC_BUDGET}" nice -n 10 "${JAVA}" "${XMX}" \
          "${SPROPS[@]}" -cp "${JAR}:${pcp}" \
          edu.uva.liftlab.graphchecker.GraphCheckerMain \
          -i "${pcd}" -x "${pcp}" \
          -o "${T}/instrumented-classes" </dev/null ) \
        >"${T}/static.log" 2>&1 || status=$?
      timed "${ID}" static "$(( $(date +%s) - t0 ))s"
      if [[ "${status}" -ne 0 ]]; then
        skip "${ID}" static static_scope_map.jsonl \
          "GraphCheckerMain exit ${status} (124 = over ${STATIC_BUDGET}s), see ${T}/static.log"
      else
        ssm="${T}/out/static_scope_map.jsonl"
        if [[ -s "${ssm}" ]]; then
          row "${ID}" static static_scope_map.jsonl "$(digest_norm "${ssm}" 1)" \
            "rows=$(wc -l <"${ssm}" | tr -d ' ')"
        else
          skip "${ID}" static static_scope_map.jsonl "the pass wrote no map"
        fi
        for gz in candidate_dataflow_edges region_skeletons communication_gaps; do
          f="${T}/out/${gz}.jsonl.gz"
          if [[ -s "${f}" ]]; then
            row "${ID}" static "${gz}.jsonl.gz" \
              "$(zcat "${f}" | LC_ALL=C sort -S 128M -T "${OUT}/.sorttmp" | sha256sum | cut -d' ' -f1)" \
              "rows=$(zcat "${f}" | wc -l | tr -d ' ')"
          else
            skip "${ID}" static "${gz}.jsonl.gz" "the pass wrote no such file"
          fi
        done
      fi
    fi
  fi
done <<<"${CORPORA}"

LC_ALL=C sort -o "${DIGESTS}" "${DIGESTS}"
rm -rf -- "${OUT}/.sorttmp"
echo
echo "== ${DIGESTS}"
cat "${DIGESTS}"
echo
echo "== ${TIMES}"
cat "${TIMES}"
}

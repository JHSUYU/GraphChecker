#!/usr/bin/env bash
set -euo pipefail
lib=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
source "${lib}/case-env.sh" "${1:?missing case directory}" "${2-}"
jar=${GRAPHCHECKER_JAR:?missing GraphChecker jar}
cp=$(bash "${lib}/classpath.sh" "${case_dir}" "${case_id}")
scratch_owned=""

if [[ -n ${CAUSYNTH_CONCOLIC_TASK_PLAN:-} ]]; then
  classes=${CAUSYNTH_CONCOLIC_CLASSES:?missing concolic classes}
  work=${CAUSYNTH_CONCOLIC_WORKER_DIR:?missing worker directory}
  results=${CAUSYNTH_CONCOLIC_RESULTS:?missing result path}
  jdk=${CAUSYNTH_CUSTOM_JDK_HOME:?missing custom JDK}
  properties=(
    "-Dcausynth.concolic.task.plan=${CAUSYNTH_CONCOLIC_TASK_PLAN}"
    "-Dcausynth.concolic.task.id=${CAUSYNTH_CONCOLIC_TASK_ID}"
    "-Dcausynth.concolic.results=${results}"
    "-Dcausynth.concolic.campaign.max.tasks=${CAUSYNTH_CONCOLIC_MAX_TASKS}"
  )
else
  classes=${CAUSYNTH_INSTRUMENTED_CLASSES_DIR:?missing instrumented classes}
  work=$(mktemp -d "/tmp/${tag}-trace.XXXXXX")
  scratch_owned=${work}
  trace=${CAUSYNTH_TRACE_OUTPUT_DIR:?missing trace output directory}
  jdk=/usr/lib/jvm/java-8-openjdk-amd64
  properties=(
    "-Dcausynth.trace.test=${test_name}"
    "-Dcausynth.trace.start.paused=true"
    ${CAUSYNTH_PLANT:+"-javaagent:${jar}" "-Dcausynth.plant=${CAUSYNTH_PLANT}"}
    ${CAUSYNTH_ORDER_TIMEOUT_MS:+"-Dcausynth.confirm.order.timeout.ms=${CAUSYNTH_ORDER_TIMEOUT_MS}"})
fi

[[ -z ${recording_window} ]] \
  || properties+=("-Dcausynth.recording.window=${recording_window}")
properties+=("-Dcausynth.window.ms.file=${trace:-${work}}/window_ms")
[[ -z ${CAUSYNTH_VIEW_HOLD_MAX_MS:-} ]] \
  || properties+=("-Dcausynth.view.hold.max.ms=${CAUSYNTH_VIEW_HOLD_MAX_MS}")
[[ -z ${CAUSYNTH_VIEW_HOLD_MAX_RECORDED_MS:-} ]] \
  || properties+=("-Dcausynth.view.hold.max.recorded.ms=${CAUSYNTH_VIEW_HOLD_MAX_RECORDED_MS}")

mkdir -p ${trace:+"${trace}"} ${results:+"$(dirname "${results}")"}

remove_local_scratch() {
  [[ -z ${scratch_owned} ]] || rm -rf -- "${scratch_owned}"
}
trap remove_local_scratch EXIT
tmpdir="${work}/temp"
datadir="${work}/data"
if [[ -n ${CAUSYNTH_LOCAL_SCRATCH:-} ]]; then
  mkdir -p "${CAUSYNTH_LOCAL_SCRATCH}"
  scratch_owned=$(mktemp -d "${CAUSYNTH_LOCAL_SCRATCH}/replay.XXXXXXXX")
  tmpdir="${scratch_owned}/temp"
  datadir="${scratch_owned}/data"
fi
mkdir -p "${tmpdir}" "${datadir}"
system_jvm_properties "${tmpdir}" "${datadir}"
if [[ ${system_jar_first} == true ]]; then
  classpath="${classes}:${jar}:${cp}"
else
  classpath="${classes}:${cp}:${jar}"
fi

extra=()
[[ -z ${CAUSYNTH_WORKLOAD_JAVA_OPTS:-} ]] \
  || read -r -a extra <<<"${CAUSYNTH_WORKLOAD_JAVA_OPTS}"

charged_mb=${CAUSYNTH_CHARGED_MB:-0}

out_of_heap=()
[[ ${CAUSYNTH_TRACE_MODE:-} != replay-context ]] \
  || out_of_heap=(-XX:+ExitOnOutOfMemoryError)
# shellcheck source=../../run_engine.sh
source "${lib}/../../run_engine.sh"
heap_mb=$(campaign_replay_heap_mb "${CAUSYNTH_HEAP_BASIS_MB:-${charged_mb}}")
set +e
"${jdk}/bin/java" -ea -Xmx${heap_mb}m "${out_of_heap[@]+"${out_of_heap[@]}"}" \
  -Djava.awt.headless=true \
  -Dsun.reflect.noInflation=true \
  -Dorg.slf4j.simpleLogger.defaultLogLevel=warn \
  -Djava.io.tmpdir="${tmpdir}" "${jvm_properties[@]}" \
  "${properties[@]}" \
  "${extra[@]+"${extra[@]}"}" -cp "${classpath}" \
  edu.uva.liftlab.graphchecker.runtime.JUnitMethodRunner \
  "${test_class}" "${test_method}" &
jvm=$!
campaign_watch_workload "${jvm}" "${charged_mb}" "${trace:-${work}}" \
  "${trace:+${CAUSYNTH_RECORDING_MAX_TRACE_MB:-0}}" &
watch=$!
wait "${jvm}"
status=$?
wait "${watch}"
set -e
if [[ -n ${results:-} ]]; then
  [[ -s ${results} ]] || exit $((status == 0 ? 2 : status))
else
  ((status == 0))
  [[ -s ${trace}/runtime_trace.jsonl && -s ${trace}/streaming_trace_manifest.json ]]
fi

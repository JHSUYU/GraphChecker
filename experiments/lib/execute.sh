#!/usr/bin/env bash
# execute.sh <case-dir> <case-id> -- one workload JVM: the recording when the
# campaign names a trace directory, a concolic replay when it names a task
# plan.  The same script for every case.
set -euo pipefail
lib=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
source "${lib}/case-env.sh" "${1:?missing case directory}" "${2-}"
jar=${GRAPHCHECKER_JAR:?missing GraphChecker jar}
cp=$(bash "${lib}/classpath.sh" "${case_dir}" "${case_id}")

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
  [[ ${CAUSYNTH_CONCOLIC_ROLE} != worker ]] || properties+=(
    -Dcausynth.concolic.halt.after.selected.result=true)
else
  classes=${CAUSYNTH_INSTRUMENTED_CLASSES_DIR:?missing instrumented classes}
  work=$(mktemp -d "/tmp/${tag}-trace.XXXXXX")
  trace=${CAUSYNTH_TRACE_OUTPUT_DIR:?missing trace output directory}
  jdk=/usr/lib/jvm/java-8-openjdk-amd64
  properties=(
    "-Dcausynth.trace.test=${test_name}"
    "-Dcausynth.trace.start.paused=true")
fi

mkdir -p ${trace:+"${trace}"} ${results:+"$(dirname "${results}")"}

# Where the JVM puts its temp files and the cluster its data
# (system_jvm_properties).  The worker directory is on the shared home, so
# by default this is an fsync-heavy little filesystem per concurrent replay
# on one NFS mount; CAUSYNTH_LOCAL_SCRATCH moves it to a local disk instead.
# Nothing downstream reads either: what a replay PUBLISHES is its session and
# its result rows, both under the worker directory.  Opt-in, and it degrades
# rather than fails.
scratch_owned=""
remove_local_scratch() {
  [[ -z ${scratch_owned} ]] || rm -rf -- "${scratch_owned}"
}
tmpdir="${work}/temp"
datadir="${work}/data"
if [[ -n ${CAUSYNTH_LOCAL_SCRATCH:-} ]]; then
  if mkdir -p "${CAUSYNTH_LOCAL_SCRATCH}" 2>/dev/null \
      && scratch_owned=$(mktemp -d "${CAUSYNTH_LOCAL_SCRATCH}/replay.XXXXXXXX" \
        2>/dev/null); then
    tmpdir="${scratch_owned}/temp"
    datadir="${scratch_owned}/data"
    trap remove_local_scratch EXIT
  else
    scratch_owned=""
    echo "${tag}: CAUSYNTH_LOCAL_SCRATCH=${CAUSYNTH_LOCAL_SCRATCH} is not\
 usable on $(hostname); replay scratch stays under ${work}" >&2
  fi
fi
mkdir -p "${tmpdir}" "${datadir}"
system_jvm_properties "${tmpdir}" "${datadir}"
if [[ ${system_jar_first} == true ]]; then
  classpath="${classes}:${jar}:${cp}"
else
  classpath="${classes}:${cp}:${jar}"
fi

# Extra JVM options for every workload JVM of a run, recording and replays
# alike -- a debugging switch, empty by default.
extra=()
[[ -z ${CAUSYNTH_WORKLOAD_JAVA_OPTS:-} ]] \
  || read -r -a extra <<<"${CAUSYNTH_WORKLOAD_JAVA_OPTS}"

# The heap is half of what the campaign reserves for one replay
# (obligation_memory_mb, which the host gate charges); the other half is the
# VM's native symbolic state.  2 GB at least.
heap_mb=$(( ${CAUSYNTH_OBLIGATION_MEMORY_MB:-0} / 2 ))
(( heap_mb >= 2048 )) || heap_mb=2048

# noInflation: a reflective call is served by a generated accessor from its
# first call, not by the native one for fifteen calls and a generated one
# after, so one write through reflection names one site in every run.
set +e
"${jdk}/bin/java" -ea -Xmx${heap_mb}m -Djava.awt.headless=true \
  -Dsun.reflect.noInflation=true \
  -Dorg.slf4j.simpleLogger.defaultLogLevel=warn \
  -Djava.io.tmpdir="${tmpdir}" "${jvm_properties[@]}" \
  "${properties[@]}" "${workload_properties[@]+"${workload_properties[@]}"}" \
  "${extra[@]+"${extra[@]}"}" -cp "${classpath}" \
  edu.uva.liftlab.graphchecker.runtime.JUnitMethodRunner \
  "${test_class}" "${test_method}"
status=$?
set -e
if [[ -n ${results:-} ]]; then
  [[ -s ${results} ]] || exit $((status == 0 ? 2 : status))
else
  ((status == 0))
  [[ -s ${trace}/runtime_trace.jsonl && -s ${trace}/streaming_trace_manifest.json ]]
fi

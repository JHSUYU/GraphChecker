#!/usr/bin/env bash
# execute.sh <case-dir> <case-id> -- one workload JVM: the recording when the
# campaign names a trace directory, a concolic replay when it names a task
# plan.  The same script for every case.
set -euo pipefail
lib=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
source "${lib}/case-env.sh" "${1:?missing case directory}" "${2-}"
jar=${GRAPHCHECKER_JAR:?missing GraphChecker jar}
cp=$(bash "${lib}/classpath.sh" "${case_dir}" "${case_id}")
# The scratch directory this script made, removed when it exits.
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
  [[ ${CAUSYNTH_CONCOLIC_ROLE} != worker ]] || properties+=(
    -Dcausynth.concolic.halt.after.selected.result=true)
else
  classes=${CAUSYNTH_INSTRUMENTED_CLASSES_DIR:?missing instrumented classes}
  # The recording's own temp and data: nothing reads them after it.
  work=$(mktemp -d "/tmp/${tag}-trace.XXXXXX")
  scratch_owned=${work}
  trace=${CAUSYNTH_TRACE_OUTPUT_DIR:?missing trace output directory}
  jdk=/usr/lib/jvm/java-8-openjdk-amd64
  # A native reproduction plants CONFIRM's world (runtime.RecordingPlant),
  # each ORDER held at most CAUSYNTH_ORDER_TIMEOUT_MS (runtime.Confirmation).
  properties=(
    "-Dcausynth.trace.test=${test_name}"
    "-Dcausynth.trace.start.paused=true"
    ${CAUSYNTH_PLANT:+"-Dcausynth.plant=${CAUSYNTH_PLANT}"}
    ${CAUSYNTH_ORDER_TIMEOUT_MS:+"-Dcausynth.confirm.order.timeout.ms=${CAUSYNTH_ORDER_TIMEOUT_MS}"})
fi

# The case's window, the same in the recording and every replay
# (case-env.sh recording_window; runtime.RecordingWindow#atStartup).
[[ -z ${recording_window} ]] \
  || properties+=("-Dcausynth.recording.window=${recording_window}")

mkdir -p ${trace:+"${trace}"} ${results:+"$(dirname "${results}")"}

# Where the JVM puts its temp files and the cluster its data
# (system_jvm_properties).  The worker directory is on the shared home, so
# by default this is an fsync-heavy little filesystem per concurrent replay
# on one NFS mount; CAUSYNTH_LOCAL_SCRATCH moves it to a local disk instead.
# Nothing downstream reads either: what a replay PUBLISHES is its session and
# its result rows, both under the worker directory.  Opt-in, and it degrades
# rather than fails.
remove_local_scratch() {
  [[ -z ${scratch_owned} ]] || rm -rf -- "${scratch_owned}"
}
trap remove_local_scratch EXIT
tmpdir="${work}/temp"
datadir="${work}/data"
if [[ -n ${CAUSYNTH_LOCAL_SCRATCH:-} ]]; then
  if mkdir -p "${CAUSYNTH_LOCAL_SCRATCH}" 2>/dev/null \
      && scratch_owned=$(mktemp -d "${CAUSYNTH_LOCAL_SCRATCH}/replay.XXXXXXXX" \
        2>/dev/null); then
    tmpdir="${scratch_owned}/temp"
    datadir="${scratch_owned}/data"
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

# What its host was charged for this JVM (CAUSYNTH_CHARGED_MB: a replay's,
# run_engine.sh campaign_replay; a native reproduction's; none for a
# recording).  The heap is half of it, the other half the VM's native
# symbolic state -- but 4 GB at least: the charge is where a JVM starts, and
# one that outgrows it is granted more where the host's real memory has room
# (campaign_watch_workload), so the heap must not stop it first (Solr seed
# replays of SplitShardTest and ReindexCollectionTest ran out of a 2 GB heap
# at a 2500 MB charge, round a40s).
charged_mb=${CAUSYNTH_CHARGED_MB:-0}
# A replay starts with a charge capped at half a host's ceiling (run_engine.sh
# campaign_replay_charge_mb); its heap is half its whole need
# (CAUSYNTH_HEAP_BASIS_MB), so the cap places it and the ledger grants its
# growth, but the heap never stops it first.
heap_mb=$(( ${CAUSYNTH_HEAP_BASIS_MB:-${charged_mb}} / 2 ))
(( heap_mb >= 4096 )) || heap_mb=4096

# noInflation: a reflective call is served by a generated accessor from its
# first call, not by the native one for fifteen calls and a generated one
# after, so one write through reflection names one site in every run.
# The JVM is watched until it ends (run_engine.sh campaign_watch_workload):
# one that outgrows its charge asks its host's ledger for the excess, and is
# ended only when the host cannot take it; its peak is said at its end (i2/m1,
# sampled: replays peaked at 0.2-1.0 GB for hdfs-11741 and HDFS cases, 1.6 GB
# for SOLR-18406) and goes to workload_rss_mb: a recording's in its trace
# directory, what a native run of it is charged (REPRODUCE); a replay's in its
# worker directory, the campaign's measured replay need (run_engine.sh
# campaign_replay_measured).
# shellcheck source=../../run_engine.sh
source "${lib}/../../run_engine.sh"
set +e
"${jdk}/bin/java" -ea -Xmx${heap_mb}m -Djava.awt.headless=true \
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

#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
jar=${GRAPHCHECKER_JAR:?missing GraphChecker jar}
cp=$("${here}/classpath.sh")
test_class=org.apache.hadoop.hdfs.server.balancer.TestCausynthExpiredBalancerKey
test_method=testEncryptedBalancerAfterKeyRotations
test_name=${test_class}#${test_method}

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
  work=$(mktemp -d /tmp/hdfs-11741-trace.XXXXXX)
  trace=${CAUSYNTH_TRACE_OUTPUT_DIR:?missing trace output directory}
  jdk=/usr/lib/jvm/java-8-openjdk-amd64
  properties=(
    "-Dcausynth.trace.test=${test_name}"
    "-Dcausynth.trace.start.paused=true")
fi

mkdir -p ${trace:+"${trace}"} ${results:+"$(dirname "${results}")"}

# Where the JVM puts its temp files and MiniDFSCluster its name directories,
# edit logs and block data.  The worker directory is on the shared home, so
# by default this is an fsync-heavy little filesystem per concurrent replay
# on one NFS mount; CAUSYNTH_LOCAL_SCRATCH moves it to a local disk instead.
#
# Nothing downstream reads either of these.  What this replay PUBLISHES is
# its session under CAUSYNTH_CONCOLIC_SESSIONS and its rows at
# CAUSYNTH_CONCOLIC_RESULTS, both under the worker directory on the shared
# home and neither of them beneath temp/ or data/.  So the subdirectory goes
# away when the replay exits, however it exits.
#
# Opt-in, and it degrades rather than fails: a host without a usable scratch
# root says so on stderr and keeps the old paths, because a replay that
# cannot find a local disk is still a replay.
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
    echo "hdfs-11741: CAUSYNTH_LOCAL_SCRATCH=${CAUSYNTH_LOCAL_SCRATCH} is not\
 usable on $(hostname); replay scratch stays under ${work}" >&2
  fi
fi
mkdir -p "${tmpdir}" "${datadir}"

set +e
"${jdk}/bin/java" -ea -Xmx2g -Djava.awt.headless=true \
  -Dorg.slf4j.simpleLogger.defaultLogLevel=warn \
  -Djava.io.tmpdir="${tmpdir}" -Dtest.build.data="${datadir}" \
  "${properties[@]}" -cp "${classes}:${jar}:${cp}" \
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

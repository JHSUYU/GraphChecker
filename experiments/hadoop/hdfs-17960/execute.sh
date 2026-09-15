#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
jar=${GRAPHCHECKER_JAR:?missing GraphChecker jar}
cp=$("${here}/classpath.sh")
test_class=org.apache.hadoop.hdfs.server.namenode.snapshot.TestOrderedSnapshotDeletion
test_method=testOrderedDeletionWithRestart
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
  work=$(mktemp -d /tmp/hdfs-17960-trace.XXXXXX)
  trace=${CAUSYNTH_TRACE_OUTPUT_DIR:?missing trace output directory}
  jdk=/usr/lib/jvm/java-8-openjdk-amd64
  properties=(
    "-Dcausynth.trace.test=${test_name}"
    "-Dcausynth.trace.start.paused=true")
fi

mkdir -p "${work}/temp" "${work}/data" ${trace:+"${trace}"} \
  ${results:+"$(dirname "${results}")"}
set +e
"${jdk}/bin/java" -ea -Xmx2g -Djava.awt.headless=true \
  -Dorg.slf4j.simpleLogger.defaultLogLevel=warn \
  -Djava.io.tmpdir="${work}/temp" -Dtest.build.data="${work}/data" \
  -Dcausynth.junit.ignore.timeout=true -Dcausynth.junit.exit.after.run=true \
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

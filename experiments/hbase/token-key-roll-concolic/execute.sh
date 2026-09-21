#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
jar=${GRAPHCHECKER_JAR:?GraphChecker jar is required}
classpath=$("$here/classpath.sh")
test_class=org.apache.hadoop.hbase.security.token.TestAuthenticationTokenKeyRollCoordination
test_method=testDelayedRollNotificationMakesUnexpiredTokenUnverifiable
test_name="$test_class#$test_method"

if [[ -n ${CAUSYNTH_CONCOLIC_TASK_PLAN:-} ]]; then
  classes=${CAUSYNTH_CONCOLIC_CLASSES:?concolic classes are required}
  work=${CAUSYNTH_CONCOLIC_WORKER_DIR:?worker dir is required}
  results=${CAUSYNTH_CONCOLIC_RESULTS:?result path is required}
  jdk=${CAUSYNTH_CUSTOM_JDK_HOME:?custom JDK is required}
  properties=(
    "-Dcausynth.concolic.task.plan=$CAUSYNTH_CONCOLIC_TASK_PLAN"
    "-Dcausynth.concolic.task.id=${CAUSYNTH_CONCOLIC_TASK_ID:?task id is required}"
    "-Dcausynth.concolic.results=$results"
    "-Dcausynth.concolic.campaign.max.tasks=${CAUSYNTH_CONCOLIC_MAX_TASKS:?task limit is required}"
  )
  if [[ ${CAUSYNTH_CONCOLIC_ROLE:-} == worker ]]; then
    properties+=(-Dcausynth.concolic.halt.after.selected.result=true)
  fi
else
  classes=${CAUSYNTH_INSTRUMENTED_CLASSES_DIR:?instrumented classes are required}
  work=$(mktemp -d /tmp/hbase-token-key-roll-trace.XXXXXX)
  trace=${CAUSYNTH_TRACE_OUTPUT_DIR:?trace output dir is required}
  jdk=/usr/lib/jvm/java-8-openjdk-amd64
  properties=(
    "-Dcausynth.trace.test=$test_name"
    "-Dcausynth.trace.start.paused=true"
  )
fi

if [[ -n ${CAUSYNTH_TRACE_MODE:-} ]]; then
  properties+=("-Dcausynth.trace.mode=$CAUSYNTH_TRACE_MODE")
fi
mkdir -p "$work/temp" "$work/data" ${trace:+"$trace"} \
  ${results:+"$(dirname "$results")"}
set +e
"$jdk/bin/java" -ea -Xint -Xms256m -Xmx3g -Djava.awt.headless=true \
  -Dorg.slf4j.simpleLogger.defaultLogLevel=warn \
  "-Djava.io.tmpdir=$work/temp" "-Dhadoop.tmp.dir=$work/temp" \
  "-Dtest.build.data=$work/data" "${properties[@]}" \
  -cp "$classes:$jar:$classpath" \
  edu.uva.liftlab.graphchecker.runtime.JUnitMethodRunner \
  "$test_class" "$test_method"
status=$?
set -e
if [[ -n ${results:-} ]]; then
  [[ -s "$results" ]] || exit $((status == 0 ? 2 : status))
else
  ((status == 0))
  [[ -s "$trace/runtime_trace.jsonl" && -s "$trace/streaming_trace_manifest.json" ]]
fi

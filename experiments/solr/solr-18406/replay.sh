#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
role=${CAUSYNTH_CONCOLIC_ROLE:?missing replay role}
plan=${CAUSYNTH_CONCOLIC_TASK_PLAN:?missing task plan}
ids=${CAUSYNTH_CONCOLIC_TASK_ID:?missing task ids}
results=${CAUSYNTH_CONCOLIC_RESULTS:?missing result path}
classes=${CAUSYNTH_CONCOLIC_CLASSES:?missing concolic classes}
worker=${CAUSYNTH_CONCOLIC_WORKER_DIR:?missing worker directory}
limit=${CAUSYNTH_CONCOLIC_MAX_TASKS:?missing task limit}
jdk=${CAUSYNTH_CUSTOM_JDK_HOME:?missing custom JDK}
jar=${GRAPHCHECKER_JAR:?missing GraphChecker jar}

mkdir -p "${worker}/temp" "$(dirname "${results}")"
cp=$(${here}/classpath.sh)
properties=(
  "-Dcausynth.concolic.task.plan=${plan}"
  "-Dcausynth.concolic.task.id=${ids}"
  "-Dcausynth.concolic.results=${results}"
  "-Dcausynth.concolic.diagnostics=${CAUSYNTH_CONCOLIC_DIAGNOSTICS:-false}"
  "-Dcausynth.concolic.campaign.max.tasks=${limit}"
)
[[ "${role}" != worker ]] || properties+=(
  -Dcausynth.concolic.halt.after.selected.result=true
)

set +e
"${jdk}/bin/java" -ea -Xmx2g \
  -Djava.awt.headless=true \
  -Dtest.solr.allowed.securerandom=NativePRNG \
  -Dsolr.tests.rsaKeySize=512 \
  -Djava.io.tmpdir="${worker}/temp" \
  -Djetty.testMode=1 \
  -Dtests.asserts=true \
  -Dtests.seed=3DB23CD8D4DC835D \
  -Dtests.locale=en \
  -Dtests.timezone=UTC \
  -Dtests.slow=true \
  -Dtests.src.home=/opt/solr \
  -Dtests.luceneMatchVersion=8.11.4 \
  -Dtests.LUCENE_VERSION=8.11.4 \
  -Dcausynth.junit.exit.after.run=true \
  "${properties[@]}" \
  -cp "${classes}:${jar}:${cp}" \
  edu.uva.liftlab.graphchecker.runtime.JUnitMethodRunner \
  org.apache.solr.handler.TestReplicationHandler \
  testFollowerRestartsWhenCommitExpiresBeforeFileDownload
status=$?
set -e

[[ -s "${results}" ]] || exit "${status:-2}"

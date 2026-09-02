#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
classes=${CAUSYNTH_INSTRUMENTED_CLASSES_DIR:?missing instrumented classes}
trace=${CAUSYNTH_TRACE_OUTPUT_DIR:?missing trace output directory}
jar=${GRAPHCHECKER_JAR:?missing GraphChecker jar}
work=$(mktemp -d /tmp/solr-18406-trace.XXXXXX)
mkdir -p "${trace}" "${work}/temp"
cp=$(${here}/classpath.sh)

set +e
/usr/lib/jvm/java-8-openjdk-amd64/bin/java -ea -Xmx2g \
  -Djava.awt.headless=true \
  -Dsolr.tests.rsaKeySize=512 \
  -Djava.io.tmpdir="${work}/temp" \
  -Djetty.testMode=1 \
  -Dtests.asserts=true \
  -Dtests.seed=3DB23CD8D4DC835D \
  -Dtests.locale=en \
  -Dtests.timezone=UTC \
  -Dtests.slow=true \
  -Dtests.src.home=/opt/solr \
  -Dtests.luceneMatchVersion=8.11.4 \
  -Dtests.LUCENE_VERSION=8.11.4 \
  -Dcausynth.trace.output.dir="${trace}" \
  -Dcausynth.trace.test=org.apache.solr.handler.TestReplicationHandler#testFollowerRestartsWhenCommitExpiresBeforeFileDownload \
  -Dcausynth.junit.exit.after.run=true \
  -cp "${classes}:${jar}:${cp}" \
  edu.uva.liftlab.graphchecker.runtime.JUnitMethodRunner \
  org.apache.solr.handler.TestReplicationHandler \
  testFollowerRestartsWhenCommitExpiresBeforeFileDownload
status=$?
set -e

[[ ${status} -eq 1 ]] || {
  echo "expected the unfixed SOLR-18406 assertion failure, got exit ${status}" >&2
  exit 2
}
[[ -s "${trace}/runtime_trace.jsonl" ]]
[[ -s "${trace}/streaming_trace_manifest.json" ]]

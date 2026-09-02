#!/usr/bin/env bash
set -euo pipefail

cd /opt/solr/solr/core
set +e
/usr/lib/jvm/java-8-openjdk-amd64/bin/java -cp \
  '../../lucene/tools/lib/ant-1.10.14.jar:/users/ZhenyuLi/.ivy2/cache/org.apache.ant/ant-launcher/jars/ant-launcher-1.10.11.jar:/users/ZhenyuLi/.ivy2/cache/org.apache.ivy/ivy/jars/ivy-2.4.0.jar:/usr/lib/jvm/java-8-openjdk-amd64/lib/tools.jar' \
  org.apache.tools.ant.Main -Divy_install_path=/users/ZhenyuLi/.ivy2/cache/org.apache.ivy/ivy/jars \
  test -Dtestcase=TestReplicationHandler \
  -Dtests.method=testFollowerRestartsWhenCommitExpiresBeforeFileDownload \
  -Dtests.seed=3DB23CD8D4DC835D
status=$?
set -e
[[ ${status} -ne 0 ]] || {
  echo "SOLR-18406 workload unexpectedly passed" >&2
  exit 2
}
[[ -f ../../solr/build/solr-core/test/TEST-org.apache.solr.handler.TestReplicationHandler.xml ]]

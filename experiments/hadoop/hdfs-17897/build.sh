#!/usr/bin/env bash
set -euo pipefail

repo=/opt/hadoop-hdfs-17897
test_class=org.apache.hadoop.hdfs.TestCausynthStripedChecksum
test_method=testStaleEncryptionKeyFailsStripedChecksum
report=${repo}/hadoop-hdfs-project/hadoop-hdfs/target/surefire-reports/TEST-${test_class}.xml
export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
export PATH=${JAVA_HOME}/bin:${PATH}
cd "${repo}"

common=(-q -Djavac.version=8 -DskipShade -Dskip.npm -Dskip.yarn)
./mvnw "${common[@]}" -pl \
  hadoop-common-project/hadoop-common,hadoop-hdfs-project/hadoop-hdfs-client,hadoop-hdfs-project/hadoop-hdfs \
  -am -Dmaven.test.skip=true clean install
./mvnw "${common[@]}" -pl hadoop-hdfs-project/hadoop-hdfs \
  -Dtest="${test_class##*.}#${test_method}" clean test
rg -q 'tests="1" errors="0" skipped="0" failures="0"' "${report}"

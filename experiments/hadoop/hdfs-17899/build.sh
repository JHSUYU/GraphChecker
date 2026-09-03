#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
source "${here}/case.sh" "${1:?missing case}"
export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
export PATH=${JAVA_HOME}/bin:${PATH}
cd "${repo}"

common=(-q -Djavac.version=8 -DskipShade -Dskip.npm -Dskip.yarn)
./mvnw "${common[@]}" -pl \
  hadoop-common-project/hadoop-common,hadoop-hdfs-project/hadoop-hdfs-client,hadoop-hdfs-project/hadoop-hdfs \
  -am -Dmaven.test.skip=true clean install
for artifact in hadoop-common-project/hadoop-auth \
  hadoop-common-project/hadoop-common hadoop-common-project/hadoop-kms; do
  ./mvnw "${common[@]}" -pl "${artifact}" -DskipTests clean install
done
./mvnw "${common[@]}" -pl hadoop-hdfs-project/hadoop-hdfs \
  -Dtest="${test_class##*.}#${test_method}" clean test
[[ -f "${report}" ]]

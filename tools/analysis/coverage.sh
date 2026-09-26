#!/usr/bin/env bash
# coverage.sh TREE TEST_CLASS TEST_METHOD OUT_PREFIX
# Runs one workload's JUnit method on plain JDK 8 under the JaCoCo agent and writes
# OUT_PREFIX.exec and OUT_PREFIX.lines ("class<TAB>line" of every executed line of
# the tree's hadoop-common / hdfs-client / hdfs classes).
set -uo pipefail
tree=$1 cls=$2 method=$3 out=$4
export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64 PATH=/usr/lib/jvm/java-8-openjdk-amd64/bin:$PATH
m2=$HOME/.m2/repository
agent=$m2/org/jacoco/org.jacoco.agent/0.8.5/org.jacoco.agent-0.8.5-runtime.jar
tools="$m2/org/jacoco/org.jacoco.core/0.8.6/org.jacoco.core-0.8.6.jar:$m2/org/ow2/asm/asm/9.4/asm-9.4.jar:$m2/org/ow2/asm/asm-commons/9.4/asm-commons-9.4.jar:$m2/org/ow2/asm/asm-tree/9.4/asm-tree-9.4.jar:$m2/org/ow2/asm/asm-analysis/9.4/asm-analysis-9.4.jar"
here=$(cd "$(dirname "$0")" && pwd)
gc=$(cd "$here/../.." && pwd)/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar
hdfs=$tree/hadoop-hdfs-project/hadoop-hdfs; client=$tree/hadoop-hdfs-project/hadoop-hdfs-client
common=$tree/hadoop-common-project/hadoop-common
report=$(ls -t $hdfs/target/surefire-reports/TEST-*.xml | head -1)
deps=$(python3 - "$report" <<'PY'
import sys, xml.etree.ElementTree as ET
r = ET.parse(sys.argv[1]).getroot()
print(next(p.get("value") for p in r.findall("./properties/property") if p.get("name") == "java.class.path"))
PY
)
cp="$hdfs/target/test-classes:$hdfs/target/classes:$client/target/classes:$common/target/classes:$gc:$deps"
work=$(mktemp -d /tmp/gc-cov-XXXXXX)
( cd "$tree" && java -ea -Xmx2g -Djava.awt.headless=true -Djava.io.tmpdir=$work \
    -Dtest.build.data=$work/data -Dsun.reflect.noInflation=true \
    -javaagent:$agent=destfile=$out.exec,includes=org.apache.hadoop.* \
    -cp "$cp" edu.uva.liftlab.graphchecker.runtime.JUnitMethodRunner "$cls" "$method" ) > $out.log 2>&1
status=$?
javac -cp "$tools" -d "$work" "$here/CoveredLines.java"
java -cp "$tools:$work" CoveredLines $out.exec $hdfs/target/classes $client/target/classes $common/target/classes > $out.lines
rm -rf "$work"
echo "$(basename $out) exit=$status lines=$(wc -l < $out.lines)"

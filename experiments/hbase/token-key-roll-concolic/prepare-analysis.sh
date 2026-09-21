#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
repo=/u/vnr3ne/hbase-jdk8-concolic
jar=${GRAPHCHECKER_JAR:-/u/vnr3ne/GraphChecker/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar}
jdk=/usr/lib/jvm/java-8-openjdk-amd64
overlay="$here/overlay"
source_dir="$overlay/source/org/apache/hadoop/hbase/security/token"
production_dir="$overlay/production-classes"
test_dir="$overlay/test-classes"
classpath=$("$here/classpath.sh")

[[ -s "$jar" && -x "$jdk/bin/javac" ]] || {
  printf 'GraphChecker jar or Java 8 javac is missing\n' >&2
  exit 2
}
mkdir -p "$source_dir" "$production_dir" "$test_dir"
find "$production_dir" "$test_dir" -type f -name '*.class' -delete

python3 - "$repo/hbase-server/src/main/java/org/apache/hadoop/hbase/security/token/AuthenticationTokenSecretManager.java" \
  "$source_dir/AuthenticationTokenSecretManager.java" <<'PY'
import pathlib
import sys

source = pathlib.Path(sys.argv[1]).read_text()
needle = '      throw new InvalidToken("Unknown master key for token (id="'
if source.count(needle) != 1:
    raise SystemExit('expected exactly one unknown-master-key throw')
source = source.replace(
    'import org.apache.hadoop.conf.Configuration;',
    'import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;\n'
    'import org.apache.hadoop.conf.Configuration;', 1)
source = source.replace(
    needle,
    '      throw new @CausynthExceptionTarget("hbase-token-key-roll") '
    'InvalidToken("Unknown master key for token (id="', 1)
pathlib.Path(sys.argv[2]).write_text(source)
PY

test_source="$here/workload-src/TestAuthenticationTokenKeyRollCoordination.java"
[[ -s "$test_source" ]] || {
  printf 'missing vendored HBase regression test: %s\n' "$test_source" >&2
  exit 2
}
"$jdk/bin/javac" -g -source 8 -target 8 -proc:none \
  -cp "$jar:$classpath" -d "$production_dir" \
  "$source_dir/AuthenticationTokenSecretManager.java"
"$jdk/bin/javac" -g -source 8 -target 8 -proc:none \
  -cp "$production_dir:$jar:$classpath" -d "$test_dir" "$test_source"

[[ -s "$production_dir/org/apache/hadoop/hbase/security/token/AuthenticationTokenSecretManager.class" ]]
[[ -s "$test_dir/org/apache/hadoop/hbase/security/token/TestAuthenticationTokenKeyRollCoordination.class" ]]
printf 'compiled annotated HBase target and regression workload in %s\n' "$overlay"

#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker=$(cd "${here}/../../.." && pwd -P)
worktree=${HBASE_JDK8_WORKTREE:-/u/vnr3ne/hbase-jdk8-concolic}
vm_home=${VM_HOME:-${JAVA_HOME_OVERRIDE:-${graphchecker}/third_party/OpenJDK-Concolic-Execution-Engine/build/linux-x86_64-normal-zero-release/images/j2sdk-image}}
graphchecker_jar=${GRAPHCHECKER_JAR:-${graphchecker}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar}
test_class=org.apache.hadoop.hbase.client.TestMultiActionMetricsFromClient
test_method=testMultiMetrics
output_root=${PRESSURE_OUTPUT_ROOT:-/tmp/graphchecker-hbase-jdk8-pressure}
timeout_duration=${PRESSURE_TIMEOUT:-45m}
heap=${PRESSURE_HEAP:-8g}
classpath_file=
plan=
task_id=
instrumented_classes=

usage() {
  cat <<'EOF'
Usage: run.sh [options]
  --test CLASS#METHOD       JUnit 4/5 test (default: 1-RS TestMultiActionMetricsFromClient#testMultiMetrics)
  --large                   Use 3-Master/5-RS TestClientClusterStatus#testNone
  --worktree DIR            Java 8 HBase checkout
  --vm-home DIR             JDK home; defaults to the built concolic Zero VM
  --classpath-file FILE     Maven test-dependency classpath; if omitted, generate it after build
  --output-root DIR         Parent directory for an isolated run directory
  --timeout DURATION        GNU timeout duration (default: 45m)
  --heap SIZE               Java -Xmx value (default: 8g)
  --plan FILE --task-id ID --classes DIR
                            Optional one-task instrumented concolic replay

The default run measures the custom Zero VM with a real mini-cluster. A true
symbolic replay additionally needs a GraphChecker task plan and instrumented
classes. No HBase build or test is started until this script is invoked.
EOF
}

die() { printf 'jdk8-pressure: %s\n' "$*" >&2; exit 2; }

while (($#)); do
  case $1 in
    --test) (($# >= 2)) || die "--test needs CLASS#METHOD"; test_spec=$2; shift 2 ;;
    --large) test_class=org.apache.hadoop.hbase.TestClientClusterStatus; test_method=testNone; shift ;;
    --worktree) (($# >= 2)) || die "--worktree needs DIR"; worktree=$2; shift 2 ;;
    --vm-home) (($# >= 2)) || die "--vm-home needs DIR"; vm_home=$2; shift 2 ;;
    --classpath-file) (($# >= 2)) || die "--classpath-file needs FILE"; classpath_file=$2; shift 2 ;;
    --output-root) (($# >= 2)) || die "--output-root needs DIR"; output_root=$2; shift 2 ;;
    --timeout) (($# >= 2)) || die "--timeout needs DURATION"; timeout_duration=$2; shift 2 ;;
    --heap) (($# >= 2)) || die "--heap needs SIZE"; heap=$2; shift 2 ;;
    --plan) (($# >= 2)) || die "--plan needs FILE"; plan=$2; shift 2 ;;
    --task-id) (($# >= 2)) || die "--task-id needs ID"; task_id=$2; shift 2 ;;
    --classes) (($# >= 2)) || die "--classes needs DIR"; instrumented_classes=$2; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) die "unknown option: $1" ;;
  esac
done

if [[ -n ${test_spec:-} ]]; then
  [[ $test_spec == *#* ]] || die "--test must be CLASS#METHOD"
  test_class=${test_spec%#*}
  test_method=${test_spec##*#}
fi
[[ $test_class =~ ^[A-Za-z_$][A-Za-z0-9_$.]*$ ]] || die "invalid test class"
[[ $test_method =~ ^[A-Za-z_$][A-Za-z0-9_$]*$ ]] || die "invalid test method"
if [[ -n $plan || -n $task_id || -n $instrumented_classes ]]; then
  [[ -n $plan && -n $task_id && -n $instrumented_classes ]] ||
    die "--plan, --task-id and --classes must be provided together"
  [[ -s $plan && -d $instrumented_classes ]] || die "plan or instrumented classes missing"
  plan=$(realpath "$plan")
  instrumented_classes=$(realpath "$instrumented_classes")
fi

worktree=$(cd "$worktree" && pwd -P) || die "HBase worktree absent"
vm_home=$(cd "$vm_home" && pwd -P) || die "VM home absent"
[[ -x $vm_home/bin/java ]] || die "VM executable absent: $vm_home/bin/java"
[[ -s $graphchecker_jar ]] || die "GraphChecker jar absent: $graphchecker_jar"
graphchecker_jar=$(realpath "$graphchecker_jar")
[[ -d $worktree/hbase-server/target/classes && -d $worktree/hbase-server/target/test-classes ]] ||
  die "Java 8 HBase server classes and test-classes must be built first"
test_class_file=$worktree/hbase-server/target/test-classes/${test_class//.//}.class
[[ -s $test_class_file ]] || die "compiled test class absent: $test_class_file"
python3 "$here/classpath.py" --check-class "$test_class_file"
vm_version=$("$vm_home/bin/java" -version 2>&1) || die "VM cannot launch"
[[ $vm_version == *'version "1.8.'* ]] || die "VM must be Java 8: $vm_home"

mkdir -p "$output_root"
output_root=$(cd "$output_root" && pwd -P)
run_dir=$(mktemp -d "$output_root/run.$(date -u +%Y%m%dT%H%M%SZ).XXXXXX")
mkdir -p "$run_dir/tmp" "$run_dir/data" "$run_dir/sessions"
printf '%s\n' "$run_dir" > "$output_root/latest-run"

if [[ -n $classpath_file ]]; then
  [[ -s $classpath_file ]] || die "classpath file absent or empty: $classpath_file"
  cp "$classpath_file" "$run_dir/maven-test-classpath.txt"
else
  stock_jdk=${STOCK_JDK8_HOME:-/usr/lib/jvm/java-8-openjdk-amd64}
  [[ -x $stock_jdk/bin/java ]] || die "stock Java 8 absent: $stock_jdk"
  # Reactor order ends in hbase-server, whose test dependency path is the one
  # retained in this single output file. This runs only when the script runs.
  env JAVA_HOME="$stock_jdk" PATH="$stock_jdk/bin:$PATH" \
    mvn -o -q -f "$worktree/pom.xml" -pl hbase-server -am \
    -DincludeScope=test \
    "-Dmdep.outputFile=$run_dir/maven-test-classpath.txt" \
    org.apache.maven.plugins:maven-dependency-plugin:3.6.1:build-classpath \
    > "$run_dir/classpath-maven.log" 2>&1 ||
    die "Maven test classpath generation failed; see $run_dir/classpath-maven.log"
fi

python3 "$here/classpath.py" --worktree "$worktree" \
  --input "$run_dir/maven-test-classpath.txt" --output "$run_dir/classpath.txt" ||
  die "classpath validation failed; see $run_dir/maven-test-classpath.txt"
classpath=$(cat "$run_dir/classpath.txt")
if [[ -n $instrumented_classes ]]; then
  classpath="$instrumented_classes:$graphchecker_jar:$classpath"
else
  classpath="$graphchecker_jar:$classpath"
fi

printf 'test=%s#%s\nvm=%s\nworktree=%s\nheap=%s\ntimeout=%s\nconcolic_plan=%s\n' \
  "$test_class" "$test_method" "$vm_home" "$worktree" "$heap" "$timeout_duration" \
  "${plan:-none}" > "$run_dir/run-info.txt"
"$vm_home/bin/java" -version 2>> "$run_dir/run-info.txt"

java_args=(
  -ea -Xint -Xms512m "-Xmx$heap"
  -Djava.awt.headless=true
  "-Djava.io.tmpdir=$run_dir/tmp"
  "-Dhadoop.tmp.dir=$run_dir/tmp"
  "-Dtest.build.data=$run_dir/data"
  "-Dcausynth.trace.test=$test_class#$test_method"
)
if [[ -d $worktree/hbase-server/target/test-classes/webapps ]]; then
  java_args+=("-Dtest.build.webapps=$worktree/hbase-server/target/test-classes/webapps")
fi
if [[ -n $plan ]]; then
  java_args+=(
    "-Dcausynth.concolic.task.plan=$plan"
    "-Dcausynth.concolic.task.id=$task_id"
    "-Dcausynth.concolic.results=$run_dir/concolic-results.jsonl"
    -Dcausynth.concolic.campaign.max.tasks=1
  )
fi

# One test JVM, one selected symbolic task at most. /usr/bin/time captures
# child peak RSS and elapsed time, while the sampler gives second-by-second
# Java RSS, threads, MemAvailable and swap use.
cd "$worktree/hbase-server"
set +e
CAUSYNTH_CONCOLIC_SESSIONS="$run_dir/sessions" \
  /usr/bin/time -v -o "$run_dir/time.txt" \
  timeout --signal=TERM --kill-after=30s "$timeout_duration" \
  "$vm_home/bin/java" "${java_args[@]}" -cp "$classpath" \
  edu.uva.liftlab.graphchecker.runtime.JUnitMethodRunner \
  "$test_class" "$test_method" > "$run_dir/jvm.log" 2>&1 &
runner_pid=$!
python3 "$here/sample_usage.py" --root-pid "$runner_pid" \
  --output "$run_dir/samples.csv" &
sampler_pid=$!
wait "$runner_pid"
status=$?
kill -TERM "$sampler_pid" 2>/dev/null || true
wait "$sampler_pid" 2>/dev/null || true
set -e
printf '%s\n' "$status" > "$run_dir/exit-code.txt"
printf 'run_dir=%s\nexit_code=%s\n' "$run_dir" "$status"
awk '/Elapsed \(wall clock\) time|Maximum resident set size|Swaps:|Exit status:/ {print}' "$run_dir/time.txt"
exit "$status"

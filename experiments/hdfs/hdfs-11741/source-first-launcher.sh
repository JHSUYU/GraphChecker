#!/usr/bin/env bash
#
# HDFS-11741's concrete inputs to the source-first launcher.
#
# This file is not a workflow. It holds no pipeline, no stage ordering and no
# configuration grammar: it records which Hadoop test, which target id and
# which Configuration keys this experiment uses, and hands them to
# edu.uva.liftlab.graphchecker.launcher.SourceTestLauncher. Anything about how
# many passes to run, in which instrumentation mode, belongs to the caller -
# invoke this once per pass with CAUSYNTH_* already in the environment and
# --instrumented pointing at that pass's rewritten classes.
#
# Usage:
#   source-first-launcher.sh build
#   source-first-launcher.sh run [--instrumented DIR ...] [extra launcher args]
#
# Environment:
#   GRAPHCHECKER_JAR   GraphChecker jar-with-dependencies (default: target/)
#   HADOOP_HOME_DIR    Hadoop checkout        (default: /opt/hadoop)
#   CAUSYNTH_JDK_HOME  concolic JDK image     (default: the in-tree build)
#   LAUNCHER_OUTPUT    launcher output dir    (default: experiments-output/...)
#   HADOOP_PROTOC_PATH protoc matching the checkout's protobuf.version
#   LAUNCHER_JVM_ARGS  JVM arguments for the launcher's own JVM, whitespace
#                      separated. The launcher forwards every causynth.*
#                      system property set on itself to the workload, so this
#                      is how a caller supplies a per-pass knob -- the trace
#                      event cap, a selected concolic task -- without this
#                      file growing a configuration grammar.
#   CAUSYNTH_ARTIFACT_MODE  discovery | concolic; required for run
#                      Which of the two artifacts this pass is. GraphChecker
#                      builds two and they are not interchangeable: broad
#                      discovery runs on a stock JIT JVM with lightweight
#                      identity hooks, and the narrow concolic envelope of one
#                      task runs on the Zero image. The pair that has already
#                      cost this experiment a run is a discovery/skeleton tree
#                      under Zero -- nothing fails, the VM simply interprets
#                      every method the broad pass rewrote and admits no
#                      region. Declaring the mode is what lets this file
#                      refuse that pair before the workload starts, and what
#                      refuses a mismatched pair before the workload starts.
#   CAUSYNTH_WORKLOAD_HEAP  explicit workload heap, e.g. 8g. Required under
#                      the concolic image and optional elsewhere. The image's
#                      own default MaxHeapSize is 256 MB, which is not a heap
#                      a MiniDFSCluster plus a symbolic session fits in, and
#                      the failure it produces is not a crash: the VM catches
#                      the OutOfMemoryError while serialising its summary, the
#                      run still exits 0, and the evidence is simply absent.
#                      The launcher owns no JVM-argument flag, so this is
#                      handed to the child through _JAVA_OPTIONS, which the
#                      child JVM echoes on startup - the heap that was
#                      actually used ends up in the workload log rather than
#                      being inferred from a default nobody stated.
#
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)

graphchecker_jar=${GRAPHCHECKER_JAR:-${repo_root}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar}
hadoop_home=${HADOOP_HOME_DIR:-/opt/hadoop}
jdk_home=${CAUSYNTH_JDK_HOME:-${CAUSYNTH_CUSTOM_JDK_HOME:-${repo_root}/third_party/OpenJDK-Concolic-Execution-Engine/build/linux-x86_64-normal-zero-release/images/j2sdk-image}}
output_dir=${LAUNCHER_OUTPUT:-${repo_root}/experiments-output/hdfs-11741-source-first}
# Hadoop pins gson 2.2.4 and the trace recorder needs the 2.10 GsonBuilder API.
# The workload classpath resolves every other shared library to Hadoop's copy,
# so this one jar is prepended by name; keep it at the version GraphChecker's
# own pom declares.
gson_jar=${GRAPHCHECKER_GSON_JAR:-${HOME}/.m2/repository/com/google/code/gson/gson/2.10.1/gson-2.10.1.jar}
artifact_mode=${CAUSYNTH_ARTIFACT_MODE:-}
read -r -a launcher_jvm_args <<< "${LAUNCHER_JVM_ARGS:-}"
heartbeat_expire_interval_ms=""
socket_timeout_ms=""
key_update_interval_ms=""
instrumented_conf_args=()

if [[ $# -lt 1 ]]; then
  echo "usage: $(basename "$0") build|run [launcher args]" >&2
  exit 2
fi
command=$1
shift

if [[ ! -f "${graphchecker_jar}" ]]; then
  echo "GraphChecker jar not found: ${graphchecker_jar}" >&2
  echo "build it with: mvn -DskipTests package" >&2
  exit 2
fi

common=(
  --hadoop-home "${hadoop_home}"
  --output-dir "${output_dir}"
  --exception-target-id hdfs-11741
)

test_class=org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer
test_method=testEncryptedBalancer1

# The VM half of the same question. A concolic-capable image exports the
# concolic natives from its own libjvm; nothing about the path says so, and
# CAUSYNTH_JDK_HOME defaults to the in-tree Zero image, so a discovery pass
# that simply forgot the stock-JVM override is otherwise indistinguishable
# from one that meant it.
jdk_is_concolic() {
  local libjvm symbols
  for libjvm in "${jdk_home}/jre/lib/amd64/server/libjvm.so" \
                "${jdk_home}/lib/amd64/server/libjvm.so"; do
    if [[ -f "${libjvm}" ]] && command -v nm >/dev/null 2>&1; then
      # grep -c, not grep -q: -q closes the pipe on the first match, nm dies
      # of SIGPIPE, and under `set -o pipefail` the concolic image reports
      # itself as a stock JVM.
      symbols=$(nm -D -- "${libjvm}" 2>/dev/null | grep -c -i concolic || true)
      [[ "${symbols}" -gt 0 ]]
      return $?
    fi
  done
  # No nm and no libjvm to read: fall back to what the VM calls itself. The
  # concolic engine is a Zero build; a stock JIT image never is.
  symbols=$("${jdk_home}/bin/java" -version 2>&1 | grep -c "Zero VM" || true)
  [[ "${symbols}" -gt 0 ]]
}

# Refuses the two pairings that produce a run nobody can read afterwards.
#
# A discovery/skeleton tree under Zero is the expensive one: the broad pass
# rewrote a relatively wide candidate set because it performs no symbolic
# execution, and interpreting all of it under the concolic VM buys nothing,
# because no concolic region is declared in it at all. The reverse, a narrow
# concolic tree on a stock JVM, records no symbolic state and quietly yields
# an empty replay.
reconcile_artifact_and_jdk() {
  local concolic=false
  local instrumented_tree_count=0 previous="" argument
  for argument in "$@"; do
    if [[ "${previous}" == "--instrumented" ]]; then
      instrumented_tree_count=$((instrumented_tree_count + 1))
    fi
    previous=${argument}
  done
  if jdk_is_concolic; then concolic=true; fi

  case "${artifact_mode}" in
    concolic)
      [[ "${concolic}" == "true" ]] || {
        echo "ARTIFACT_JDK_MISMATCH: CAUSYNTH_ARTIFACT_MODE=concolic but" \
          "${jdk_home} exports no concolic natives." >&2
        echo "  A concolic pass on a stock JVM records no symbolic state;" \
          "the replay finishes and its evidence is empty." >&2
        exit 3
      }
      [[ ${instrumented_tree_count} -gt 0 ]] || {
        echo "ARTIFACT_MODE_WITHOUT_TREE: CAUSYNTH_ARTIFACT_MODE=concolic" \
          "names no --instrumented tree." >&2
        exit 3
      }
      # Zero executes the selected production methods interpretively.  The
      # upstream test's 11 s DataNode expiry budget is shorter than a measured
      # instrumented NameNode pause, so a healthy node can be removed before
      # the target is reached.  The workload bridge applies this test-only
      # expiry budget after cluster construction; it does not change heartbeat
      # polling, key rotation, RPC traffic, or the selected causal state.
      heartbeat_expire_interval_ms=${CAUSYNTH_HDFS_HEARTBEAT_EXPIRE_MS:-600000}
      socket_timeout_ms=${CAUSYNTH_HDFS_SOCKET_TIMEOUT_MS:-300000}
      key_update_interval_ms=${CAUSYNTH_HDFS_KEY_UPDATE_MS:-60000}
      test_wait_timeout_ms=${CAUSYNTH_HDFS_TEST_WAIT_TIMEOUT_MS:-180000}
      locate_following_block_retries=${CAUSYNTH_HDFS_LOCATE_FOLLOWING_BLOCK_RETRIES:-8}
      launcher_jvm_args+=(
        "-Dcausynth.hdfs.heartbeat.expire.interval.ms=${heartbeat_expire_interval_ms}"
        "-Dcausynth.hdfs.key.update.interval.ms=${key_update_interval_ms}"
        "-Dcausynth.hdfs.test.wait.timeout.ms=${test_wait_timeout_ms}"
      )
      instrumented_conf_args=(
        --conf
        "dfs.client.socket-timeout=${socket_timeout_ms}"
        --conf
        "dfs.client.block.write.locateFollowingBlock.retries=${locate_following_block_retries}"
      )
      # Whether the plan still describes the bodies it names is not asked
      # again here. The campaign freezes one generation and digests its
      # source, jar, VM, config, adapter, loop bounds and production classes
      # in run-manifest.json; a second stamp verified from a second place is
      # a second provenance authority, and two of them disagree exactly when
      # it matters.
      ;;
    discovery)
      [[ "${concolic}" == "false" ]] || {
        echo "ARTIFACT_JDK_MISMATCH: CAUSYNTH_ARTIFACT_MODE=discovery but" \
          "${jdk_home} is the concolic image." >&2
        echo "  Broad discovery belongs on a stock JIT JVM. This launcher" \
          "defaults CAUSYNTH_JDK_HOME to the in-tree Zero image, so a" \
          "discovery pass must name the stock JVM explicitly." >&2
        exit 3
      }
      ;;
    *)
      echo "ARTIFACT_MODE_UNKNOWN: ${artifact_mode}" >&2
      exit 3
      ;;
  esac

  local heap=${CAUSYNTH_WORKLOAD_HEAP:-}
  if [[ -z "${heap}" && "${concolic}" == "true" ]]; then
    echo "WORKLOAD_HEAP_UNDECLARED: the concolic image defaults to a 256 MB" \
      "MaxHeapSize; set CAUSYNTH_WORKLOAD_HEAP (e.g. 8g)." >&2
    exit 3
  fi
  if [[ -n "${heap}" ]]; then
    export _JAVA_OPTIONS="-Xmx${heap}${_JAVA_OPTIONS:+ ${_JAVA_OPTIONS}}"
  fi

}

case "${command}" in
  build)
    exec java "${launcher_jvm_args[@]}" -cp "${graphchecker_jar}" \
      edu.uva.liftlab.graphchecker.launcher.SourceTestLauncher build \
      "${common[@]}" "$@"
    ;;
  run)
    # The workload is HDFS's existing encrypted-balancer test. It supplies the
    # concrete MiniDFSCluster/Balancer execution used to select and exercise
    # local relations; it is not modified to arrange the HDFS-11741 ordering.
    # Alternative branch, communication, read-from and bounded-loop choices
    # belong to GraphChecker's model, not to a replacement test.
    #
    # The two booleans merely restate configuration the test already sets.
    # The key update interval does not: it is a real cluster knob, and it is
    # here because at the stock 600 minutes the NameNode rotates exactly once
    # per start, from lastBlockKeyUpdate=0, before any DataNode has
    # registered. A traced pass then holds one DataNode key-map version and
    # no rotation causally after the Balancer's cached encryption key, so the
    # selected state has no later install and no removal to flip -- there is
    # nothing for the model to search. The value is read in whole minutes
    # (BlockManager.createBlockTokenSecretManager, conf.getLong * 60 * 1000),
    # and the NameNode monitor turns about every 5 s, so 1 is already too
    # coarse to rotate twice inside one Balancer episode; 0 makes every
    # monitor turn rotate. Concolic replay keeps the original token lifetime
    # and instead time-dilates that periodic update through the typed test
    # bridge, because Zero makes unrelated cluster setup last minutes. This
    # removes replay-only stutter rotations without deleting a key version or
    # changing Map store/remove semantics.
    #
    # The other two stretch the Balancer's episode, and they are here because
    # rotating faster is not possible: HeartbeatManager$Monitor.run() sleeps a
    # hard-coded 5000 ms, so ~5 s is the floor on rotation cadence and no key
    # reads it. Unmodified, the Balancer acquires keys, caches its encryption
    # key, moves ten 100-byte blocks and finishes in under two seconds -- the
    # whole episode fits between two rotations, so its SASL lookups only ever
    # see the DataNode map version installed at registration.
    #
    # max.concurrent.moves is the one that matters: a move's SASL handshake
    # happens when the move is dispatched, so serialising moves per node is
    # what spreads the handshakes over time. bandwidthPerSec alone does
    # nothing here -- DataXceiver applies that throttler inside replaceBlock,
    # after the handshake -- but combined with serialisation it makes each
    # serialised move slow enough that the episode spans two rotations and the
    # DataNode installs they trigger. Measured: episode 0.8 s -> 12 s, and 9 of
    # the Balancer's 10 handshakes then read a DataNode map with 2-3 versions
    # instead of 1. Neither key is set anywhere in TestBalancer.initConf or
    # TestBalancerWithEncryptedTransfer, so both are live from this overlay;
    # dfs.heartbeat.interval is not, which is why it is not used here.
    reconcile_artifact_and_jdk "$@"
    exec java "${launcher_jvm_args[@]}" -cp "${graphchecker_jar}" \
      edu.uva.liftlab.graphchecker.launcher.SourceTestLauncher run \
      "${common[@]}" \
      --test-class "${test_class}" \
      --test-method "${test_method}" \
      --jdk-home "${jdk_home}" \
      --target-classes "${hadoop_home}/hadoop-hdfs-project/hadoop-hdfs/target/classes/org/apache/hadoop/hdfs/security" \
      --conf dfs.encrypt.data.transfer=true \
      --conf dfs.block.access.token.enable=true \
      --conf dfs.block.access.key.update.interval=0 \
      --conf dfs.datanode.balance.max.concurrent.moves=1 \
      --conf dfs.datanode.balance.bandwidthPerSec=100 \
      ${instrumented_conf_args[@]+"${instrumented_conf_args[@]}"} \
      --conf-defaults-class org.apache.hadoop.hdfs.HdfsConfiguration \
      --graphchecker-lib "${gson_jar}" \
      "$@"
    ;;
  *)
    echo "unknown command: ${command}" >&2
    exit 2
    ;;
esac

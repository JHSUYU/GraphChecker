#!/usr/bin/env bash

set -euo pipefail

experiment_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker_dir=$(cd "${experiment_dir}/../../.." && pwd -P)
hadoop_dir=${HADOOP_REPO:-/opt/hadoop}
hdfs_pom="${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/pom.xml"
runtime_patch_file="${experiment_dir}/patches/runtime-trace-workload.patch"
fatal_patch_file="${experiment_dir}/patches/mark-fatal-target.patch"
expiry_guard_patch_file="${experiment_dir}/patches/expiry-guard.patch"
symbolic_rpc_fault_patch_file="${experiment_dir}/patches/symbolic-rpc-fault.patch"
workflow=${CAUSYNTH_HDFS_WORKFLOW:-${experiment_dir}/workflow.properties}
external_experiment=${CAUSYNTH_HDFS_EXPERIMENT:-}
variant=${HDFS11741_VARIANT:-vulnerable}
if [[ -n "${external_experiment}" ]]; then
  variant=external
fi
case "${variant}" in
  vulnerable|patched|patched-fault|external) ;;
  *)
    echo "[hdfs-11741] HDFS11741_VARIANT must be vulnerable, patched, or patched-fault" >&2
    exit 1
    ;;
esac
# Experiment artifacts live outside target/ so `mvn clean` can never erase
# a multi-hour trace/schedule campaign.  Override with HDFS11741_WORK_ROOT.
# A pre-migration tree under target/hdfs-11741 is still honored (with a
# warning) until it is moved once:
#   mv target/hdfs-11741 experiments-output/hdfs-11741
legacy_work_root="${graphchecker_dir}/target/hdfs-11741"
default_work_root="${graphchecker_dir}/experiments-output/hdfs-11741"
if [[ "${variant}" != vulnerable ]]; then
  default_work_root="${default_work_root}-${variant}"
fi
if [[ -n "${HDFS11741_WORK_ROOT:-}" ]]; then
  work_root="${HDFS11741_WORK_ROOT}"
elif [[ "${variant}" == vulnerable \
    && ! -d "${default_work_root}" && -d "${legacy_work_root}" ]]; then
  echo "[hdfs-11741] WARNING: using legacy work root ${legacy_work_root};" >&2
  echo "[hdfs-11741] migrate once with: mv ${legacy_work_root} ${default_work_root}" >&2
  work_root="${legacy_work_root}"
else
  work_root="${default_work_root}"
fi
dependency_classpath="${work_root}/dependency-classpath.txt"
project_classpath="${work_root}/project-classpath.txt"
seed_campaign_root="${work_root}/campaigns/auto-seeds"
candidate_root="${work_root}/candidates"
region_plan="${work_root}/runtime/concolic_region_plan.jsonl"
cached_protoc="${work_root}/tools/protoc-2.5.0"
base_commit=ece33208b89a6a06c1b362d10fab31343fe5df13
key_manager_rel=hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/balancer/KeyManager.java
key_manager_source="${hadoop_dir}/${key_manager_rel}"
hdfs_main_classes="${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/target/classes"
hdfs_test_classes="${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/target/test-classes"
protoc_sha256=8b62bcf4d564e08c5bdd5d409c5e8462b07abadba10904946f63870dc9735f45
test_class=${CAUSYNTH_HDFS_TEST_CLASS:-org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer}
test_method=${CAUSYNTH_HDFS_TEST_METHOD:-testEncryptedBalancer1}
test_selector="${test_class}#${test_method}"
test_report="${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/target/surefire-reports/TEST-${test_class}.xml"

partial_probe_enabled=false
partial_probe_sat=false
partial_probe_attempt=0
partial_probe_last_hash=""
partial_probe_target_campaign=""
partial_probe_target_region=""
partial_probe_target_instance=""
partial_probe_target_goal=""
partial_probe_target_reach=""
partial_probe_output=""
declare -a partial_probe_summary_files=()
declare -a partial_probe_required_true_ports=()
replay_engine_fingerprint=""

# Concolic exploration has two independent parallelism levels.  Region jobs
# run different logical closure campaigns, while path jobs execute the
# immutable branch-flip frontier produced for one campaign.  Both default to
# this host's CPU count: every worker is its own JVM, so they contend for
# nothing a smaller default would protect, while a serialised run costs hours
# and produces byte for byte the same artifacts -- which is precisely why
# leaving it narrow goes unnoticed.  The two levels multiply: a campaign
# fan-out of N with a flip fan-out of M admits N*M concurrent replays, at
# roughly 1 GB resident each.
host_parallelism=$(nproc 2>/dev/null || echo 2)
region_parallelism=${HDFS11741_REGION_JOBS:-${host_parallelism}}
path_parallelism=${HDFS11741_PATH_JOBS:-${host_parallelism}}

# Runtime discovery and custom-VM replay must observe the same bounded
# activation envelope.  These workload knobs only cap repeated relevant
# actions in the concrete Hadoop test; the generic CFG instrumentation below
# remains authoritative for every loop executed by a concolic task.
hdfs11741_loop_iteration_cap=8
# Keep the concrete replay envelope identical to the runtime-discovery
# workload.  This is deliberately independent from the generic CFG loop
# bound: increasing the analysis bound must not manufacture more HDFS keys
# and thereby change the observed region occurrences being replayed.
hdfs11741_workload_update_iterations=4
hdfs11741_nn_update_iterations=${HDFS11741_NN_UPDATE_ITERATIONS:-${hdfs11741_workload_update_iterations}}
hdfs11741_datanode_refresh_iterations=${HDFS11741_DATANODE_REFRESH_ITERATIONS:-${hdfs11741_workload_update_iterations}}
hdfs11741_balancer_refresh_iterations=${HDFS11741_BALANCER_REFRESH_ITERATIONS:-${hdfs11741_workload_update_iterations}}
# The Balancer dispatcher pool decides which thread first materializes the
# lazily cached data encryption key.  With the Hadoop default of 200 threads
# the winner is scheduling noise, so runtime discovery and concolic replay
# would observe different producers for the same region.  Both stages run a
# single dispatcher thread to make that winner deterministic.
hdfs11741_balancer_dispatcher_threads=${HDFS11741_BALANCER_DISPATCHER_THREADS:-1}

die() {
  echo "[hdfs-11741] $*" >&2
  exit 1
}

require_positive_integer() {
  local label=$1
  local value=$2
  [[ "${value}" =~ ^[1-9][0-9]*$ ]] \
    || die "${label} must be a positive integer"
}

# Parallelism is the one knob that changes nothing about a run except how long
# it takes, so a wrong value leaves no trace in the artifacts it produces.
# State the width in force and where it came from at every fan-out, so the
# answer survives in the stage log instead of having to be reconstructed from
# directory birth times after the fact.
announce_parallelism() {
  local label=$1
  local variable=$2
  local value=$3
  if [[ -z "${!variable:-}" ]]; then
    echo "[hdfs-11741] warning: ${variable} unset; ${label} defaults to ${value} (host CPUs: ${host_parallelism})" >&2
  elif [[ "${value}" -eq 1 ]]; then
    echo "[hdfs-11741] warning: ${variable}=1 serialises ${label}; that is a debugging posture, not a run configuration" >&2
  fi
}

require_bounded_workload_iterations() {
  local label=$1
  local value=$2
  [[ "${value}" =~ ^[1-9][0-9]*$ ]] \
      && (( value <= hdfs11741_loop_iteration_cap )) \
    || die "${label} must be an integer from 1 through ${hdfs11741_loop_iteration_cap}"
}

require_bounded_workload_iterations HDFS11741_NN_UPDATE_ITERATIONS \
  "${hdfs11741_nn_update_iterations}"
require_bounded_workload_iterations HDFS11741_DATANODE_REFRESH_ITERATIONS \
  "${hdfs11741_datanode_refresh_iterations}"
require_bounded_workload_iterations HDFS11741_BALANCER_REFRESH_ITERATIONS \
  "${hdfs11741_balancer_refresh_iterations}"
require_positive_integer HDFS11741_BALANCER_DISPATCHER_THREADS \
  "${hdfs11741_balancer_dispatcher_threads}"

publish_file_atomically() {
  local source=$1
  local destination=$2
  local temporary
  require_file "published artifact source" "${source}"
  mkdir -p "$(dirname "${destination}")"
  temporary=$(mktemp "${destination}.tmp.XXXXXX")
  cp "${source}" "${temporary}"
  mv -f "${temporary}" "${destination}"
}

terminate_process_tree() {
  local parent=$1
  local child
  local -a children=()
  if command -v pgrep >/dev/null 2>&1; then
    while IFS= read -r child; do
      [[ -n "${child}" ]] && children+=("${child}")
    done < <(pgrep -P "${parent}" 2>/dev/null || true)
    for child in "${children[@]}"; do
      terminate_process_tree "${child}"
    done
  fi
  kill "${parent}" >/dev/null 2>&1 || true
}

terminate_workers() {
  local pid
  for pid in "$@"; do
    terminate_process_tree "${pid}"
  done
  for pid in "$@"; do
    wait "${pid}" >/dev/null 2>&1 || true
  done
}

worker_signal_cleanup() {
  local pid
  while IFS= read -r pid; do
    [[ -n "${pid}" ]] && kill "${pid}" >/dev/null 2>&1 || true
  done < <(jobs -pr)
  wait >/dev/null 2>&1 || true
  exit 143
}

require_command() {
  command -v "$1" >/dev/null 2>&1 \
    || die "required command not found: $1"
}

require_file() {
  local label=$1
  local path=$2
  [[ -f "${path}" ]] || die "${label} not found: ${path}"
}

require_nonempty_file() {
  local label=$1
  local path=$2
  [[ -s "${path}" ]] || die "${label} is missing or empty: ${path}"
}

require_nonempty_directory() {
  local label=$1
  local path=$2
  local first_file
  [[ -d "${path}" ]] || die "${label} directory not found: ${path}"
  first_file=$(find "${path}" -type f -print -quit)
  [[ -n "${first_file}" ]] \
    || die "${label} directory contains no files: ${path}"
}

require_directory() {
  local label=$1
  local path=$2
  [[ -d "${path}" ]] || die "${label} directory not found: ${path}"
}

require_jsonl_contains() {
  local label=$1
  local path=$2
  local literal=$3
  rg -Fq -- "${literal}" "${path}" \
    || die "${label} missing from ${path}: ${literal}"
}

# Reads one top-level string field from the JSONL row on stdin without
# building the row.  A selected result carries the region's whole symbolic
# expression tree, which runs to hundreds of megabytes nested past jq's
# tree-parser depth limit; the stream stops at the field, so this stays fast
# however deep the row is, and the row itself is never held in a variable.
jsonl_stream_field() {
  local field=$1
  jq --stream -n -r --arg field "${field}" '
    first(inputs | select(length == 2 and .[0] == [$field]) | .[1]) // ""'
}

# Answers whether two rows sharing an identity carry the same content.  Equal
# bytes settle it outright, which is the whole answer for every identity whose
# normalization was already the identity function.  Only summaryId needs the
# taskId-insensitive form, and only when the bytes differ; a row too deep to
# rebuild cannot be compared that way, so it is refused rather than assumed
# equal.  Rebuilding is bounded because it happens only on that path.
jsonl_rows_agree() {
  local left_file=$1
  local left_line=$2
  local right_file=$3
  local right_line=$4
  local identity=$5
  local limit=$((8 * 1024 * 1024))
  local left right
  left=$(sed -n "${left_line}p" "${left_file}" | sha256sum)
  right=$(sed -n "${right_line}p" "${right_file}" | sha256sum)
  [[ "${left}" == "${right}" ]] && return 0
  [[ "${identity}" == "summaryId" ]] || return 1
  [[ "$(sed -n "${left_line}p" "${left_file}" | wc -c)" -le "${limit}" ]] \
    && [[ "$(sed -n "${right_line}p" "${right_file}" | wc -c)" \
      -le "${limit}" ]] \
    || return 1
  jq -e -n -s \
    --argjson a "$(sed -n "${left_line}p" "${left_file}")" \
    --argjson b "$(sed -n "${right_line}p" "${right_file}")" \
    '($a | del(.taskId)) == ($b | del(.taskId))' >/dev/null
}

require_unique_task_result() {
  local label=$1
  local path=$2
  local task_id=$3
  require_nonempty_file "${label}" "${path}"
  local event task total number results=0
  total=$(wc -l <"${path}")
  for ((number = 1; number <= total; number++)); do
    event=$(sed -n "${number}p" "${path}" | jsonl_stream_field event)
    task=$(sed -n "${number}p" "${path}" | jsonl_stream_field taskId)
    [[ "${task}" == "${task_id}" ]] \
      || die "${label} carries a row of another task (${task}): ${path}"
    case "${event}" in
      CONCOLIC_REGION_RESULT) results=$((results + 1)) ;;
      CONCOLIC_REGION_SKIPPED) ;;
      *) die "${label} carries an incompatible event (${event}): ${path}" ;;
    esac
  done
  [[ "${results}" -eq 1 ]] \
    || die "${label} must contain one selected result and only compatible skipped events: ${path}"
}

require_unique_complete_summary() {
  local label=$1
  local path=$2
  local task_id=$3
  require_nonempty_file "${label}" "${path}"
  # An imported summary carries the region's projected relation and can be
  # nested past jq's tree-parser depth limit, so read its two fields as a
  # stream rather than building the summary to look at them.
  [[ "$(wc -l <"${path}")" -eq 1 ]] \
    && [[ "$(jsonl_stream_field taskId <"${path}")" == "${task_id}" ]] \
    && [[ "$(jsonl_stream_field relationallyComplete <"${path}")" == true ]] \
    || die "${label} must contain one relationally complete summary for ${task_id}: ${path}"
}

reject_coordination_candidates() {
  local path=$1
  local candidates='RUNTIME_COORDINATED_STATE_FLOW|DECLARED_FIELD_COORDINATION_CANDIDATE_V1|FAILURE_SLICED_DECLARED_FIELD_FAMILY_V1'
  if rg -q -- "${candidates}" "${path}"; then
    die "declaration-only coordination candidate leaked into ${path}"
  fi
}

verify_checkout_lineage() {
  [[ -e "${hadoop_dir}/.git" ]] \
    || die "Hadoop checkout not found: ${hadoop_dir}"
  local head
  git -C "${hadoop_dir}" rev-parse --verify "${base_commit}^{commit}" \
    >/dev/null 2>&1 \
    || die "pre-fix Hadoop base is unavailable: ${base_commit}"
  head=$(git -C "${hadoop_dir}" rev-parse HEAD)
  git -C "${hadoop_dir}" merge-base --is-ancestor \
    "${base_commit}" "${head}" \
    || die "Hadoop HEAD ${head} is not based on pre-fix ${base_commit}"

  # Variants are controlled working-tree overlays on the audited pre-fix
  # lineage.  A descendant may add tracing support, but it must not commit a
  # different KeyManager implementation behind the variant selector.
  git -C "${hadoop_dir}" diff --quiet \
    "${base_commit}..${head}" -- "${key_manager_rel}" \
    || die "Hadoop descendant commits changes to ${key_manager_rel}; variants require the audited pre-fix lineage"
}

key_manager_method() {
  require_file "KeyManager source" "${key_manager_source}"
  sed -n \
    '/public DataEncryptionKey newDataEncryptionKey()/,/^  }/p' \
    "${key_manager_source}"
}

verify_variant_semantics() {
  local key_method normalized_method
  key_method=$(key_manager_method)
  [[ -n "${key_method}" ]] \
    || die "cannot attest KeyManager.newDataEncryptionKey()"
  normalized_method=$(tr '\n\t' '  ' <<<"${key_method}" \
    | sed -E 's/[[:space:]]+/ /g')
  case "${variant}" in
    vulnerable)
      case "${key_method}" in
        *expiryDate*|*isExpired*|*timer.now*|*Time.now*)
          die "variant vulnerable requires the pre-fix null-only key guard"
          ;;
      esac
      case "${normalized_method}" in
        *'if (encryptionKey == null) {'*) ;;
        *) die "variant vulnerable has no pre-fix null-only key guard" ;;
      esac
      ;;
    patched|patched-fault)
      rg -Fq 'import org.apache.hadoop.util.Time;' "${key_manager_source}" \
        || die "variant ${variant} requires the Time import"
      case "${normalized_method}" in
        *'if (encryptionKey == null || encryptionKey.expiryDate < Time.now()) {'*) ;;
        *) die "variant ${variant} requires the expiryDate < Time.now() key guard" ;;
      esac
      ;;
  esac
  if [[ "${variant}" == patched-fault ]]; then
    [[ -s "${symbolic_rpc_fault_patch_file}" ]] \
      || die "variant patched-fault is unavailable: missing nonempty ${symbolic_rpc_fault_patch_file}"
    patch_is_applied "${symbolic_rpc_fault_patch_file}" \
      || die "variant patched-fault requires its symbolic RPC fault patch"
  fi
}

verify_checkout() {
  if [[ "${variant}" == external ]]; then
    return
  fi
  verify_checkout_lineage
  verify_variant_semantics
}

patch_is_applied() {
  local patch=$1
  git -C "${hadoop_dir}" apply --reverse --check "${patch}" \
    >/dev/null 2>&1
}

apply_patch_once() {
  local label=$1
  local patch=$2
  require_file "${label} patch" "${patch}"
  if patch_is_applied "${patch}"; then
    echo "[hdfs-11741] ${label} patch is already applied"
    return
  fi
  git -C "${hadoop_dir}" apply --check "${patch}" \
    || die "${label} patch does not apply cleanly"
  git -C "${hadoop_dir}" apply "${patch}"
  patch_is_applied "${patch}" \
    || die "${label} patch failed post-apply verification"
  echo "[hdfs-11741] applied ${label} patch"
}

apply_runtime_patch() {
  if runtime_patch_is_applied; then
    echo "[hdfs-11741] runtime trace/workload patch is already applied"
    return
  fi
  apply_patch_once "runtime trace/workload" "${runtime_patch_file}"
}

runtime_patch_is_applied() {
  patch_is_applied "${runtime_patch_file}" \
    || (verify_runtime_patch_content >/dev/null 2>&1)
}

verify_runtime_patch_content() {
  local bridge="${hadoop_dir}/hadoop-common-project/hadoop-common/src/main/java/org/apache/hadoop/ipc/CausynthRpcTrace.java"
  require_file "Causynth RPC trace bridge" "${bridge}"
  rg -Fq 'recorderWithOwner.invoke(null, direction, transport, wireId, localOwner)' \
    "${bridge}" \
    || die "RPC trace bridge must call the endpoint-free recorder"
  if rg -q 'recordRpcEndpoint|String endpoint|payloadFingerprint|valueFingerprint' \
      "${bridge}"; then
    die "RPC trace bridge contains retired endpoint or payload state"
  fi
  require_jsonl_contains "deterministic key serial knob" \
    "${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/security/token/block/BlockTokenSecretManager.java" \
    'causynth.replay.block.key.serial.seed'
  require_jsonl_contains "NameNode activation knob" \
    "${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/blockmanagement/HeartbeatManager.java" \
    'hdfs11741.nn.update.iterations'
  require_jsonl_contains "DataNode activation knob" \
    "${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/datanode/BPOfferService.java" \
    'hdfs11741.datanode.refresh.iterations'
  require_jsonl_contains "Balancer activation knob" "${key_manager_source}" \
    'hdfs11741.balancer.refresh.iterations'
  require_jsonl_contains "Balancer dispatcher width knob" \
    "${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/src/test/java/org/apache/hadoop/hdfs/server/balancer/TestBalancer.java" \
    'hdfs11741.balancer.dispatcher.threads'
  if rg -qi 'fixed[- ]length|padding|Arrays\.copyOf' \
      "${runtime_patch_file}"; then
    die "runtime patch must not pad exported keys"
  fi
}

do_patch() {
  verify_checkout_lineage
  if [[ "${variant}" == patched-fault \
      && ! -s "${symbolic_rpc_fault_patch_file}" ]]; then
    die "variant patched-fault is unavailable: missing nonempty ${symbolic_rpc_fault_patch_file}"
  fi
  apply_runtime_patch
  apply_patch_once "fatal target" "${fatal_patch_file}"
  case "${variant}" in
    vulnerable) ;;
    patched|patched-fault)
      apply_patch_once "HDFS-11741 expiry guard" "${expiry_guard_patch_file}"
      ;;
  esac
  if [[ "${variant}" == patched-fault ]]; then
    apply_patch_once "symbolic RPC fault" "${symbolic_rpc_fault_patch_file}"
  fi
  verify_variant_semantics
  verify_runtime_patch_content
}

marker_is_applied() {
  patch_is_applied "${fatal_patch_file}"
}

verify_marker() {
  if [[ "${variant}" == external ]]; then
    return
  fi
  runtime_patch_is_applied \
    || die "runtime trace/workload patch is not applied; run: $0 prepare"
  marker_is_applied \
    || die "fatal-target patch is not applied; run: $0 prepare"
  verify_runtime_patch_content
}

ensure_java8() {
  require_command java
  local version
  version=$(java -version 2>&1 | sed -n '1p')
  case "${version}" in
    *\"1.8.*) ;;
    *) die "Hadoop baseline requires Java 8; found: ${version}" ;;
  esac
}

ensure_protoc() {
  local protoc=${HADOOP_PROTOC_PATH:-${cached_protoc}}
  if [[ ! -x "${protoc}" && -n "${HADOOP_PROTOC_PATH:-}" ]]; then
    die "HADOOP_PROTOC_PATH is not executable: ${protoc}"
  fi
  if [[ ! -x "${protoc}" ]]; then
    require_command curl
    require_command sha256sum
    mkdir -p "$(dirname "${cached_protoc}")"
    local staging
    staging=$(mktemp -d /tmp/hdfs-11741-protoc.XXXXXX)
    echo "[hdfs-11741] downloading protoc 2.5.0" >&2
    curl -fsSL \
      https://repo.maven.apache.org/maven2/com/google/protobuf/protoc/2.5.0/protoc-2.5.0-linux-x86_64.exe \
      -o "${staging}/protoc"
    echo "${protoc_sha256}  ${staging}/protoc" | sha256sum -c - \
      >/dev/null
    chmod 755 "${staging}/protoc"
    mv "${staging}/protoc" "${cached_protoc}"
    rmdir "${staging}"
    protoc=${cached_protoc}
  fi
  local version
  version=$("${protoc}" --version)
  [[ "${version}" == "libprotoc 2.5.0" ]] \
    || die "expected libprotoc 2.5.0; found: ${version}"
  printf '%s\n' "${protoc}"
}

do_build() {
  verify_checkout
  verify_marker
  ensure_java8
  require_command mvn
  local protoc
  protoc=$(ensure_protoc)
  (
    cd "${hadoop_dir}"
    HADOOP_PROTOC_PATH="${protoc}" mvn \
      -pl hadoop-common-project/hadoop-annotations,hadoop-hdfs-project/hadoop-hdfs \
      -am -DskipTests install
  )
}

do_classpath() {
  verify_checkout
  verify_marker
  require_command mvn
  [[ -f "${hdfs_pom}" ]] || die "HDFS POM not found: ${hdfs_pom}"
  [[ -d "${hdfs_main_classes}" ]] || die "main classes not built; run: $0 prepare"
  [[ -d "${hdfs_test_classes}" ]] || die "test classes not built; run: $0 prepare"
  mkdir -p "${work_root}"
  mvn -q -f "${hdfs_pom}" \
    -DincludeScope=test \
    -Dmdep.outputAbsoluteArtifactFilename=true \
    -Dmdep.outputFile="${dependency_classpath}" \
    dependency:build-classpath
  local dependencies
  dependencies=$(tr -d '\r\n' < "${dependency_classpath}")
  [[ -n "${dependencies}" ]] || die "Maven produced an empty classpath"
  printf '%s:%s:%s\n' \
    "${hdfs_main_classes}" "${hdfs_test_classes}" "${dependencies}" \
    >"${project_classpath}"
  local entry
  local entries=0
  while IFS= read -r entry; do
    [[ -e "${entry}" ]] || die "classpath entry does not exist: ${entry}"
    entries=$((entries + 1))
  done < <(tr ':' '\n' < "${project_classpath}")
  echo "[hdfs-11741] classpath ready: ${entries} entries"
  echo "[hdfs-11741] ${project_classpath}"
}

do_baseline() {
  verify_checkout
  verify_marker
  ensure_java8
  require_command mvn
  local protoc
  protoc=$(ensure_protoc)
  (
    cd "${hadoop_dir}"
    HADOOP_PROTOC_PATH="${protoc}" mvn -f "${hdfs_pom}" \
      -Dtest="${test_selector}" test
  )
  [[ -f "${test_report}" ]] \
    || die "Surefire report not found: ${test_report}"
  require_command rg
  local suite
  suite=$(sed -n '2p' "${test_report}")
  case "${suite}" in
    *'tests="1"'*'errors="0"'*'skipped="0"'*'failures="0"'*) ;;
    *) die "unexpected Surefire result: ${suite}" ;;
  esac
  rg -Fq "<testcase name=\"${test_method}\"" "${test_report}" \
    || die "Surefire report did not contain ${test_method}"
  echo "[hdfs-11741] baseline passed: ${test_selector}"
}

do_prepare() {
  do_patch
  do_build
  do_classpath
  do_baseline
}

verify_static_artifacts() {
  local analysis="${work_root}/analysis"
  require_nonempty_file "resolved target" \
    "${analysis}/target_resolved.json"
  require_nonempty_file "candidate dataflow graph" \
    "${analysis}/candidate_dataflow_edges.jsonl.gz"
  require_nonempty_file "region skeleton archive" \
    "${analysis}/region_skeletons.jsonl.gz"
  require_nonempty_directory "instrumented classes" \
    "${work_root}/instrumented-classes"
}

verify_runtime_artifacts() {
  local runtime="${work_root}/runtime"
  local runtime_plan="${runtime}/concolic_region_plan.jsonl"
  require_command rg
  require_command jq
  verify_region_artifacts
  require_nonempty_file "pass-2 runtime trace" \
    "${runtime}/runtime_trace.jsonl"
  require_nonempty_file "pass-2 streaming manifest" \
    "${runtime}/streaming_trace_manifest.json"
  require_nonempty_file "runtime-refined graph" \
    "${runtime}/refined_dataflow_edges.jsonl.gz"
  require_nonempty_file "runtime region plan" \
    "${runtime_plan}"
  jq -e -s '.[0].kind == "CONCOLIC_RUNTIME_MODEL_CATALOG" and
    ((.[0].regions // []) | length > 0)' "${runtime_plan}" >/dev/null \
    || die "runtime plan has no compact region catalog: ${runtime_plan}"

  if [[ "${variant}" == external ]]; then
    return
  fi

  local root
  local core_roots=(
    'HeartbeatManager$Monitor: void run()'
    'NameNodeRpcServer: org.apache.hadoop.hdfs.security.token.block.ExportedBlockKeys getBlockKeys()'
    'KeyManager$BlockKeyUpdater: void run()'
    'Dispatcher$1: void run()'
    'NameNodeRpcServer: org.apache.hadoop.hdfs.server.protocol.HeartbeatResponse sendHeartbeat('
    'BPServiceActor: void run()'
    'DataXceiver: void run()'
  )
  for root in "${core_roots[@]}"; do
    require_jsonl_contains "core runtime region" "${runtime_plan}" "${root}"
  done
  jq -e -s '
    any(.[0].edges[]?;
      .kind == "RUNTIME_FIELD_FLOW" and
      .bindingKind == "CONTAINER_MUTATION" and
      ((.fieldPathDeclarations // []) |
        index("<org.apache.hadoop.hdfs.security.token.block.BlockTokenSecretManager: java.util.Map allKeys>") != null))
  ' "${runtime_plan}" >/dev/null \
    || die "exact runtime allKeys container flow missing from ${runtime_plan}"
  require_jsonl_contains "trusted runtime RPC" "${runtime_plan}" \
    '"state":"CONFIRMED_TRUSTED_CONFIGURED_RPC"'
  require_jsonl_contains "trusted runtime RPC authority" "${runtime_plan}" \
    '"correlationAuthority":"TRUSTED_CONFIGURED_RPC_MAPPING_V1"'
  reject_coordination_candidates "${runtime_plan}"
}

verify_region_artifacts() {
  local runtime="${work_root}/runtime"
  local skeleton="${runtime}/skeleton-pass"
  require_nonempty_file "pass-1 selected region skeletons" \
    "${skeleton}/region_skeletons.jsonl"
  require_nonempty_file "pass-1 runtime trace" \
    "${skeleton}/runtime_trace.jsonl"
  require_nonempty_file "pass-1 streaming manifest" \
    "${skeleton}/streaming_trace_manifest.json"
}

verify_task_artifacts() {
  local schedule="${work_root}/schedule"
  local tasks="${schedule}/execution_task_plan.jsonl"
  local workflow_index="${schedule}/runtime_workflow_schedule_index.json"
  local plan_sha task_sha plan_size task_size
  require_command jq
  require_nonempty_file "concolic execution task plan" "${tasks}"
  require_file "branch query plan" "${schedule}/branch_queries.jsonl"
  require_nonempty_file "target-first workflow index" "${workflow_index}"
  reject_coordination_candidates "${tasks}"
  jq -e -s '
    length > 0 and
    any(.[]; .admission.state == "EXECUTABLE") and
    all(.[];
      all([.taskId, .goalId, .regionId, .sourceKey, .occurrenceId,
           .relationKey, .relationContractHash][];
          type == "string" and length > 0) and
      (.goalKind == "TARGET_REACH_CLOSURE" or
        .goalKind == "OUTPUT_RELATION_CLOSURE") and
      (.inputActions | type == "array") and
      (.branches | type == "array") and
      (.admission.state == "EXECUTABLE" or
        .admission.state == "BLOCKED") and
      .loopBound.schemaVersion == 1 and
      .loopBound.kind == "CFG_BACKEDGE" and
      .loopBound.scope == "ALL_EXECUTION_SCOPE_LOOPS" and
      .loopBound.maxBackedgeTraversals == 8 and
      .loopBound.onLimit == "CUT_PATH")
  ' "${tasks}" >/dev/null \
    || die "execution task plan failed identity/admission/loopBound validation: ${tasks}"
  if [[ -s "${schedule}/branch_queries.jsonl" ]]; then
    jq -e -s 'all(.[]; type == "object")' \
      "${schedule}/branch_queries.jsonl" >/dev/null \
      || die "branch query plan is not valid JSONL: ${schedule}/branch_queries.jsonl"
  fi
  plan_sha=$(sha256sum "${region_plan}" | cut -d' ' -f1)
  task_sha=$(sha256sum "${tasks}" | cut -d' ' -f1)
  plan_size=$(stat -c '%s' "${region_plan}")
  task_size=$(stat -c '%s' "${tasks}")
  jq -e --arg planSha "${plan_sha}" --arg taskSha "${task_sha}" \
      --argjson planSize "${plan_size}" \
      --argjson taskSize "${task_size}" \
      --slurpfile tasks "${tasks}" '
      def matches($entry; $kind):
        ([$tasks[] | select(.taskId == $entry.taskId)]) as $matched
        | ($matched | length) == 1
          and $matched[0].regionId == $entry.regionId
          and $matched[0].relationKey == $entry.relationKey
          and $matched[0].occurrenceId == $entry.occurrenceId
          and $matched[0].goalId == $entry.goalId
          and $matched[0].goalKind == $kind
          and $matched[0].admission.state == "EXECUTABLE";
      .schemaVersion == 1 and
      .kind == "RUNTIME_TARGET_FIRST_SCHEDULE_INDEX" and
      .selectionAuthority ==
        "RANKED_EXACT_RUNTIME_READ_FROM_CLOSURE_V1" and
      .regionPlan.sha256 == $planSha and
      .regionPlan.sizeBytes == $planSize and
      .executionTaskPlan.sha256 == $taskSha and
      .executionTaskPlan.sizeBytes == $taskSize and
      all([.target.campaignId, .target.regionId, .target.relationKey,
           .target.occurrenceId, .target.goalId, .target.taskId][];
          type == "string" and length > 0) and
      (.producers | type == "array" and length > 0) and
      (([.target.taskId] + [.producers[].taskId]) as $indexedIds
        | ($indexedIds | length) == ($indexedIds | unique | length)) and
      (($tasks | map(.taskId) | length) ==
        ($tasks | map(.taskId) | unique | length)) and
      (([.target.taskId] + [.producers[].taskId] | sort) ==
        ($tasks | map(.taskId) | sort)) and
      matches(.target; "TARGET_REACH_CLOSURE") and
      all(.producers[]; matches(.; "OUTPUT_RELATION_CLOSURE"))
  ' "${workflow_index}" >/dev/null \
    || die "target-first workflow index failed integrity validation: ${workflow_index}"
}

do_engine_config() {
  local command=$1
  shift
  [[ -s "${project_classpath}" ]] \
    || die "project classpath not found; run: $0 prepare"
  local classpath
  classpath=$(tr -d '\r\n' < "${project_classpath}")
  (
    cd "${graphchecker_dir}"
    # Path env overrides keep every engine artifact rooted at the selected
    # work root, whichever root (default, legacy, or HDFS11741_WORK_ROOT)
    # was chosen above.  Values already present in the environment win, so
    # per-campaign overrides (e.g. seed instrumentation) are preserved.
    CAUSYNTH_REPO="${hadoop_dir}" \
      CAUSYNTH_CLASSPATH="${classpath}" \
      CAUSYNTH_OUTPUT_DIR="${CAUSYNTH_OUTPUT_DIR:-${work_root}/analysis}" \
      CAUSYNTH_INSTRUMENTED_CLASSES_DIR="${CAUSYNTH_INSTRUMENTED_CLASSES_DIR:-${work_root}/instrumented-classes}" \
      CAUSYNTH_REGION_PLAN="${CAUSYNTH_REGION_PLAN:-${work_root}/runtime/concolic_region_plan.jsonl}" \
      CAUSYNTH_SCHEDULE_OUTPUT_DIR="${CAUSYNTH_SCHEDULE_OUTPUT_DIR:-${work_root}/schedule}" \
      ./run_engine.sh --config "${workflow}" "${command}" "$@"
  )
}

configured_value() {
  local key=$1
  local normalized value
  normalized=$(do_engine_config config)
  value=$(sed -n "s/^${key}=//p" <<< "${normalized}")
  [[ -n "${value}" ]] || die "workflow configuration has no ${key}"
  printf '%s\n' "${value}"
}

# A task id identifies what to replay, not which VM/runtime semantics produced
# its summary.  Keep that second identity beside every reusable campaign so a
# rebuilt concolic VM or GraphChecker runtime cannot silently reuse relations
# emitted by older code.
class_tree_digest() {
  local label=$1
  local root=$2
  require_directory "${label}" "${root}"
  [[ -n "$(find "${root}" -type f -name '*.class' -print -quit)" ]] \
    || die "${label} contains no class files: ${root}"
  (
    cd "${root}"
    find . -type f -name '*.class' -print0 \
      | LC_ALL=C sort -z \
      | xargs -0 -r sha256sum -z -- \
      | LC_ALL=C sed -zE 's/^([0-9a-f]{64})  (.*)$/\2\t\1/' \
      | tr '\0' '\n' \
      | head -c -1
  ) | sha256sum | cut -d' ' -f1
}

initialize_replay_engine_fingerprint() {
  local tools_jar runtime_jar jdk libjvm main_classes_digest
  local test_classes_digest instrumented_classes_digest
  local -a libjvms=()
  tools_jar=$(configured_value graphchecker_jar)
  runtime_jar="${graphchecker_dir}/target/GraphChecker-1.0-SNAPSHOT.jar"
  jdk=$(configured_value custom_jdk_home)
  require_file "GraphChecker tool jar" "${tools_jar}"
  require_file "GraphChecker runtime jar" "${runtime_jar}"
  require_directory "custom concolic JDK" "${jdk}"
  while IFS= read -r libjvm; do
    [[ -n "${libjvm}" ]] && libjvms+=("${libjvm}")
  done < <(find "${jdk}" -type f \
    \( -name libjvm.so -o -name libjvm.dylib -o -name jvm.dll \) \
    -print | sort)
  (( ${#libjvms[@]} == 1 )) \
    || die "expected one custom VM library under ${jdk}; found ${#libjvms[@]}"
  main_classes_digest=$(class_tree_digest "HDFS main classes" \
    "${hdfs_main_classes}")
  test_classes_digest=$(class_tree_digest "HDFS test classes" \
    "${hdfs_test_classes}")
  instrumented_classes_digest=$(class_tree_digest "instrumented HDFS classes" \
    "${work_root}/instrumented-classes")
  replay_engine_fingerprint=$({
    printf '%s\n' 'HDFS11741_REPLAY_ENGINE_V1'
    sha256sum "${tools_jar}" "${runtime_jar}" "${libjvms[0]}"
    printf '%s\n' \
      "variant=${variant}" \
      "hdfsMainClasses=${main_classes_digest}" \
      "hdfsTestClasses=${test_classes_digest}" \
      "instrumentedHdfsClasses=${instrumented_classes_digest}" \
      "blockKeySerialSeed=${HDFS11741_BLOCK_KEY_SERIAL_SEED:-11741}" \
      "testCapacity=${HDFS11741_TEST_CAPACITY:-1000}" \
      "heartbeatRecheckMs=${HDFS11741_HEARTBEAT_RECHECK_MS:-300000}" \
      "keyUpdateIntervalMinutes=${HDFS11741_KEY_UPDATE_INTERVAL_MINUTES:-0}" \
      "nnUpdateIterations=${hdfs11741_nn_update_iterations}" \
      "datanodeRefreshIterations=${hdfs11741_datanode_refresh_iterations}" \
      "balancerRefreshIterations=${hdfs11741_balancer_refresh_iterations}" \
      "balancerDispatcherThreads=${hdfs11741_balancer_dispatcher_threads}"
  } | sha256sum | cut -d' ' -f1)
}

seed_campaign_cache_key() {
  local canonical_task=$1
  [[ -n "${replay_engine_fingerprint}" ]] \
    || die "replay engine fingerprint was not initialized"
  {
    printf '%s\n' "${replay_engine_fingerprint}"
    printf '%s\n' "${canonical_task}"
  } | sha256sum | cut -d' ' -f1
}

run_graphchecker_main() {
  local main_class=$1
  shift
  local jar java_bin
  jar=$(configured_value graphchecker_jar)
  java_bin=$(configured_value java_bin)
  require_file "GraphChecker tool jar" "${jar}"
  (cd "${graphchecker_dir}" && "${java_bin}" -cp "${jar}" \
    "${main_class}" "$@")
}

# Schedules the complete ranked closure in one JVM.  Discovery and scheduler
# indices share one parse of the large runtime plan; the compact index is
# published last and acts as the integrity-checked commit record consumed by
# candidates.
schedule_target_first_closure() {
  local max_jobs=$1
  local schedule="${work_root}/schedule"
  local staging task_count producer_count
  mkdir -p "${work_root}"
  staging=$(mktemp -d "${work_root}/schedule-stage.XXXXXX")

  do_engine_config schedule --output-dir "${staging}" \
    --target-first --max-jobs "${max_jobs}"
  require_nonempty_file "target-first execution task plan" \
    "${staging}/execution_task_plan.jsonl"
  require_file "target-first branch query plan" \
    "${staging}/branch_queries.jsonl"
  require_file "symbolic input selection audit" \
    "${staging}/symbolic_input_selections.jsonl"
  require_nonempty_file "target-first workflow index" \
    "${staging}/runtime_workflow_schedule_index.json"

  task_count=$(jq -s 'length' \
    "${staging}/execution_task_plan.jsonl")
  producer_count=$(jq -r '.producers | length' \
    "${staging}/runtime_workflow_schedule_index.json")
  [[ "${task_count}" -eq $((1 + producer_count)) ]] \
    || die "target-first index/task count mismatch; staging retained at ${staging}"

  mkdir -p "${schedule}"
  publish_file_atomically "${staging}/execution_task_plan.jsonl" \
    "${schedule}/execution_task_plan.jsonl"
  publish_file_atomically "${staging}/branch_queries.jsonl" \
    "${schedule}/branch_queries.jsonl"
  publish_file_atomically "${staging}/symbolic_input_selections.jsonl" \
    "${schedule}/symbolic_input_selections.jsonl"
  publish_file_atomically \
    "${staging}/runtime_workflow_schedule_index.json" \
    "${schedule}/runtime_workflow_schedule_index.json"
  rm -f -- "${schedule}/selected_target_binding.tsv" \
    "${schedule}/selected_closure_bindings.tsv"
  rm -rf -- "${staging}"
  echo "[hdfs-11741] scheduled ranked exact closure: 1 target + ${producer_count} producer logical goal(s)"
}

do_tasks() {
  local max_jobs=${HDFS11741_SCHEDULE_MAX_JOBS:-4096}
  [[ "${max_jobs}" =~ ^[1-9][0-9]*$ ]] \
    || die "HDFS11741_SCHEDULE_MAX_JOBS must be a positive integer"
  verify_checkout
  verify_marker
  echo "[hdfs-11741] stage 1/3: static analysis"
  do_engine_config analyze
  verify_static_artifacts
  echo "[hdfs-11741] stage 2/3: two-pass runtime refinement"
  do_engine_config workload
  verify_runtime_artifacts
  echo "[hdfs-11741] stage 3/3: schedule concolic tasks"
  schedule_target_first_closure "${max_jobs}"
  verify_task_artifacts
  echo "[hdfs-11741] task preparation complete: ${work_root}/schedule/execution_task_plan.jsonl"
}

# Rebuild only the target-first schedule from an already completed runtime
# refinement.  This keeps planner/contract fixes resumable without repeating
# the expensive HDFS workload.
do_schedule() {
  local max_jobs=${HDFS11741_SCHEDULE_MAX_JOBS:-4096}
  [[ "${max_jobs}" =~ ^[1-9][0-9]*$ ]] \
    || die "HDFS11741_SCHEDULE_MAX_JOBS must be a positive integer"
  verify_checkout
  verify_marker
  verify_runtime_artifacts
  schedule_target_first_closure "${max_jobs}"
  verify_task_artifacts
  echo "[hdfs-11741] schedule rebuilt: ${work_root}/schedule/execution_task_plan.jsonl"
}

seed_campaign_group() {
  case "$1" in
    OUTPUT_RELATION_CLOSURE) printf '%s\n' producer ;;
    TARGET_REACH_CLOSURE) printf '%s\n' target ;;
    *) die "unsupported executable goal kind: $1" ;;
  esac
}

seed_campaign_directory() {
  local goal_kind=$1
  local task_id=$2
  local group
  group=$(seed_campaign_group "${goal_kind}")
  printf '%s/%s/%s\n' "${seed_campaign_root}" "${group}" "${task_id}"
}

# The schedule is the sole owner of auto-seed cache reachability. Old task
# ids otherwise retain a complete instrumented class tree indefinitely.
prune_stale_seed_campaigns() {
  local schedule_plan=$1
  local goal_kind task_id group group_dir campaign base
  declare -A keep_target=() keep_producer=()
  while IFS=$'\t' read -r goal_kind task_id; do
    [[ "${task_id}" == TASK.SEED.* ]] \
      || die "invalid scheduled seed task id: ${task_id}"
    case "${goal_kind}" in
      TARGET_REACH_CLOSURE) keep_target["${task_id}"]=1 ;;
      OUTPUT_RELATION_CLOSURE) keep_producer["${task_id}"]=1 ;;
    esac
  done < <(jq -r '[.goalKind,.taskId] | @tsv' "${schedule_plan}")

  for group in target producer; do
    group_dir="${seed_campaign_root}/${group}"
    [[ -d "${group_dir}" ]] || continue
    while IFS= read -r -d '' campaign; do
      base=${campaign##*/}
      [[ "${base}" == TASK.SEED.* ]] \
        || die "refusing to prune unexpected campaign: ${campaign}"
      if [[ "${group}" == target ]]; then
        [[ -n "${keep_target[${base}]+x}" ]] && continue
      else
        [[ -n "${keep_producer[${base}]+x}" ]] && continue
      fi
      rm -rf -- "${campaign}"
    done < <(find "${group_dir}" -mindepth 1 -maxdepth 1 -type d \
      -name 'TASK.SEED.*' -print0)
  done
}

prepare_seed_campaign() {
  local schedule_plan=$1
  local task_id=$2
  local goal_kind=$3
  local campaign singleton results summaries classes cache_marker
  local canonical_schedule canonical_singleton expected_cache_key
  campaign=$(seed_campaign_directory "${goal_kind}" "${task_id}")
  singleton="${campaign}/execution_task_plan.jsonl"
  results="${campaign}/seed-results.jsonl"
  summaries="${campaign}/seed-summaries.jsonl"
  classes="${campaign}/classes"
  cache_marker="${campaign}/replay-cache-key.sha256"
  canonical_schedule=$(jq -ceS -s --arg task "${task_id}" \
    --arg goalKind "${goal_kind}" '
      [.[] | select(.taskId == $task)]
      | if length == 1
          and .[0].admission.state == "EXECUTABLE"
          and .[0].goalKind == $goalKind
        then .[0]
        else error("expected one executable scheduled task") end
    ' "${schedule_plan}") \
    || die "unknown or non-executable scheduled task: ${task_id}"
  expected_cache_key=$(seed_campaign_cache_key "${canonical_schedule}")

  if [[ -e "${campaign}" ]]; then
    [[ -d "${campaign}" ]] \
      || die "seed campaign path is not a directory: ${campaign}"
    if [[ ! -s "${cache_marker}" \
        || "$(tr -d '\r\n' <"${cache_marker}")" \
          != "${expected_cache_key}" ]]; then
      case "${campaign}" in
        "${seed_campaign_root}"/producer/TASK.SEED.*|\
        "${seed_campaign_root}"/target/TASK.SEED.*) ;;
        *) die "refusing to invalidate unexpected campaign path: ${campaign}" ;;
      esac
      echo "[hdfs-11741] invalidate stale replay campaign: ${campaign}" >&2
      rm -rf -- "${campaign}"
    fi
  fi

  if [[ -e "${campaign}" ]]; then
    require_nonempty_file "seed campaign singleton" "${singleton}"
    require_nonempty_file "seed campaign result" "${results}"
    require_nonempty_file "seed campaign summary" "${summaries}"
    require_directory "seed campaign classes" "${classes}"
    canonical_singleton=$(jq -ceS -s '
      if length == 1 then .[0]
      else error("expected one singleton task") end
    ' "${singleton}") \
      || die "invalid seed campaign singleton: ${singleton}"
    [[ "${canonical_singleton}" == "${canonical_schedule}" ]] \
      || die "seed campaign task payload differs from schedule: ${campaign}"
    require_unique_task_result "seed campaign result" "${results}" \
      "${task_id}"
    require_unique_complete_summary "seed campaign summary" "${summaries}" \
      "${task_id}"
    printf 'REUSE\t%s\t%s\n' "${campaign}" "${expected_cache_key}"
    return
  fi

  mkdir -p "${campaign}"
  printf '%s\n' "${canonical_schedule}" >"${singleton}"
  printf 'NEW\t%s\t%s\n' "${campaign}" "${expected_cache_key}"
}

publish_seed_campaign_cache_key() {
  local campaign=$1
  local cache_key=$2
  local marker="${campaign}/replay-cache-key.sha256"
  local temporary
  temporary=$(mktemp "${marker}.tmp.XXXXXX")
  printf '%s\n' "${cache_key}" >"${temporary}"
  mv -f "${temporary}" "${marker}"
}

instrument_seed_task() {
  local campaign=$1
  local task_id=$2
  local singleton="${campaign}/execution_task_plan.jsonl"
  local classes="${campaign}/classes"
  # Soot's class output and every auxiliary analysis artifact are campaign
  # private.  This is what makes independent region instrumentation safe to
  # run concurrently.
  CAUSYNTH_OUTPUT_DIR="${campaign}/analysis" \
    CAUSYNTH_INSTRUMENTED_CLASSES_DIR="${classes}" \
    CAUSYNTH_INSTRUMENT_CONCOLIC=true \
    CAUSYNTH_CONCOLIC_TASK_PLAN="${singleton}" \
    CAUSYNTH_CONCOLIC_TASK_ID="${task_id}" \
    do_engine_config analyze
  [[ -d "${classes}" ]] \
    || die "concolic instrumentation emitted no classes: ${classes}"
}

replay_concolic_plan() {
  local singleton=$1
  local task_id=$2
  local classes=$3
  local results=$4
  local campaign=$5
  local replay_timeout_s=${6:-${HDFS11741_REPLAY_TIMEOUT_S:-2400}}
  local hadoop_log_dir="${campaign}/hadoop-logs"
  local normalized jdk graphchecker_jar classpath java_path
  local maven_repository gson_jar replay_status
  normalized=$(do_engine_config config)
  jdk=$(sed -n 's/^custom_jdk_home=//p' <<< "${normalized}")
  [[ -n "${jdk}" ]] \
    || die "workflow configuration has no custom_jdk_home"
  # Keep Hadoop's historical dependency versions authoritative.  The fat
  # GraphChecker jar is for standalone planner tools; replay uses the thin
  # runtime jar after the Hadoop test classpath.
  graphchecker_jar="${graphchecker_dir}/target/GraphChecker-1.0-SNAPSHOT.jar"
  classpath=$(tr -d '\r\n' < "${project_classpath}")
  maven_repository=$(mvn -q help:evaluate \
    -Dexpression=settings.localRepository -DforceStdout 2>/dev/null)
  gson_jar="${maven_repository}/com/google/code/gson/gson/2.10.1/gson-2.10.1.jar"
  java_path="${jdk}/bin/java"
  [[ -x "${java_path}" ]] || die "custom JDK is not built: ${java_path}"
  [[ -f "${graphchecker_jar}" ]] \
    || die "GraphChecker runtime jar not found: ${graphchecker_jar}"
  [[ -f "${gson_jar}" ]] \
    || die "GraphChecker Gson jar not found: ${gson_jar}"
  [[ -d "${classes}" ]] \
    || die "concolic classes not found: ${classes}"
  [[ ! -e "${results}" ]] || die "replay output already exists: ${results}"
  mkdir -p "${hadoop_log_dir}" "${campaign}/test-data" \
    "${campaign}/java-tmp"

  # A replay is bounded in the paths it may walk, not in what walking them
  # costs, and the workload's own timeout is disabled so that a replay may
  # finish its region.  Without a wall-clock budget one path can hold the
  # round open indefinitely; with one, it ends like any other flip that costs
  # more than it is worth -- abandoned by the caller, and named.
  set +e
  (cd "${graphchecker_dir}" && \
      env -u CAUSYNTH_CONCOLIC_TASK_ID -u CAUSYNTH_TRACE_OUTPUT_DIR \
      timeout --signal=TERM --kill-after=60 \
        "${replay_timeout_s}" \
      "${java_path}" \
        -Xint \
        -Xmx"${HDFS11741_CONCOLIC_HEAP:-2g}" \
        -XX:ErrorFile="${campaign}/hs_err_pid%p.log" \
        -Dcausynth.trace.test="${test_class}.${test_method}" \
        -Dcausynth.concolic.task.plan="${singleton}" \
        -Dcausynth.concolic.task.id="${task_id}" \
        -Dcausynth.concolic.results="${results}" \
        -Dcausynth.concolic.halt.after.selected.result=true \
        -Dcausynth.concolic.engine.wait.millis="${HDFS11741_ENGINE_WAIT_MS:-60000}" \
        -Dcausynth.junit.exit.after.run=true \
        -Dcausynth.junit.ignore.timeout=true \
        -Dtest.build.data="${campaign}/test-data" \
        -Djava.io.tmpdir="${campaign}/java-tmp" \
        -Dcausynth.replay.block.key.serial.seed="${HDFS11741_BLOCK_KEY_SERIAL_SEED:-11741}" \
        -Dhdfs11741.test.capacity="${HDFS11741_TEST_CAPACITY:-1000}" \
        -Dhdfs11741.test.timeout.ms="${HDFS11741_TEST_TIMEOUT_MS:-240000}" \
        -Dhdfs11741.heartbeat.recheck.ms="${HDFS11741_HEARTBEAT_RECHECK_MS:-300000}" \
        -Dhdfs11741.key.update.interval.minutes="${HDFS11741_KEY_UPDATE_INTERVAL_MINUTES:-0}" \
        -Dhdfs11741.nn.update.iterations="${hdfs11741_nn_update_iterations}" \
        -Dhdfs11741.datanode.refresh.iterations="${hdfs11741_datanode_refresh_iterations}" \
        -Dhdfs11741.balancer.refresh.iterations="${hdfs11741_balancer_refresh_iterations}" \
        -Dhdfs11741.balancer.dispatcher.threads="${hdfs11741_balancer_dispatcher_threads}" \
        -Dhadoop.log.dir="${hadoop_log_dir}" \
        -cp "${classes}:${gson_jar}:${classpath}:${graphchecker_jar}" \
        edu.uva.liftlab.graphchecker.runtime.JUnitMethodRunner \
        "${test_class}" "${test_method}")
  replay_status=$?
  set -e
  require_unique_task_result "raw concolic result" "${results}" \
    "${task_id}"
  if [[ "${replay_status}" -ne 0 ]]; then
    echo "[hdfs-11741] accepted replay exit ${replay_status}; selected result is durable"
  fi
}

replay_seed_task() {
  local campaign=$1
  local task_id=$2
  replay_concolic_plan "${campaign}/execution_task_plan.jsonl" \
    "${task_id}" "${campaign}/classes" "${campaign}/seed-results.jsonl" \
    "${campaign}"
}

import_seed_task() {
  local campaign=$1
  local task_id=$2
  local singleton="${campaign}/execution_task_plan.jsonl"
  local results="${campaign}/seed-results.jsonl"
  local summaries="${campaign}/seed-summaries.jsonl"
  run_concolic_import "${singleton}" "${results}" "${summaries}" \
    "${campaign}"
  require_unique_complete_summary "imported seed summary" "${summaries}" \
    "${task_id}"
}

run_seed_task() {
  local schedule_plan=$1
  local task_id=$2
  local goal_kind=$3
  local prepared state campaign cache_key
  prepared=$(prepare_seed_campaign \
    "${schedule_plan}" "${task_id}" "${goal_kind}")
  IFS=$'\t' read -r state campaign cache_key <<< "${prepared}"
  if [[ "${state}" == "REUSE" ]]; then
    echo "[hdfs-11741] reuse ${goal_kind} seed: ${task_id}"
    return
  fi
  [[ "${state}" == "NEW" && -n "${campaign}" \
      && -n "${cache_key}" ]] \
    || die "invalid seed campaign preparation state: ${prepared}"
  echo "[hdfs-11741] seed ${goal_kind}: ${task_id}"
  instrument_seed_task "${campaign}" "${task_id}"
  replay_seed_task "${campaign}" "${task_id}"
  import_seed_task "${campaign}" "${task_id}"
  publish_seed_campaign_cache_key "${campaign}" "${cache_key}"
}

run_seed_tasks_parallel() {
  local schedule_plan=$1
  shift
  local spec goal_kind task_id pid status index next=0
  local -a specs=("$@") batch=() labels=() failures=()
  declare -A seen=()
  local -a unique=()

  require_positive_integer HDFS11741_REGION_JOBS "${region_parallelism}"
  announce_parallelism "region seed campaigns" HDFS11741_REGION_JOBS \
    "${region_parallelism}"
  for spec in "${specs[@]}"; do
    IFS=$'\t' read -r goal_kind task_id <<< "${spec}"
    [[ -n "${goal_kind}" && -n "${task_id}" ]] \
      || die "invalid seed campaign specification: ${spec}"
    if [[ -z "${seen[${goal_kind}:${task_id}]+x}" ]]; then
      seen[${goal_kind}:${task_id}]=1
      unique+=("${goal_kind}"$'\t'"${task_id}")
    fi
  done
  (( ${#unique[@]} > 0 )) || die "no seed campaign to execute"

  echo "[hdfs-11741] seeding ${#unique[@]} region campaign(s), ${region_parallelism} in parallel"
  while (( next < ${#unique[@]} )); do
    batch=()
    labels=()
    while (( next < ${#unique[@]} \
        && ${#batch[@]} < region_parallelism )); do
      IFS=$'\t' read -r goal_kind task_id <<< "${unique[$next]}"
      (
        trap worker_signal_cleanup TERM INT
        set -euo pipefail
        run_seed_task "${schedule_plan}" "${task_id}" "${goal_kind}"
      ) &
      pid=$!
      batch+=("${pid}")
      labels+=("${goal_kind} ${task_id}")
      next=$((next + 1))
    done
    # One campaign that cannot seed says nothing about the others, and
    # stopping here would hide every remaining failure behind the first.
    # Run the whole closure, then report all of them together.
    for index in "${!batch[@]}"; do
      set +e
      wait "${batch[$index]}"
      status=$?
      set -e
      if [[ "${status}" -ne 0 ]]; then
        failures+=("${labels[$index]} (exit ${status})")
        echo "[hdfs-11741] region seed failed: ${labels[$index]} (exit ${status})" >&2
      fi
    done
  done
  if (( ${#failures[@]} > 0 )); then
    for spec in "${failures[@]}"; do
      echo "[hdfs-11741] unseeded region campaign: ${spec}" >&2
    done
    echo "[hdfs-11741] continuing with observed relations; ${#failures[@]} of ${#unique[@]} region seed campaign(s) are coverage gaps" >&2
  fi
  if command -v hardlink >/dev/null 2>&1; then
    hardlink --quiet --content --include '\.class$' \
      "${seed_campaign_root}"
  fi
}

combine_jsonl_unique() {
  local identity_field=$1
  local output=$2
  shift 2
  local input temporary
  [[ $# -gt 0 ]] || die "no JSONL input for ${output}"
  for input in "$@"; do
    require_file "JSONL input" "${input}"
  done
  temporary=$(mktemp "${output}.tmp.XXXXXX")
  # Rows pass through verbatim and only their identity is read, so a row
  # carrying a symbolic expression tree deeper than jq's tree parser accepts
  # still survives.  Rows are addressed by line so none is ever held whole.
  #
  # Identity taskId keeps the original comparison exactly: its normalization
  # was the identity function, so equal bytes mean equal rows.  Only summaries
  # need the taskId-insensitive comparison, and those rows are small.
  local key total number seen_keys=() seen_files=() seen_lines=() index found
  for input in "$@"; do
    total=$(wc -l <"${input}")
    for ((number = 1; number <= total; number++)); do
      if [[ "${identity_field}" == "taskId" ]] \
        && [[ "$(sed -n "${number}p" "${input}" | jsonl_stream_field event)" \
          == "CONCOLIC_REGION_SKIPPED" ]]; then
        # SKIPPED rows are replay diagnostics, not the task result retained in
        # path state.  The admission check already required one real result.
        continue
      fi
      key=$(sed -n "${number}p" "${input}" \
        | jsonl_stream_field "${identity_field}")
      [[ -n "${key}" ]] \
        || die "missing JSONL identity ${identity_field} in ${input}"
      found=""
      for index in "${!seen_keys[@]}"; do
        if [[ "${seen_keys[$index]}" == "${key}" ]]; then
          found=$index
          break
        fi
      done
      if [[ -n "${found}" ]]; then
        # Only a repeated identity is compared, and only when it repeats.
        jsonl_rows_agree "${seen_files[$found]}" "${seen_lines[$found]}" \
          "${input}" "${number}" "${identity_field}" \
          || die "conflicting duplicate ${identity_field}:${key}"
        continue
      fi
      seen_keys+=("${key}")
      seen_files+=("${input}")
      seen_lines+=("${number}")
      sed -n "${number}p" "${input}" >>"${temporary}"
    done
  done
  [[ -s "${temporary}" ]] || die "combined JSONL is empty: ${output}"
  mv -f "${temporary}" "${output}"
}

run_concolic_import() {
  local plan=$1
  local results=$2
  local summaries=$3
  local output_dir=$4
  CAUSYNTH_RAW_RESULTS="${results}" \
    CAUSYNTH_IMPORT_TASK_PLAN="${plan}" \
    CAUSYNTH_IMPORTED_SUMMARIES="${summaries}" \
    CAUSYNTH_IMPORT_DIAGNOSTICS="${output_dir}/import-diagnostics.jsonl" \
    do_engine_config import
}

prepare_target_branch_query() {
  local campaign=$1
  local region=$2
  local instance=$3
  local goal=$4
  local query_dir="${campaign}/target-query"
  local target_edge_ids
  target_edge_ids=$(jq -er '
    [.edgeBindings[]?.edgeId
      | select(type == "string" and length > 0)]
    | unique
    | if length > 0 then join(",")
      else error("selected target task has no exact edge binding") end
  ' "${campaign}/execution_task_plan.jsonl")
  mkdir -p "${query_dir}"
  CAUSYNTH_SCHEDULE_OUTPUT_DIR="${query_dir}" \
    CAUSYNTH_SCHEDULE_SUMMARIES="${campaign}/seed-summaries.jsonl" \
    do_engine_config schedule --region-id "${region}" \
      --occurrence-id "${instance}" --goal-id "${goal}" \
      --target-edge-ids "${target_edge_ids}"
  require_nonempty_file "target branch query" \
    "${query_dir}/branch_queries.jsonl"
}

run_path_query() {
  local query_key=$1
  local worklist=$2
  local execution_tasks=$3
  local classes=$4
  local task_dir=$5
  local z3=$6
  local solver_timeout=$7
  local solver_status solver_outcome replay_task
  local raw="${task_dir}/raw-results.jsonl"
  local imported="${task_dir}/summaries.jsonl"

  mkdir -p "${task_dir}"
  set +e
  run_graphchecker_main \
    edu.uva.liftlab.graphchecker.concolic.ConcolicPathFlipSolver \
    --worklist "${worklist}" --task-plan "${execution_tasks}" \
    --query-key "${query_key}" --output-dir "${task_dir}" \
    --z3 "${z3}" --solver-timeout-ms "${solver_timeout}"
  solver_status=$?
  set -e
  [[ "${solver_status}" -eq 0 ]] \
    || die "path solver failed for ${query_key}"
  solver_outcome=$(jq -er '.status' \
    "${task_dir}/path_flip_solver_result.json")
  if [[ "${solver_outcome}" == "UNSAT" ]]; then
    jq -c '{schemaVersion: 1, kind: "PATH_EXPLORATION_RECORD",
      queryKey, regionId, sourcePathKey, sourceSummaryId, status,
      solverInputHash}' "${task_dir}/path_flip_solver_result.json" \
      >"${task_dir}/record.jsonl"
    return
  fi
  # An UNSUPPORTED or MATERIALIZATION_GAP flip is an explored-and-abandoned
  # exploration proposal, not a semantic authority: the fatal branch
  # condition itself remains symbolic and is decided at the reach stage.
  # One flip the replay cannot express or cannot materialize decides
  # nothing, so record the named gap and let the planner close over it while
  # the pipeline proceeds to candidates/compose.  The flip's own
  # materialization test is untouched.
  if [[ "${solver_outcome}" == "UNSUPPORTED" \
      || "${solver_outcome}" == "MATERIALIZATION_GAP" ]]; then
    jq -c '{schemaVersion: 1, kind: "PATH_EXPLORATION_RECORD",
      queryKey, regionId, sourcePathKey, sourceSummaryId, status,
      reason, unsupported, unresolvedContainerBoundaries,
      unresolvedReplayControlSymbols}
      | with_entries(select(.value != null))' \
      "${task_dir}/path_flip_solver_result.json" \
      >"${task_dir}/record.jsonl"
    return
  fi
  [[ "${solver_outcome}" == "SAT_MODEL_READY" ]] \
    || die "path solver emitted unsupported status ${solver_outcome}"
  replay_task=$(jq -er -s \
    'if length == 1 then .[0].taskId else error("not singleton") end' \
    "${task_dir}/execution_task_plan.jsonl")
  # A replay that never reaches its selected result leaves nothing to admit.
  # Exploring a flip is allowed to cost more than this machine can pay -- the
  # replay is bounded, its resident cost is not -- so a flip whose replay dies
  # before publishing is explored and abandoned like one whose path missed the
  # relation, not a pipeline failure.  A seed replay keeps dying on this,
  # because a campaign with no result cannot be seeded at all.
  set +e
  ( replay_concolic_plan "${task_dir}/execution_task_plan.jsonl" \
      "${replay_task}" "${classes}" "${raw}" "${task_dir}" \
      "${HDFS11741_PATH_REPLAY_TIMEOUT_S:-180}" )
  local replay_outcome=$?
  set -e
  if [[ "${replay_outcome}" -ne 0 ]]; then
    jq -c -s -n --slurpfile task "${task_dir}/execution_task_plan.jsonl" \
      --arg outcome "${replay_outcome}" '
      {schemaVersion: 1, kind: "PATH_EXPLORATION_RECORD",
       queryKey: $task[0].pathQueryKey, regionId: $task[0].regionId,
       taskId: $task[0].taskId, status: "REPLAY_PRODUCED_NO_RESULT",
       reason: ("replay ended without a selected result (exit "
                + $outcome + ")")}' >"${task_dir}/record.jsonl"
    echo "[hdfs-11741] flip abandoned: replay produced no result (exit ${replay_outcome}): ${task_dir}"
    return
  fi
  run_concolic_import "${task_dir}/execution_task_plan.jsonl" "${raw}" \
    "${imported}" "${task_dir}"
  # A proposed flip whose bounded replay walked a path that never reaches the
  # region's output relation is explored and abandoned, not a pipeline
  # failure.  The importer's admission stays exactly as strict; the flip is
  # named as an exploration gap so the planner closes over it and the round
  # continues.
  #
  # A replay whose every activation only ever lost the single symbolic engine
  # is a different gap: nothing about its path was decided, so it may not be
  # recorded as a path that failed admission.  The reason carries every
  # diagnostic code, not just the admission ones, or a run rejected upstream
  # of admission reports an empty reason and becomes unattributable.
  if [[ ! -s "${imported}" ]]; then
    jq -c -s --slurpfile task "${task_dir}/execution_task_plan.jsonl" '
      (map(.code) | unique) as $codes
      | {schemaVersion: 1, kind: "PATH_EXPLORATION_RECORD",
         queryKey: $task[0].pathQueryKey, regionId: $task[0].regionId,
         taskId: $task[0].taskId,
         status: (if ($codes | length) > 0
                    and ($codes - ["REGION_ENGINE_UNAVAILABLE"]
                         | length) == 0
                  then "REPLAY_ENGINE_UNAVAILABLE"
                  else "REPLAY_NOT_ADMITTED" end),
         reason: ([.[] | .code + ": " + (.detail // "")] | join(";"))}
    ' "${task_dir}/import-diagnostics.jsonl" >"${task_dir}/record.jsonl"
    echo "[hdfs-11741] flip abandoned: $(jq -r '.status' \
      "${task_dir}/record.jsonl"): ${task_dir}"
    return
  fi
  # The imported summary carries the replayed region's projected relation and
  # can be nested past jq's tree-parser depth limit, so its admission is read
  # as a stream; the record itself is built from the task plan, which is not.
  [[ "$(wc -l <"${imported}")" -eq 1 ]] \
    && [[ "$(jsonl_stream_field relationallyComplete <"${imported}")" \
      == true ]] \
    && [[ "$(jsonl_stream_field taskId <"${imported}")" \
      == "${replay_task}" ]] \
    || die "path replay admission failed: ${task_dir}"
  jq -e -c -s '
    if length == 1
    then {schemaVersion: 1, kind: "PATH_EXPLORATION_RECORD",
      queryKey: .[0].pathQueryKey, regionId: .[0].regionId,
      taskId: .[0].taskId,
      occurrenceId: .[0].occurrenceId,
      goalId: .[0].goalId,
      status: (if .[0].goalKind == "OUTPUT_RELATION_CLOSURE"
        then "VALIDATED_FRESH_OUTPUT_PATH_FLIP_REPLAY"
        else "VALIDATED_FRESH_TARGET_PATH_FLIP_REPLAY" end)}
    else error("path replay task plan is not singleton") end
  ' "${task_dir}/execution_task_plan.jsonl" >"${task_dir}/record.jsonl" \
    || die "path replay admission failed: ${task_dir}"
}

run_path_frontier() {
  local worklist=$1
  local execution_tasks=$2
  local classes=$3
  local planner=$4
  local z3=$5
  local solver_timeout=$6
  local query task_dir pid status next=0
  local -a queries=() workers=() batch=()

  require_positive_integer HDFS11741_PATH_JOBS "${path_parallelism}"
  announce_parallelism "path flips" HDFS11741_PATH_JOBS \
    "${path_parallelism}"
  while IFS= read -r query; do
    [[ -n "${query}" ]] && queries+=("${query}")
  done < <(jq -er -s '
    sort_by(.queryKey)
    | if length == 0 then error("empty path frontier")
      elif ([group_by(.queryKey)[] | select(length != 1)] | length) > 0
        then error("duplicate path query key")
      else .[].queryKey end
  ' "${worklist}")
  (( ${#queries[@]} > 0 )) || die "path planner emitted an empty frontier"

  echo "[hdfs-11741] executing ${#queries[@]} path flip(s), ${path_parallelism} in parallel"
  while (( next < ${#queries[@]} )); do
    batch=()
    while (( next < ${#queries[@]} \
        && ${#batch[@]} < path_parallelism )); do
      query=${queries[$next]}
      task_dir="${planner}/task-${query}"
      (
        trap worker_signal_cleanup TERM INT
        set -euo pipefail
        run_path_query "${query}" "${worklist}" "${execution_tasks}" \
          "${classes}" "${task_dir}" "${z3}" "${solver_timeout}"
      ) &
      pid=$!
      workers+=("${pid}")
      batch+=("${pid}")
      next=$((next + 1))
    done
    for pid in "${batch[@]}"; do
      set +e
      wait "${pid}"
      status=$?
      set -e
      if [[ "${status}" -ne 0 ]]; then
        terminate_workers "${workers[@]}"
        die "parallel path frontier failed (exit ${status}): ${planner}"
      fi
    done
  done
}

prepare_observed_seed_relation() {
  local campaign=$1
  local region=$2
  local goal=$3
  local published="${campaign}/observed_summary.jsonl"
  local planner="${campaign}/observed-seed"
  if [[ -s "${campaign}/path_closure.json" \
      && -s "${campaign}/relation_summary.jsonl" ]]; then
    cp -f "${campaign}/relation_summary.jsonl" "${published}"
    return
  fi
  mkdir -p "${planner}"
  run_graphchecker_main \
    edu.uva.liftlab.graphchecker.concolic.ConcolicPathFlipPlanner \
    --summaries "${campaign}/seed-summaries.jsonl" \
    --task-plan "${campaign}/execution_task_plan.jsonl" \
    --output-dir "${planner}" --region-id "${region}" --goal-id "${goal}"
  if jq -e '.state == "CLOSED"' \
      "${planner}/region_path_manifest.json" >/dev/null; then
    local relation_source
    if jq -e '.coverageState == "CLOSED"' \
        "${planner}/region_path_manifest.json" >/dev/null; then
      relation_source="${planner}/merged_region_summaries.jsonl"
    else
      relation_source="${planner}/observed_region_summaries.jsonl"
    fi
    require_nonempty_file "producer seed relation" "${relation_source}"
    cp -f "${relation_source}" "${published}"
    return
  fi
  jq -e '.state == "PENDING"' \
    "${planner}/region_path_manifest.json" >/dev/null \
    || die "producer seed path planner emitted no executable state"
  require_nonempty_file "observed producer seed relation" \
    "${planner}/observed_region_summaries.jsonl"
  cp -f "${planner}/observed_region_summaries.jsonl" "${published}"
}

reach_satisfies_required_true_ports() {
  local report=$1
  local required_json
  (( ${#partial_probe_required_true_ports[@]} > 0 )) || return 0
  required_json=$(printf '%s\n' \
    "${partial_probe_required_true_ports[@]}" \
    | jq -Rsc 'split("\n")[:-1]')
  jq -e --argjson required "${required_json}" '
    . as $report
    | ($report.roots.booleanInputs // []) as $roots
    | def rootIndex($port):
        ([range(0; $roots | length) as $index
          | select($roots[$index].portId == $port)
          | $index]
         | if length == 1 then .[0] else -1 end);
      ($required | map(rootIndex(.))) as $indices
    | (all($indices[]; . >= 0)
       and any($report.valuations[]?;
         . as $valuation
         | ($valuation.status == "sat"
            and all($indices[];
              . as $index | $valuation.values[$index] == true))))
  ' "${report}" >/dev/null
}

probe_observed_candidate() {
  [[ "${partial_probe_enabled:-false}" == true ]] || return 1
  [[ "${CAUSYNTH_REQUIRE_COMPLETE_CANDIDATE:-false}" != true ]] \
    || return 1
  local fingerprint attempt compose_summaries reachability source snapshot
  local degeneracy
  local index=0
  local -a snapshot_summaries=()
  fingerprint=$(sha256sum "${partial_probe_summary_files[@]}" \
    | sha256sum | cut -d' ' -f1)
  [[ "${fingerprint}" != "${partial_probe_last_hash}" ]] || return 1
  partial_probe_last_hash=${fingerprint}
  partial_probe_attempt=$((partial_probe_attempt + 1))
  attempt="${partial_probe_output}/observed-attempt-$(printf '%04d' \
    "${partial_probe_attempt}")"
  mkdir -p "${attempt}"
  # Region workers publish by rename.  Snapshot every input before composing
  # so one solver attempt always sees one immutable cross-region cut.
  for source in "${partial_probe_summary_files[@]}"; do
    snapshot="${attempt}/producer-$(printf '%04d' "${index}").jsonl"
    cp "${source}" "${snapshot}"
    snapshot_summaries+=("${snapshot}")
    index=$((index + 1))
  done
  compose_summaries=$(IFS=:; printf '%s' \
    "${snapshot_summaries[*]}")
  CAUSYNTH_FATAL_QUERIES="${partial_probe_target_reach}" \
    CAUSYNTH_COMPOSE_SUMMARIES="${compose_summaries}" \
    CAUSYNTH_COMPOSED_SMT="${attempt}/candidate.smt2" \
    CAUSYNTH_COMPOSITION_MANIFEST="${attempt}/composition.json" \
    CAUSYNTH_FATAL_REGION="${partial_probe_target_region}" \
    CAUSYNTH_FATAL_OCCURRENCE_ID="${partial_probe_target_instance}" \
    do_engine_config compose \
      --composition-mode EXISTENTIAL_OBSERVED_PATHS
  # Exploration can finish while this probe is still armed: once every
  # producer campaign is closed the same summaries compose into a complete
  # path set, which is no longer the underapproximation this probe is
  # allowed to publish.  That is the probe's job ending, not a failure -
  # retire it and let the complete closure below compose and report.
  if jq -e '.pathSetComplete == true' \
      "${attempt}/composition.json" >/dev/null; then
    echo "[hdfs-11741] observed-path probe retired: producer paths are complete"
    partial_probe_enabled=false
    return 1
  fi
  jq -e '.trustState == "OBSERVED_PATH_UNDERAPPROX"
    and .pathSetComplete == false' \
    "${attempt}/composition.json" >/dev/null \
    || die "observed-path composition lost its underapproximation scope"
  # This probe is opportunistic: it asks whether the paths imported so far
  # already prove the target. A cut that still carries composition gaps is
  # not an answer, exactly like a cut the solver cannot satisfy yet, so it
  # continues exploration instead of ending the campaign. The complete
  # closure below composes again and reports its own gaps.
  if ! jq -e '.state == "CANDIDATE_READY"' \
      "${attempt}/composition.json" >/dev/null; then
    echo "[hdfs-11741] observed-path composition still has gaps; continuing exploration"
    return 1
  fi
  CAUSYNTH_COMPOSED_SMT="${attempt}/candidate.smt2" \
    CAUSYNTH_COMPOSITION_MANIFEST="${attempt}/composition.json" \
    CAUSYNTH_REACH_REPORT="${attempt}/z3-result.json" \
    do_engine_config reach
  reachability=$(jq -er '.reachCondition.reachability' \
    "${attempt}/z3-result.json")
  if [[ "${reachability}" != "REACHABLE" ]] \
      || ! jq -e 'any(.valuations[]?; .status == "sat")' \
        "${attempt}/z3-result.json" >/dev/null; then
    echo "[hdfs-11741] observed paths are not SAT yet; continuing exploration"
    return 1
  fi
  if ! reach_satisfies_required_true_ports \
      "${attempt}/z3-result.json"; then
    echo "[hdfs-11741] observed paths do not yet admit every required explicit fault as true; continuing exploration"
    return 1
  fi
  # A reach condition that admits the whole root space says only that the
  # target's method runs -- which the recording already showed.  Ending the
  # campaign on it would trade the exploration that could still constrain the
  # target for an answer that constrains nothing, so it is not an answer.
  # This probe is opportunistic and continuing costs only time, so an
  # undecided verdict keeps exploring too; it is still named, never silent.
  degeneracy=$(jq -er '.reachCondition.degeneracyCheck
    // "UNDECIDED_VERDICT_NOT_PUBLISHED"' "${attempt}/z3-result.json")
  if [[ "${degeneracy}" != CONSTRAINED_* ]]; then
    echo "[hdfs-11741] observed-path reach condition not proven to constrain (${degeneracy}); continuing exploration"
    return 1
  fi
  run_graphchecker_main \
    edu.uva.liftlab.graphchecker.concolic.CausalGraphWriter \
    "${region_plan}" \
    "${work_root}/runtime/causal_source_events.jsonl" \
    "${workflow_index}" \
    "${attempt}/composition.json" \
    "${attempt}/z3-result.json" \
    "${attempt}" "${snapshot_summaries[@]}"
  cp -f "${attempt}/candidate.smt2" \
    "${partial_probe_output}/candidate.smt2"
  cp -f "${attempt}/composition.json" \
    "${partial_probe_output}/composition.json"
  cp -f "${attempt}/z3-result.json" \
    "${partial_probe_output}/z3-result.json"
  for artifact in causal_skeleton.json causal_witness.json \
      causal_witness.dot; do
    require_nonempty_file "observed-path ${artifact}" \
      "${attempt}/${artifact}"
    cp -f "${attempt}/${artifact}" \
      "${partial_probe_output}/${artifact}"
  done
  jq -n --arg campaign "${partial_probe_target_campaign}" \
    --arg region "${partial_probe_target_region}" \
    --arg instance "${partial_probe_target_instance}" \
    --arg goal "${partial_probe_target_goal}" \
    --arg degeneracy "${degeneracy}" \
    --arg smt "${partial_probe_output}/candidate.smt2" \
    --arg z3 "${partial_probe_output}/z3-result.json" \
    --arg graph "${partial_probe_output}/causal_skeleton.json" \
    --arg witness "${partial_probe_output}/causal_witness.json" \
    --arg dot "${partial_probe_output}/causal_witness.dot" \
    '{schemaVersion: 1, kind: "HDFS11741_BOUNDED_CANDIDATE",
      target: {campaign: $campaign, regionId: $region,
        occurrenceId: $instance, goalId: $goal},
      reachability: "REACHABLE", degeneracyCheck: $degeneracy,
      pathSetComplete: false,
      proofScope: "OBSERVED_IMPORTED_VM_PATH_UNDERAPPROX_V1",
      artifacts: {smt: $smt, z3Result: $z3,
        causalSkeleton: $graph, causalWitness: $witness,
        causalWitnessDot: $dot}}' \
    >"${partial_probe_output}/result.json"
  cp -f "${partial_probe_output}/result.json" \
    "${candidate_root}/sat-result.json"
  partial_probe_sat=true
  echo "[hdfs-11741] SAT from imported VM paths: ${partial_probe_output}/candidate.smt2"
  return 0
}

close_region_paths() {
  local label=$1
  local region=$2
  local goal=$3
  local campaign=$4
  local publish_progress=${5:-true}
  local classes="${campaign}/classes"
  local state="${campaign}/path-state"
  local summaries="${state}/summaries.jsonl"
  local tasks="${state}/tasks.jsonl"
  local records="${state}/records.jsonl"
  local iteration=1 replay_count=0 planner worklist query task_dir outcome
  local z3 solver_timeout goal_kind
  local -a queries=() record_inputs=() summary_inputs=()
  local -a task_inputs=()

  goal_kind=$(jq -er --arg goal "${goal}" \
    'select(.goalId == $goal) | .goalKind' \
    "${campaign}/execution_task_plan.jsonl")
  if [[ -s "${campaign}/path_closure.json" ]] \
      && jq -e '.state == "CLOSED"' \
        "${campaign}/path_closure.json" >/dev/null \
      && { [[ "${goal_kind}" == "TARGET_REACH_CLOSURE" ]] \
        || [[ -s "${campaign}/relation_summary.jsonl" ]]; }; then
    echo "[hdfs-11741] reuse closed ${label} path campaign"
    return
  fi
  require_nonempty_file "${label} seed summary" \
    "${campaign}/seed-summaries.jsonl"
  require_nonempty_file "${label} seed result" \
    "${campaign}/seed-results.jsonl"
  require_nonempty_file "${label} seed task" \
    "${campaign}/execution_task_plan.jsonl"
  require_directory "${label} concolic classes" "${classes}"
  mkdir -p "${state}"
  combine_jsonl_unique summaryId "${summaries}" \
    "${campaign}/seed-summaries.jsonl"
  combine_jsonl_unique taskId "${tasks}" \
    "${campaign}/execution_task_plan.jsonl"
  : >"${records}"
  z3=$(configured_value z3_bin)
  solver_timeout=$(configured_value solver_timeout_ms)

  while true; do
    planner="${campaign}/path-iteration-$(printf '%04d' "${iteration}")"
    mkdir -p "${planner}"
    set +e
    run_graphchecker_main \
      edu.uva.liftlab.graphchecker.concolic.ConcolicPathFlipPlanner \
      --summaries "${summaries}" --task-plan "${tasks}" \
      --records "${records}" --output-dir "${planner}" \
      --region-id "${region}" --goal-id "${goal}"
    outcome=$?
    set -e
    [[ "${outcome}" -eq 0 ]] \
      || die "${label} path planner did not close: ${planner}"
    if jq -e '.state == "CLOSED"' \
        "${planner}/region_path_manifest.json" >/dev/null; then
      cp -f "${planner}/region_path_manifest.json" \
        "${campaign}/path_closure.json"
      if [[ "${goal_kind}" != "TARGET_REACH_CLOSURE" ]]; then
        local coverage relation_source
        coverage=$(jq -r '.coverageState // "CLOSED"' \
          "${planner}/region_path_manifest.json")
        if [[ "${coverage}" == "CLOSED" ]]; then
          relation_source="${planner}/merged_region_summaries.jsonl"
        else
          relation_source="${planner}/observed_region_summaries.jsonl"
        fi
        require_nonempty_file "${coverage} ${label} relation" \
          "${relation_source}"
        publish_file_atomically "${relation_source}" \
          "${campaign}/relation_summary.jsonl"
        publish_file_atomically "${relation_source}" \
          "${campaign}/observed_summary.jsonl"
      fi
      echo "[hdfs-11741] ${label} coverage $(jq -r \
        '.coverageState // "CLOSED"' "${campaign}/path_closure.json") after ${replay_count} replay(s)"
      return
    fi
    jq -e '.state == "PENDING"' \
      "${planner}/region_path_manifest.json" >/dev/null \
      || die "${label} path planner emitted no executable state"
    if [[ -s "${planner}/observed_region_summaries.jsonl" ]]; then
      if [[ "${publish_progress}" == true ]]; then
        publish_file_atomically \
          "${planner}/observed_region_summaries.jsonl" \
          "${campaign}/observed_summary.jsonl"
      fi
      if [[ "${publish_progress}" == true ]] \
          && probe_observed_candidate; then
        return
      fi
    fi
    worklist="${planner}/region_path_worklist.jsonl"
    run_path_frontier "${worklist}" "${tasks}" "${classes}" \
      "${planner}" "${z3}" "${solver_timeout}"

    queries=()
    while IFS= read -r query; do
      [[ -n "${query}" ]] && queries+=("${query}")
    done < <(jq -er -s 'sort_by(.queryKey) | .[].queryKey' "${worklist}")
    replay_count=$((replay_count + ${#queries[@]}))
    record_inputs=("${records}")
    summary_inputs=("${summaries}")
    task_inputs=("${tasks}")
    for query in "${queries[@]}"; do
      task_dir="${planner}/task-${query}"
      require_nonempty_file "path exploration record" \
        "${task_dir}/record.jsonl"
      record_inputs+=("${task_dir}/record.jsonl")
      if [[ -s "${task_dir}/summaries.jsonl" ]]; then
        summary_inputs+=("${task_dir}/summaries.jsonl")
        task_inputs+=("${task_dir}/execution_task_plan.jsonl")
      fi
    done
    combine_jsonl_unique queryKey "${state}/next-records.jsonl" \
      "${record_inputs[@]}"
    mv -f "${state}/next-records.jsonl" "${records}"
    if (( ${#summary_inputs[@]} > 1 )); then
      combine_jsonl_unique summaryId "${state}/next-summaries.jsonl" \
        "${summary_inputs[@]}"
      combine_jsonl_unique taskId "${state}/next-tasks.jsonl" \
        "${task_inputs[@]}"
      mv -f "${state}/next-summaries.jsonl" "${summaries}"
      mv -f "${state}/next-tasks.jsonl" "${tasks}"
    fi
    iteration=$((iteration + 1))
  done
}

build_target_reach_query() {
  local campaign=$1
  local selected_target_instance=$2
  local exception_type target_region target_occurrence
  target_region=$(jq -er '.regionId' \
    "${campaign}/execution_task_plan.jsonl")
  target_occurrence=$(jq -er '.occurrenceId' \
    "${campaign}/execution_task_plan.jsonl")
  if [[ -s "${campaign}/reach_query.jsonl" ]] \
      && jq -e --arg region "${target_region}" \
        --arg instance "${selected_target_instance}" \
        --arg occurrence "${target_occurrence}" \
        '.kind == "TARGET_REACH_PATH_SET_QUERY"
          and .constraintAuthority
            == "RECORDED_TARGET_PREFIX_V1"
          and .regionId == $region and .occurrenceId == $instance
          and .occurrenceId == $occurrence
          and (.paths | length) > 0' \
        "${campaign}/reach_query.jsonl" >/dev/null; then
    echo "[hdfs-11741] reuse closed target reach query"
    return
  fi
  exception_type=$(jq -er '.exception | select(type == "string" and length > 0)' \
    "${work_root}/analysis/target_resolved.json")
  run_graphchecker_main \
    edu.uva.liftlab.graphchecker.concolic.TargetReachPathQueryBuilder \
    --summaries "${campaign}/path-state/summaries.jsonl" \
    --path-manifest "${campaign}/path_closure.json" \
    --seed-query "${campaign}/target-query/branch_queries.jsonl" \
    --target-instance "${selected_target_instance}" \
    --exception-type "${exception_type}" \
    --output "${campaign}/reach_query.jsonl"
  require_nonempty_file "closed target reach query" \
    "${campaign}/reach_query.jsonl"
}

run_producer_closures_parallel() {
  local spec label region goal campaign pid status progress next=0 active=0
  local -a supplied=("$@") specs=() workers=()
  declare -A seen=() active_pid=()

  require_positive_integer HDFS11741_REGION_JOBS "${region_parallelism}"
  announce_parallelism "producer path closures" HDFS11741_REGION_JOBS \
    "${region_parallelism}"
  for spec in "${supplied[@]}"; do
    IFS=$'\t' read -r label region goal campaign <<< "${spec}"
    [[ -n "${label}" && -n "${region}" && -n "${goal}" \
        && -n "${campaign}" ]] \
      || die "invalid producer closure specification: ${spec}"
    if [[ -z "${seen[${campaign}]+x}" ]]; then
      seen[${campaign}]=1
      specs+=("${label}"$'\t'"${region}"$'\t'"${goal}"$'\t'"${campaign}")
    fi
  done
  (( ${#specs[@]} > 0 )) || die "no producer closure to execute"

  echo "[hdfs-11741] closing ${#specs[@]} producer campaign(s), ${region_parallelism} in parallel"
  while (( next < ${#specs[@]} || active > 0 )); do
    while (( next < ${#specs[@]} && active < region_parallelism )); do
      IFS=$'\t' read -r label region goal campaign <<< "${specs[$next]}"
      (
        trap worker_signal_cleanup TERM INT
        set -euo pipefail
        # Only the coordinator composes partial candidates.  Workers publish
        # complete per-wave summaries atomically in their own campaign dirs.
        partial_probe_enabled=false
        close_region_paths "${label}" "${region}" "${goal}" \
          "${campaign}" true
      ) &
      pid=$!
      workers+=("${pid}")
      active_pid[${pid}]=1
      next=$((next + 1))
      active=$((active + 1))
    done

    progress=false
    for pid in "${!active_pid[@]}"; do
      if kill -0 "${pid}" >/dev/null 2>&1; then
        continue
      fi
      set +e
      wait "${pid}"
      status=$?
      set -e
      unset 'active_pid['"${pid}"']'
      active=$((active - 1))
      progress=true
      if [[ "${status}" -ne 0 ]]; then
        terminate_workers "${workers[@]}"
        die "parallel producer closure failed (exit ${status})"
      fi
    done

    if probe_observed_candidate; then
      terminate_workers "${workers[@]}"
      return 0
    fi
    if [[ "${progress}" != true && "${active}" -gt 0 ]]; then
      sleep 1
    fi
  done
}

run_candidate_for_target() {
  local binding=$1
  local target_campaign_id target_region target_instance target_goal
  local schedule_plan="${work_root}/schedule/execution_task_plan.jsonl"
  local workflow_index="${work_root}/schedule/runtime_workflow_schedule_index.json"
  local target_task target_campaign output producer_id
  local producer_region producer_instance producer_goal producer_task
  local producer_campaign producer_summary compose_summaries reachability
  local index degeneracy producer_row coverage any_partial=false
  local -a producer_ids=() producer_regions=()
  local -a producer_goals=() producer_tasks=() producer_campaigns=()
  local -a relation_inputs=() seed_specs=() producer_closure_specs=()
  local -a usable_producer_indices=()
  local -a compose_args=()
  declare -A probe_seen=() relation_seen=()

  IFS=$'\t' read -r target_campaign_id target_region target_instance \
    target_goal <<< "${binding}"
  [[ -n "${target_campaign_id}" && -n "${target_region}" \
      && -n "${target_instance}" && -n "${target_goal}" ]] \
    || die "incomplete target binding: ${binding}"
  require_nonempty_file "target-first workflow index" "${workflow_index}"
  target_task=$(jq -er --arg campaign "${target_campaign_id}" \
      --arg region "${target_region}" --arg instance "${target_instance}" \
      --arg goal "${target_goal}" '
        select(.target.campaignId == $campaign and
          .target.regionId == $region and
          .target.occurrenceId == $instance and
          .target.goalId == $goal) | .target.taskId
    ' "${workflow_index}") \
    || die "workflow index does not match selected target: ${workflow_index}"
  while IFS= read -r producer_row; do
    [[ -n "${producer_row}" ]] || continue
    IFS=$'\t' read -r producer_id producer_region producer_instance \
      producer_goal producer_task <<< "${producer_row}"
    [[ -n "${producer_id}" && -n "${producer_region}" \
        && -n "${producer_instance}" && -n "${producer_goal}" \
        && -n "${producer_task}" ]] \
      || die "incomplete producer row in workflow index: ${producer_row}"
    producer_campaign=$(seed_campaign_directory OUTPUT_RELATION_CLOSURE \
      "${producer_task}")
    producer_ids+=("${producer_id}")
    producer_regions+=("${producer_region}")
    producer_goals+=("${producer_goal}")
    producer_tasks+=("${producer_task}")
    producer_campaigns+=("${producer_campaign}")
  done < <(jq -r '.producers[] |
    [.campaignId,.regionId,.occurrenceId,.goalId,.taskId] | @tsv' \
    "${workflow_index}")
  (( ${#producer_ids[@]} > 0 )) \
    || die "target ${target_campaign_id} has no runtime-confirmed producer"

  prune_stale_seed_campaigns "${schedule_plan}"

  seed_specs+=("TARGET_REACH_CLOSURE"$'\t'"${target_task}")
  for index in "${!producer_tasks[@]}"; do
    seed_specs+=("OUTPUT_RELATION_CLOSURE"$'\t'"${producer_tasks[$index]}")
  done
  run_seed_tasks_parallel "${schedule_plan}" "${seed_specs[@]}"

  target_campaign=$(seed_campaign_directory TARGET_REACH_CLOSURE "${target_task}")
  require_nonempty_file "target seed summary" \
    "${target_campaign}/seed-summaries.jsonl"
  for index in "${!producer_ids[@]}"; do
    producer_campaign=${producer_campaigns[$index]}
    if [[ -s "${producer_campaign}/seed-summaries.jsonl" ]]; then
      usable_producer_indices+=("${index}")
    else
      any_partial=true
      echo "[hdfs-11741] producer coverage gap: ${producer_ids[$index]}" >&2
    fi
  done
  (( ${#usable_producer_indices[@]} > 0 )) \
    || die "target ${target_campaign_id} has no observed producer relation"
  prepare_target_branch_query "${target_campaign}" "${target_region}" \
    "${target_instance}" "${target_goal}"
  close_region_paths "target ${target_campaign_id}" "${target_region}" \
    "${target_goal}" "${target_campaign}"
  build_target_reach_query "${target_campaign}" "${target_instance}"

  output="${candidate_root}/${target_campaign_id}"
  mkdir -p "${output}"
  partial_probe_enabled=true
  partial_probe_sat=false
  partial_probe_attempt=0
  partial_probe_last_hash=""
  partial_probe_target_campaign=${target_campaign_id}
  partial_probe_target_region=${target_region}
  partial_probe_target_instance=${target_instance}
  partial_probe_target_goal=${target_goal}
  partial_probe_target_reach="${target_campaign}/reach_query.jsonl"
  partial_probe_output=${output}
  partial_probe_summary_files=()
  partial_probe_required_true_ports=()
  if [[ "${CAUSYNTH_REQUIRE_EXPLICIT_FAULT_TRUE:-false}" == true ]]; then
    while IFS= read -r producer_id; do
      [[ -n "${producer_id}" ]] \
        && partial_probe_required_true_ports+=("${producer_id}")
    done < <(jq -r '
      .inputActions[]?
      | select(.authority == "EXACT_RUNTIME_EXPLICIT_FAULT_RETURN_V1")
      | .portId
    ' "${schedule_plan}" | sort -u)
    (( ${#partial_probe_required_true_ports[@]} > 0 )) \
      || die "explicit-fault experiment has no scheduled fault input"
  fi
  for index in "${usable_producer_indices[@]}"; do
    producer_campaign=${producer_campaigns[$index]}
    if [[ -z "${probe_seen[${producer_campaign}]+x}" ]]; then
      probe_seen[${producer_campaign}]=1
      prepare_observed_seed_relation "${producer_campaign}" \
        "${producer_regions[$index]}" "${producer_goals[$index]}"
      partial_probe_summary_files+=(
        "${producer_campaign}/observed_summary.jsonl")
      producer_closure_specs+=(
        "producer ${producer_ids[$index]}"$'\t'"${producer_regions[$index]}"$'\t'"${producer_goals[$index]}"$'\t'"${producer_campaign}")
    fi
  done
  probe_observed_candidate || true
  if [[ "${partial_probe_sat}" == true ]]; then
    return 0
  fi

  run_producer_closures_parallel "${producer_closure_specs[@]}"
  if [[ "${partial_probe_sat}" == true ]]; then
    return 0
  fi
  for index in "${usable_producer_indices[@]}"; do
    producer_summary="${producer_campaigns[$index]}/relation_summary.jsonl"
    require_nonempty_file "producer relation summary" "${producer_summary}"
    coverage=$(jq -r '.coverageState // "CLOSED"' \
      "${producer_campaigns[$index]}/path_closure.json")
    if [[ "${coverage}" != "CLOSED" ]]; then
      any_partial=true
    fi
    if [[ -z "${relation_seen[${producer_summary}]+x}" ]]; then
      relation_seen[${producer_summary}]=1
      relation_inputs+=("${producer_summary}")
    fi
  done
  partial_probe_enabled=false
  compose_summaries=$(IFS=:; printf '%s' "${relation_inputs[*]}")
  if [[ "${any_partial}" == true ]]; then
    compose_args+=(--composition-mode EXISTENTIAL_OBSERVED_PATHS)
  fi
  CAUSYNTH_FATAL_QUERIES="${target_campaign}/reach_query.jsonl" \
    CAUSYNTH_COMPOSE_SUMMARIES="${compose_summaries}" \
    CAUSYNTH_COMPOSED_SMT="${output}/candidate.smt2" \
    CAUSYNTH_COMPOSITION_MANIFEST="${output}/composition.json" \
    CAUSYNTH_FATAL_REGION="${target_region}" \
    CAUSYNTH_FATAL_OCCURRENCE_ID="${target_instance}" \
    do_engine_config compose "${compose_args[@]}"
  require_nonempty_file "composed candidate SMT" "${output}/candidate.smt2"
  if [[ "${CAUSYNTH_REQUIRE_COMPLETE_CANDIDATE:-false}" == true ]]; then
    jq -e '.state == "CANDIDATE_READY" and
      .trustState == "CANDIDATE_ONLY" and
      .pathSetComplete == true and
      ((.gaps // []) | length == 0)' \
      "${output}/composition.json" >/dev/null \
      || die "candidate is not a gap-free complete path set: ${output}"
  fi
  CAUSYNTH_COMPOSED_SMT="${output}/candidate.smt2" \
    CAUSYNTH_COMPOSITION_MANIFEST="${output}/composition.json" \
    CAUSYNTH_REACH_REPORT="${output}/z3-result.json" \
    do_engine_config reach
  require_nonempty_file "Z3 candidate result" "${output}/z3-result.json"
  require_file "causal source events" \
    "${work_root}/runtime/causal_source_events.jsonl"
  run_graphchecker_main \
    edu.uva.liftlab.graphchecker.concolic.CausalGraphWriter \
    "${region_plan}" \
    "${work_root}/runtime/causal_source_events.jsonl" \
    "${workflow_index}" \
    "${output}/composition.json" \
    "${output}/z3-result.json" \
    "${output}" "${relation_inputs[@]}"
  require_nonempty_file "causal skeleton" \
    "${output}/causal_skeleton.json"
  require_nonempty_file "causal witness" \
    "${output}/causal_witness.json"
  require_nonempty_file "causal witness DOT" \
    "${output}/causal_witness.dot"
  reach_satisfies_required_true_ports "${output}/z3-result.json" \
    || die "candidate does not admit every required explicit fault as true"
  reachability=$(jq -er '.reachCondition.reachability' \
    "${output}/z3-result.json")
  # The extractor decides degeneracy and publishes its verdict, because the
  # formula alone cannot be read for it: a DNF over zero Boolean roots is the
  # constant "true" by arity, exactly as it is when every enumerated valuation
  # is admitted.  A report too old to carry the verdict is undecided, never a
  # pass - a check that cannot run has to look different from one that ran and
  # found nothing.
  degeneracy=$(jq -er '.reachCondition.degeneracyCheck
    // "UNDECIDED_VERDICT_NOT_PUBLISHED"' "${output}/z3-result.json")
  if [[ "${CAUSYNTH_REQUIRE_COMPLETE_CANDIDATE:-false}" == true \
      && "${degeneracy}" != CONSTRAINED_* ]]; then
    die "candidate reach condition is not proven constrained (${degeneracy}): ${output}"
  fi
  jq -n --arg campaign "${target_campaign_id}" \
    --arg region "${target_region}" --arg instance "${target_instance}" \
    --arg goal "${target_goal}" --arg reachability "${reachability}" \
    --arg degeneracy "${degeneracy}" \
    --arg coverage "$(jq -r '.pathSetComplete
      | if . then "CLOSED" else "PARTIAL" end' \
      "${output}/composition.json")" \
    --arg smt "${output}/candidate.smt2" \
    --arg z3 "${output}/z3-result.json" \
    --arg graph "${output}/causal_skeleton.json" \
    --arg witness "${output}/causal_witness.json" \
    --arg dot "${output}/causal_witness.dot" \
    '{schemaVersion: 1, kind: "HDFS11741_BOUNDED_CANDIDATE",
      target: {campaign: $campaign, regionId: $region,
        occurrenceId: $instance, goalId: $goal},
      reachability: $reachability, coverageState: $coverage,
      degeneracyCheck: $degeneracy,
      artifacts: {smt: $smt, z3Result: $z3,
        causalSkeleton: $graph, causalWitness: $witness,
        causalWitnessDot: $dot}}' >"${output}/result.json"
  if [[ "${reachability}" == "REACHABLE" ]] \
      && jq -e 'any(.valuations[]?; .status == "sat")' \
        "${output}/z3-result.json" >/dev/null; then
    case "${degeneracy}" in
      DEGENERATE_*)
        die "candidate reach condition constrains nothing (${degeneracy}): ${output}" ;;
      CONSTRAINED_*) ;;
      *)
        echo "[hdfs-11741] degeneracy undecided (${degeneracy}); candidate published without that check" ;;
    esac
    cp -f "${output}/result.json" "${candidate_root}/sat-result.json"
    echo "[hdfs-11741] SAT: ${output}/candidate.smt2"
    return 0
  fi
  if [[ "${reachability}" == "UNKNOWN" && "${any_partial}" == true ]]; then
    cp -f "${output}/result.json" \
      "${candidate_root}/inconclusive-result.json"
    echo "[hdfs-11741] partial SMT published with an inconclusive reach report: ${output}/candidate.smt2"
    return 0
  fi
  [[ "${reachability}" == "UNREACHABLE" ]] \
    || die "candidate has no complete SAT/UNSAT result: ${output}"
  echo "[hdfs-11741] UNSAT target candidate: ${target_campaign_id}"
  return 2
}

do_candidates() {
  local binding status workflow_index
  local -a targets=()
  require_nonempty_file "runtime region plan" "${region_plan}"
  require_nonempty_file "scheduled concolic tasks" \
    "${work_root}/schedule/execution_task_plan.jsonl"
  verify_task_artifacts
  initialize_replay_engine_fingerprint
  workflow_index="${work_root}/schedule/runtime_workflow_schedule_index.json"
  binding=$(jq -er '[.target.campaignId, .target.regionId,
    .target.occurrenceId, .target.goalId]
    | if all(.[]; type == "string" and length > 0)
      then join("\t") else error("incomplete target") end' \
    "${workflow_index}")
  targets+=("${binding}")
  mkdir -p "${candidate_root}"
  for binding in "${targets[@]}"; do
    echo "[hdfs-11741] trying target: ${binding}"
    if (set -euo pipefail; run_candidate_for_target "${binding}"); then
      return 0
    else
      status=$?
      if [[ "${status}" -ne 2 ]]; then
        die "target campaign failed (exit ${status}): ${binding}"
      fi
      echo "[hdfs-11741] target candidate is UNSAT; continuing" >&2
    fi
  done
  die "all ${#targets[@]} runtime target instances were attempted without SAT"
}

do_full() {
  do_prepare
  do_engine_config build
  do_tasks
  do_candidates
}

do_traced_workload() {
  [[ -s "${project_classpath}" ]] \
    || die "project classpath not found; run: $0 prepare"
  local instrumented="${work_root}/instrumented-classes"
  local graphchecker_jar="${graphchecker_dir}/target/GraphChecker-1.0-SNAPSHOT.jar"
  local trace_dir="${work_root}/runtime"
  local hadoop_log_dir="${work_root}/hadoop-logs"
  [[ -d "${instrumented}" ]] \
    || die "instrumented classes not found; run tasks first"
  [[ -f "${graphchecker_jar}" ]] \
    || die "GraphChecker jar not found: ${graphchecker_jar}"
  local maven_repository
  maven_repository=$(mvn -q help:evaluate \
    -Dexpression=settings.localRepository -DforceStdout 2>/dev/null)
  local gson_jar="${maven_repository}/com/google/code/gson/gson/2.10.1/gson-2.10.1.jar"
  [[ -f "${gson_jar}" ]] || die "GraphChecker Gson jar not found: ${gson_jar}"
  mkdir -p "${trace_dir}" "${hadoop_log_dir}"
  local classpath
  classpath=$(tr -d '\r\n' < "${project_classpath}")
  java \
    -Dcausynth.trace.output.dir="${trace_dir}" \
    -Dcausynth.trace.test="${test_class}.${test_method}" \
    -Dcausynth.trace.max.events=5000000 \
    -Dcausynth.junit.ignore.timeout=true \
    -Dcausynth.replay.block.key.serial.seed="${HDFS11741_BLOCK_KEY_SERIAL_SEED:-11741}" \
    -Dhdfs11741.test.capacity="${HDFS11741_TEST_CAPACITY:-1000}" \
    -Dhdfs11741.test.timeout.ms="${HDFS11741_TEST_TIMEOUT_MS:-240000}" \
    -Dhdfs11741.heartbeat.recheck.ms="${HDFS11741_HEARTBEAT_RECHECK_MS:-300000}" \
    -Dhdfs11741.key.update.interval.minutes="${HDFS11741_KEY_UPDATE_INTERVAL_MINUTES:-0}" \
    -Dhdfs11741.nn.update.iterations="${hdfs11741_nn_update_iterations}" \
    -Dhdfs11741.datanode.refresh.iterations="${hdfs11741_datanode_refresh_iterations}" \
    -Dhdfs11741.balancer.refresh.iterations="${hdfs11741_balancer_refresh_iterations}" \
    -Dhdfs11741.balancer.dispatcher.threads="${hdfs11741_balancer_dispatcher_threads}" \
    -Dhadoop.log.dir="${hadoop_log_dir}" \
    -cp "${instrumented}:${gson_jar}:${classpath}:${graphchecker_jar}" \
    edu.uva.liftlab.graphchecker.runtime.JUnitMethodRunner \
    "${test_class}" "${test_method}"
}

# A stage prints the one fact -- how wide it actually ran -- that cannot be
# recovered from its artifacts afterwards, and until now it printed it to a
# stdout nobody captured.  Tee both streams into the work root, keeping them
# separate so that a caller parsing stdout still parses only stdout, and
# leaving exit status untouched: the shell is not placed in a pipeline, so
# every die and every propagated status behaves exactly as before.
start_stage_log() {
  local stage=$1
  local stamp
  mkdir -p "${work_root}" 2>/dev/null || return 0
  stamp=$(date +%Y%m%d-%H%M%S)
  stage_log="${work_root}/run-${stage}-${stamp}.log"
  exec > >(tee -a "${stage_log}") 2> >(tee -a "${stage_log}" >&2)
  echo "[hdfs-11741] stage ${stage} logging to ${stage_log}"
}

# Only the long-running stages are logged.  config and validate exist to be
# read by a caller through a command substitution, and must keep a stdout that
# carries nothing but their answer.
case "${1:-prepare}" in
  prepare|tasks|schedule|candidates|full|traced-workload)
    start_stage_log "${1:-prepare}" ;;
esac

case "${1:-prepare}" in
  __patch) [[ $# -eq 1 ]] || die "__patch takes no arguments"; do_patch ;;
  prepare) [[ $# -le 1 ]] || die "prepare takes no arguments"; do_prepare ;;
  config) [[ $# -eq 1 ]] || die "config takes no arguments"; do_engine_config config ;;
  validate) [[ $# -eq 1 ]] || die "validate takes no arguments"; do_engine_config validate ;;
  tasks) [[ $# -eq 1 ]] || die "tasks takes no arguments"; do_tasks ;;
  schedule) [[ $# -eq 1 ]] || die "schedule takes no arguments"; do_schedule ;;
  candidates) [[ $# -eq 1 ]] || die "candidates takes no arguments"; do_candidates ;;
  full) [[ $# -eq 1 ]] || die "full takes no arguments"; do_full ;;
  traced-workload)
    [[ $# -eq 1 ]] || die "traced-workload takes no arguments"
    do_traced_workload
    ;;
  *)
    die "usage: $0 [prepare|tasks|schedule|candidates|full|config|validate|traced-workload]"
    ;;
esac

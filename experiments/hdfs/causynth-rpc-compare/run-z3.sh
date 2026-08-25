#!/usr/bin/env bash

set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd -P)
hadoop_root=${CAUSYNTH_RPC_HADOOP_ROOT:-/opt/hadoop}
run_base=${CAUSYNTH_RPC_RUN_BASE:-/proj/silentfailure-PG0/gc-rpc-compare/runs}
protoc=/opt/causynth-toolchain/protoc-2.5.0/bin/protoc
scenario=${CAUSYNTH_RPC_SCENARIO:-}
run_label=run

if [[ -n "${scenario}" ]]; then
  [[ "${scenario}" =~ ^([1-9]|1[0-9]|20)$ ]] || {
    printf '[causynth-rpc] invalid scenario: %s\n' "${scenario}" >&2
    exit 2
  }
  grep -Eq "CAUSYNTH_RPC_SCENARIO = ${scenario};" \
    "${hadoop_root}/hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/datanode/DataNode.java" || {
      printf '[causynth-rpc] Hadoop source does not select scenario %s: %s\n' \
        "${scenario}" "${hadoop_root}" >&2
      exit 2
    }
  printf -v run_label 'scenario-%02d' "${scenario}"
fi

mkdir -p "${run_base}"
run_dir=$(mktemp -d "${run_base}/${run_label}.XXXXXX")
final_dir=${run_dir}/final

printf '[causynth-rpc] scenario=%s hadoop=%s output=%s\n' \
  "${scenario:-unspecified}" "${hadoop_root}" "${run_dir}"

cd "${repo_root}"

# Rebuild GraphChecker first.  The campaign SETUP stage below then recompiles
# the Hadoop production and test classes from the current /opt/hadoop checkout.
if [[ "${CAUSYNTH_SKIP_GRAPHCHECKER_BUILD:-0}" != "1" ]]; then
  mvn -q -DskipTests package
fi

CAUSYNTH_REPO="${hadoop_root}" \
CAUSYNTH_TRACE_TEST='org.apache.hadoop.hdfs.TestCausynthRpcHeaderPropagation#nameNodeComparesValuesReadOnceFromTwoDataNodes' \
CAUSYNTH_INSTRUMENTED_CLASSES_DIR="${run_dir}/instrumented-classes" \
CAUSYNTH_OUTPUT_DIR="${run_dir}/analysis" \
CAUSYNTH_REGION_PLAN="${run_dir}/runtime/concolic_region_plan.jsonl" \
CAUSYNTH_SCHEDULE_OUTPUT_DIR="${run_dir}" \
CAUSYNTH_CAMPAIGN_SETUP_COMMAND="HADOOP_HOME_DIR=${hadoop_root} HADOOP_PROTOC_PATH=${protoc} LAUNCHER_OUTPUT=${run_dir}/launcher-build experiments/hdfs/causynth-rpc-compare/source-first-launcher.sh build" \
CAUSYNTH_WORKLOAD_COMMAND="HADOOP_HOME_DIR=${hadoop_root} RPC_COMPARE_OUTPUT=${run_dir}/launcher-build experiments/hdfs/causynth-rpc-compare/pass.sh" \
CAUSYNTH_CONCOLIC_REPLAY_COMMAND="HADOOP_HOME_DIR=${hadoop_root} RPC_COMPARE_BUILD_OUTPUT=${run_dir}/launcher-build experiments/hdfs/causynth-rpc-compare/replay.sh" \
  ./run_engine.sh \
    --config experiments/hdfs/causynth-rpc-compare/workflow.properties \
    campaign

z3_report=${final_dir}/z3-result.json
candidate=${final_dir}/candidate.smt2
[[ -s "${z3_report}" ]] || {
  printf '[causynth-rpc] missing Z3 report: %s\n' "${z3_report}" >&2
  exit 1
}
[[ -s "${candidate}" ]] || {
  printf '[causynth-rpc] missing candidate SMT: %s\n' "${candidate}" >&2
  exit 1
}

printf '\n[causynth-rpc] recorded Z3 attempts\n'
jq -r '
  .solverAttempts[]
  | "query=\(.queryOrdinal) attempt=\(.attemptOrdinal)"
    + " strategy=\(.strategy) status=\(.status)"
    + " elapsed_ms=\(.elapsedMillis)"
    + " query_sha256=\(.solverQuerySha256)"
' "${z3_report}"

printf '\n[causynth-rpc] symbolic witness values\n'
jq -r '
  "reachability=" + .reachCondition.reachability,
  if (.symbolicVariableModels | length) == 0 then
    "no satisfying symbolic-variable model"
  else
    .symbolicVariableModels[] as $model
    | $model.variables[]
    | "valuation=\($model.valuationOrdinal)"
      + " source=\(.sourceKey)"
      + " variable=\(.sourceId)"
      + " phase=\(.sourcePhaseId)"
      + " field=\(.fieldSignature)"
      + " value=\(.value)"
      + (if has("nullnessValue")
         then " nullness=\(.nullnessValue)" else "" end)
  end
' "${z3_report}"

printf '\n[causynth-rpc] artifacts=%s\n' "${final_dir}"

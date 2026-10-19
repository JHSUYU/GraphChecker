
cluster_automatic=
blockkey_scope=(
  common:org/apache/hadoop/ipc/Client
  common:org/apache/hadoop/security/token/delegation/DelegationKey
  client:org/apache/hadoop/hdfs/protocol/datatransfer/sasl/DataTransferSaslUtil
  client:org/apache/hadoop/hdfs/protocol/datatransfer/sasl/SaslDataTransferClient
  client:org/apache/hadoop/hdfs/security/token/block/DataEncryptionKey
  client:org/apache/hadoop/hdfs/protocolPB/PBHelperClient
  hdfs:org/apache/hadoop/hdfs/protocol/datatransfer/sasl/SaslDataTransferServer
  hdfs:org/apache/hadoop/hdfs/protocolPB/PBHelper
  hdfs:org/apache/hadoop/hdfs/security/token/block/BlockKey
  hdfs:org/apache/hadoop/hdfs/security/token/block/BlockPoolTokenSecretManager
  hdfs:org/apache/hadoop/hdfs/security/token/block/BlockTokenSecretManager
  hdfs:org/apache/hadoop/hdfs/security/token/block/ExportedBlockKeys
)
system_jar_first=true
system_sources=(
  client:hadoop-hdfs-project/hadoop-hdfs-client/src/main/java
  hdfs:hadoop-hdfs-project/hadoop-hdfs/src/main/java
)

system_paths() {
  module=${repo}/hadoop-hdfs-project/hadoop-hdfs
  report=${module}/target/surefire-reports/TEST-${test_class}.xml
  test_classes=${module}/target/test-classes
  lineage_roots="${repo}/hadoop-common-project/hadoop-common/target/classes:${repo}/hadoop-hdfs-project/hadoop-hdfs-client/target/classes:${module}/target/classes"
}

system_root() {
  case "$1" in
    common) echo "${repo}/hadoop-common-project/hadoop-common/target/classes" ;;
    client) echo "${repo}/hadoop-hdfs-project/hadoop-hdfs-client/target/classes" ;;
    hdfs) echo "${module}/target/classes" ;;
    *) echo "unknown class root: $1" >&2; return 2 ;;
  esac
}

system_classpath() {
  [[ -f "${report}" ]] || {
    echo "missing test report: ${report}; run build first" >&2
    return 2
  }
  python3 "${system_dir}/classpath.py" "${repo}" "${report}"
}

system_build() {
  bash "${system_dir}/build.sh" "${repo}" "${test_class}#${test_method}"
}

system_jvm_properties() {
  jvm_properties=("-Dtest.build.data=$2" "-Dtest.cache.data=${test_classes}")
  [[ "${cluster_automatic}" != true ]] \
    || jvm_properties+=("-Dcausynth.cluster.automatic=true")
}

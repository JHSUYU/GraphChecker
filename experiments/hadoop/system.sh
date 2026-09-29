# system.sh -- the Hadoop system: HDFS MiniDFSCluster trees, built by
# Maven, their workload classpath read off the surefire report.  Sourced by
# lib/case-env.sh before a case's case.sh.
#
# A Hadoop case.sh may also set
#   hadoop_javac        the javac the Hadoop build uses (default: the filter)

hadoop_javac=
# THE block-key family's shared scope: the SASL data-transfer handshake and
# the block-token key managers every case of the family turns on, and the IPC
# client whose propagation calls the causal context travels on.  A case adds
# only what is its own.  The Hadoop shim is not here: it is GraphChecker's
# jar, not a class of the tree.
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
# The launcher supplies the frozen GraphChecker jar ahead of the tree's
# classpath, whose shim entry it replaces.
system_jar_first=true

system_paths() {
  module=${repo}/hadoop-hdfs-project/hadoop-hdfs
  report=${module}/target/surefire-reports/TEST-${classpath_test:-${test_class}}.xml
  test_classes=${module}/target/test-classes
  # The lineage scope is the whole tree's, whatever the case analyses
  # (plan.LineageScan): a thread start or queue handoff in a class outside
  # the analysis scope is still where a thread's cause comes from.
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
  bash "${system_dir}/build.sh" "${repo}" "${test_class}" "${test_method}" \
    "${hadoop_javac}"
}

# MiniDFSCluster puts its name directories, edit logs and block data under
# test.build.data.
system_jvm_properties() {
  jvm_properties=("-Dtest.build.data=$2")
}

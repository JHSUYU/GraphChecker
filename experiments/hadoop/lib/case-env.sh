# case-env.sh -- sourced by every lib script: one case's declarations.
#
#   source case-env.sh <case-dir> <case-id>
#
# The case directory holds DECLARATIONS only (case.sh, workflow.properties,
# target.yaml and the *.jsonl the campaign reads); everything executable is
# here, one copy for every case.  case.sh sets, for the case id it is given:
#   repo          the Hadoop worktree the case runs
#   test_class    the workload's JUnit class
#   test_method   its test method
#   scope         the analysis scope, one "<root>:<class path>" per entry,
#                 root one of common|client|hdfs; "=" after the root copies
#                 exactly that class and its nested classes (no prefix glob)
# and optionally
#   target_occurrence   the declared target (empty keeps every observed one)
#   loop_bounds         default: <case-dir>/loop-bounds.jsonl
#   target_spec         default: <case-dir>/target.yaml
#   hadoop_javac        the javac the Hadoop build uses (default: the filter)
case_dir=${1:?missing case directory}
case_id=${2-}
case_dir=$(cd "${case_dir}" && pwd -P)
case_name=$(basename "${case_dir}")
here=${case_dir}
loop_bounds=${case_dir}/loop-bounds.jsonl
target_spec=${case_dir}/target.yaml
target_occurrence=
hadoop_javac=
scope=()
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
# shellcheck source=/dev/null
source "${case_dir}/case.sh" "${case_id}"
# The discovery hook, for every case alike: set but EMPTY, PLAN refuses with
# DECLARED_TARGET_OCCURRENCE_MISSING and lists every observed target
# occurrence -- the one honest way to re-read an address after an identity
# change.
target_occurrence=${CAUSYNTH_TARGET_OCCURRENCE_OVERRIDE-${target_occurrence}}
module=${repo}/hadoop-hdfs-project/hadoop-hdfs
report=${module}/target/surefire-reports/TEST-${test_class}.xml
tag=${case_name}${case_id:+-${case_id}}
analysis=/tmp/graphchecker-${tag}-classes
test_name=${test_class}#${test_method}

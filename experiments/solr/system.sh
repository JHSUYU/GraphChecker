# system.sh -- the Solr system: SolrCloud MiniSolrCloudCluster trees (Solr
# 8.11, the last line on Java 8), built by Ant, their workload classpath read
# off the junit4 report.  Sourced by lib/case-env.sh before a case's case.sh.
#
# Every Solr workload is a cluster test as it is written: the tree's
# test-framework registers each MiniSolrCloudCluster's nodes and opens the
# window itself (org.apache.solr.cloud.CausynthSolrCluster) when
# causynth.cluster.automatic is set.
#
# A Solr case.sh may also set
#   solr_seed           the randomized-testing seed (default below): the
#                       codec, directory, locale and every random() choice
#                       of the test framework, the same in the recording and
#                       in every replay

solr_seed=F0993D5343E20BA4
# GraphChecker's jar follows the tree's classpath: the tree's own libraries
# (Guava, protobuf, commons-io) are not the engine's versions.
system_jar_first=false
# The class a cluster test names: tools/adhoc/workloads.py lists the tests
# of the classes that do.
system_cluster_class=org/apache/solr/cloud/MiniSolrCloudCluster
# The cluster state's family: the classes that hold it (every node parses
# ClusterState and its collections, slices and replicas out of ZooKeeper) and
# the Overseer's writers of it.  A guard over the state then reads a tracked
# container another region wrote, whose writer the exploration may choose;
# without them it reads concrete objects no root reaches (123 of sweep q5's
# checks).  SOLR-18413's case scope holds the same classes.
solr_state_scope=(
  solrj:org/apache/solr/common/cloud/ClusterState
  solrj:org/apache/solr/common/cloud/DocCollection
  solrj:org/apache/solr/common/cloud/Slice
  solrj:org/apache/solr/common/cloud/Replica
  core:org/apache/solr/cloud/overseer/ZkStateWriter
  core:org/apache/solr/cloud/overseer/SliceMutator
  core:org/apache/solr/cloud/overseer/ReplicaMutator
  core:org/apache/solr/cloud/overseer/CollectionMutator
)
# The tree's own code, for coverage and for the ad-hoc checks' scan: its class
# roots (system_root names), the package JaCoCo counts, and each root's
# sources, as "<root>:<tree-relative source dir>".
system_roots=(solrj core)
system_package=org.apache.solr
system_sources=(
  solrj:solr/solrj/src/java
  core:solr/core/src/java
)
# A class a workload runs only if it starts a node of the system: a test
# that starts none opens no recording window, so an ad-hoc sweep does not
# choose it (tools/adhoc/select.py).
system_node_class=org/apache/solr/client/solrj/embedded/JettySolrRunner

system_paths() {
  module=${repo}/solr/core
  report=${repo}/solr/build/solr-core/test/TEST-${classpath_test:-${test_class}}.xml
  test_classes=${repo}/solr/build/solr-core/classes/test
  lineage_roots="${repo}/solr/build/solr-solrj/classes/java:${repo}/solr/build/solr-core/classes/java:${repo}/solr/build/solr-test-framework/classes/java"
}

system_root() {
  case "$1" in
    solrj) echo "${repo}/solr/build/solr-solrj/classes/java" ;;
    core) echo "${repo}/solr/build/solr-core/classes/java" ;;
    testfw) echo "${repo}/solr/build/solr-test-framework/classes/java" ;;
    lucene) echo "${repo}/lucene/build/core/classes/java" ;;
    *) echo "unknown class root: $1" >&2; return 2 ;;
  esac
}

system_classpath() {
  [[ -f "${report}" ]] || {
    echo "missing test report: ${report}; run build first" >&2
    return 2
  }
  python3 "${system_dir}/classpath.py" "${report}"
}

system_build() {
  bash "${system_dir}/build.sh" "${repo}" "${test_class}" "${test_method}" \
    "${solr_seed}"
}

# What the junit4 runner hands every test JVM of the tree, for a workload
# JVM the engine starts: the randomized-testing seed and environment, the
# test-files home, and the automatic cluster.
system_jvm_properties() {
  jvm_properties=(
    "-DtempDir=$1"
    "-Dtests.seed=${solr_seed}"
    "-Dtests.src.home=${repo}/solr/core"
    "-Dcommon.dir=${repo}/lucene"
    "-Dtests.asserts=true" "-Dtests.slow=true" "-Dtests.nightly=false"
    "-Dtests.timeoutSuite=86400000" "-Dtests.timeout=86400000"
    "-Djetty.testMode=1" "-Djetty.insecurerandom=1"
    "-Dsolr.directoryFactory=org.apache.solr.core.MockDirectoryFactory"
    "-Djdk.map.althashing.threshold=0"
    "-Djava.security.egd=file:/dev/./urandom"
    "-Dcausynth.cluster.automatic=true"
  )
}

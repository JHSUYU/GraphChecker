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
# The ZooKeeper-carried state, woven in every Solr case alike, never named by
# a case: the views a node decodes from the store (ZkStateReader with its
# StateWatcher and AliasesManager, ClusterState, DocCollection, Slice,
# Replica, Aliases, ZkNodeProps), each class and its nested classes.  PLAN
# keeps symbolic only the decodes on the anchor's backward chain over the
# store's (path, version) edges, and runs the rest doors-only; a replay that
# reads a version an off-chain writer or decode made grows the chain (GROW,
# ZK_EDGE; PIPELINE §7.8, SYMBOL-SCOPE §6.4).
system_scope=(
  solrj=:org/apache/solr/common/cloud/ZkStateReader
  solrj=:org/apache/solr/common/cloud/ClusterState
  solrj=:org/apache/solr/common/cloud/DocCollection
  solrj=:org/apache/solr/common/cloud/Slice
  solrj=:org/apache/solr/common/cloud/Replica
  solrj=:org/apache/solr/common/cloud/Aliases
  solrj=:org/apache/solr/common/cloud/ZkNodeProps
)
# The tree's own sources, as "<root>:<tree-relative source dir>": where
# tools/lib/annotated.py finds the throws a known bug's case is marked at.
system_sources=(
  solrj:solr/solrj/src/java
  core:solr/core/src/java
)

system_paths() {
  module=${repo}/solr/core
  report=${repo}/solr/build/solr-core/test/TEST-${test_class}.xml
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
  bash "${system_dir}/build.sh" "${repo}" "${solr_seed}" "${test_class}#${test_method}"
}

# What the junit4 runner hands every test JVM of the tree, for a workload
# JVM the engine starts: the randomized-testing seed and environment, the
# test-files home, and the automatic cluster (build.sh's native run: the
# same seed, parked groups and automatic cluster).
system_jvm_properties() {
  jvm_properties=(
    "-DtempDir=$1"
    "-Dtests.seed=${solr_seed}"
    "-Dtests.src.home=${repo}/solr/core"
    "-Dcommon.dir=${repo}/lucene"
    "-Dtests.asserts=true" "-Dtests.slow=true" "-Dtests.nightly=false"
    # The workload a case names runs whatever test group upstream parked it
    # in: these properties only let @BadApple and @AwaitsFix tests run
    # (TimeRoutedAliasUpdateProcessorTest and its base class, for solr-adhoc-10
    # 13 39 40).
    "-Dtests.badapples=true" "-Dtests.awaitsfix=true"
    "-Dtests.timeoutSuite=86400000" "-Dtests.timeout=86400000"
    "-Djetty.testMode=1" "-Djetty.insecurerandom=1"
    "-Dsolr.directoryFactory=org.apache.solr.core.MockDirectoryFactory"
    "-Djdk.map.althashing.threshold=0"
    "-Djava.security.egd=file:/dev/./urandom"
    "-Dcausynth.cluster.automatic=true"
  )
}

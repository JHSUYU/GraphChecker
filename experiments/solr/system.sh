
solr_seed=F0993D5343E20BA4
system_jar_first=false
system_scope=(
  solrj=:org/apache/solr/common/cloud/ZkStateReader
  solrj=:org/apache/solr/common/cloud/ClusterState
  solrj=:org/apache/solr/common/cloud/DocCollection
  solrj=:org/apache/solr/common/cloud/Slice
  solrj=:org/apache/solr/common/cloud/Replica
  solrj=:org/apache/solr/common/cloud/Aliases
  solrj=:org/apache/solr/common/cloud/ZkNodeProps
)
client_fault_transports=(SOLR_HTTP SOLR_HTTP2)
doors_only_roots=(
  '<org.apache.solr.core.CoreContainer: org.apache.solr.core.SolrCore create(java.lang.String,java.nio.file.Path,java.util.Map,boolean)>'
)
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

system_jvm_properties() {
  jvm_properties=(
    "-DtempDir=$1"
    "-Dtests.seed=${solr_seed}"
    "-Dtests.src.home=${repo}/solr/core"
    "-Dcommon.dir=${repo}/lucene"
    "-Dtests.asserts=true" "-Dtests.slow=true" "-Dtests.nightly=false"
    "-Dtests.badapples=true" "-Dtests.awaitsfix=true"
    "-Dtests.timeoutSuite=86400000" "-Dtests.timeout=86400000"
    "-Djetty.testMode=1" "-Djetty.insecurerandom=1"
    "-Dsolr.directoryFactory=org.apache.solr.core.MockDirectoryFactory"
    "-Djdk.map.althashing.threshold=0"
    "-Djava.security.egd=file:/dev/./urandom"
    "-Dcausynth.cluster.automatic=true"
  )
}


zk_module=
# Every workload JVM, recorded, replayed or native (build.sh): one commit worker, so a quorum's commits apply in one
# order; no snapshot within a case (a background snapshot's timing differs run to run).
zk_run_properties=(-Dzookeeper.commitProcessor.numWorkerThreads=1 -Dzookeeper.snapCount=1000000)
system_jar_first=false
system_scope=()
system_sources=(
  jute:zookeeper-jute/src/main/java
  server:zookeeper-server/src/main/java
  election:zookeeper-recipes/zookeeper-recipes-election/src/main/java
  lock:zookeeper-recipes/zookeeper-recipes-lock/src/main/java
  queue:zookeeper-recipes/zookeeper-recipes-queue/src/main/java
  inspector:zookeeper-contrib/zookeeper-contrib-zooinspector/src/main/java
)

# The module whose tests hold the workload: a case may name it (zk_module=), else the first module with its source.
zk_test_module() {
  [[ -z "${zk_module}" ]] || { echo "${zk_module}"; return 0; }
  local source
  for source in "${repo}"/zookeeper-server/src/test/java/"${test_class//.//}".java \
      "${repo}"/zookeeper-recipes/*/src/test/java/"${test_class//.//}".java \
      "${repo}"/zookeeper-contrib/*/src/test/java/"${test_class//.//}".java; do
    [[ -f "${source}" ]] || continue
    source=${source#"${repo}/"}
    echo "${source%/src/test/java/*}"
    return 0
  done
  echo zookeeper-server
}

system_paths() {
  test_module=$(zk_test_module)
  module=${repo}/${test_module}
  report=${module}/target/surefire-reports/TEST-${test_class}.xml
  test_classes=${module}/target/test-classes
  local each
  lineage_roots=
  for each in "${test_module}" zookeeper-server zookeeper-jute; do
    [[ ":${lineage_roots}:" == *":${repo}/${each}/target/classes:"* ]] \
      || lineage_roots+=${lineage_roots:+:}${repo}/${each}/target/classes
  done
  lineage_roots+=:${test_classes}
}

system_root() {
  case "$1" in
    jute) echo "${repo}/zookeeper-jute/target/classes" ;;
    server) echo "${repo}/zookeeper-server/target/classes" ;;
    election|lock|queue)
      echo "${repo}/zookeeper-recipes/zookeeper-recipes-$1/target/classes" ;;
    inspector) echo "${repo}/zookeeper-contrib/zookeeper-contrib-zooinspector/target/classes" ;;
    *) echo "unknown class root: $1" >&2; return 2 ;;
  esac
}

system_classpath() {
  [[ -f "${report}" ]] || {
    echo "missing test report: ${report}; run build first" >&2
    return 2
  }
  python3 "${system_dir}/classpath.py" "${repo}" "${test_module}" "${report}"
}

zookeeper_spec() {
  echo "${test_module:-$(zk_test_module)}|${test_class}#${test_method}"
}

system_build() {
  ZK_TEST_PROPERTIES="${zk_run_properties[*]} ${zk_jvm_properties[*]-}" MAVEN_REPO_LOCAL=${MAVEN_REPO_LOCAL:-${ZOOKEEPER_MAVEN_REPO:-${GC_M2}/zookeeper${repo//\//_}}} \
    bash "${system_dir}/build.sh" "${repo}" "$(zk_test_module)" "${test_class}" \
    "${test_method}"
}

system_jvm_properties() {
  jvm_properties=(
    "-Dbuild.test.dir=$2"
    "-Dzookeeper.DigestAuthenticationProvider.superDigest=super:D/InIHSb7yEEbrWz8b9l71RjZJU="
    "-Dlogback.configurationFile=${system_dir}/logback.xml"
    "-Dcausynth.cluster.automatic=true"
    "${zk_run_properties[@]}"
    "${zk_jvm_properties[@]+"${zk_jvm_properties[@]}"}"
  )
}

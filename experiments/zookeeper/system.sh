
zk_module=zookeeper-server
zk_maven_repo=${GC_M2}/zookeeper
system_jar_first=false
system_sources=(
  server:zookeeper-server/src/main/java
  election:zookeeper-recipes/zookeeper-recipes-election/src/main/java
  lock:zookeeper-recipes/zookeeper-recipes-lock/src/main/java
  queue:zookeeper-recipes/zookeeper-recipes-queue/src/main/java
)

system_paths() {
  module=${repo}/${zk_module}
  report=${module}/target/surefire-reports/TEST-${test_class}.xml
  test_classes=${module}/target/test-classes
  local each
  lineage_roots=
  for each in "${zk_module}" zookeeper-server zookeeper-jute; do
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
    *) echo "unknown class root: $1" >&2; return 2 ;;
  esac
}

system_classpath() {
  [[ -f "${report}" ]] || {
    echo "missing test report: ${report}; run build first" >&2
    return 2
  }
  python3 "${system_dir}/classpath.py" "${repo}" "${zk_module}" "${report}"
}

system_build() {
  MAVEN_REPO_LOCAL=${MAVEN_REPO_LOCAL:-${zk_maven_repo}} \
    bash "${system_dir}/build.sh" "${repo}" "${zk_module}" "${test_class}" \
    "${test_method}"
}

system_jvm_properties() {
  jvm_properties=(
    "-Dbuild.test.dir=$2"
    "-Dzookeeper.DigestAuthenticationProvider.superDigest=super:D/InIHSb7yEEbrWz8b9l71RjZJU="
    "-Dlogback.configurationFile=${system_dir}/logback.xml"
    "-Dcausynth.cluster.automatic=true"
  )
}

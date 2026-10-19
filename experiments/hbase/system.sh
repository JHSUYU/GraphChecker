system_jar_first=false
system_scope=()
client_fault_transports=(HBASE_RPC)
system_sources=(
  common:hbase-common/src/main/java
  client:hbase-client/src/main/java
  zookeeper:hbase-zookeeper/src/main/java
  procedure:hbase-procedure/src/main/java
  server:hbase-server/src/main/java
  backup:hbase-backup/src/main/java
)
hbase_modules=(hbase-common hbase-client hbase-zookeeper hbase-procedure
  hbase-asyncfs hbase-balancer hbase-replication hbase-server)

hbase_test_module() {
  local source
  for source in "${repo}"/hbase-*/src/test/java/"${test_class//.//}".java; do
    [[ -f "${source}" ]] || continue
    source=${source#"${repo}/"}
    echo "${source%%/*}"
    return 0
  done
  echo hbase-server
}

system_paths() {
  test_module=$(hbase_test_module)
  module=${repo}/${test_module}
  report=${module}/target/surefire-reports/TEST-${test_class}.xml
  test_classes=${module}/target/test-classes
  local name roots=()
  for name in "${hbase_modules[@]}"; do
    roots+=("${repo}/${name}/target/classes")
  done
  [[ " ${hbase_modules[*]} " == *" ${test_module} "* ]] || roots+=("${module}/target/classes")
  lineage_roots=$(IFS=:; echo "${roots[*]}")
}

system_root() {
  case "$1" in
    common|client|zookeeper|procedure|server|backup)
      echo "${repo}/hbase-$1/target/classes" ;;
    *) echo "unknown class root: $1" >&2; return 2 ;;
  esac
}

system_classpath() {
  [[ -f "${report}" ]] || {
    echo "missing test report: ${report}; run build first" >&2
    return 2
  }
  python3 "${system_dir}/classpath.py" "${repo}" "${report}" "${test_module}"
}

hbase_spec() {
  echo "${test_class}#${test_method}${recording_window:+@${recording_window}}"
}

system_build() {
  bash "${system_dir}/build.sh" "${repo}" "$(hbase_spec)"
}

system_jvm_properties() {
  jvm_properties=(
    "-Dtest.build.data.basedirectory=$2"
    "-Djava.net.preferIPv4Stack=true"
    "-Dio.netty.eventLoopThreads=3"
    "-Djava.security.egd=file:/dev/./urandom"
    "-Dcausynth.cluster.automatic=true"
  )
}

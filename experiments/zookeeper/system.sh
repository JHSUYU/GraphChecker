# system.sh -- the ZooKeeper system: branch-3.9 trees (the newest line on
# Java 8), built by Maven into a Maven repository of their own, their
# workload classpath read off the surefire report.  Sourced by
# lib/case-env.sh before a case's case.sh.
#
# Every workload is a ClientBase test as it is written: the tree's test code
# registers its server and its clients and opens the window itself
# (org.apache.zookeeper.test.CausynthZkCluster) when causynth.cluster.automatic
# is set, and a client's requests reach the server's pipeline as messages
# (org.apache.zookeeper.CausynthZk).
#
# A ZooKeeper case.sh also sets
#   zk_module   the tree-relative Maven module of the workload's test class
#               (default zookeeper-server; the recipes' tests are in
#               zookeeper-recipes/zookeeper-recipes-<name>)

zk_module=zookeeper-server
# The Maven repository every ZooKeeper tree builds with: its SNAPSHOT
# artifacts are the tree's own, never the shared ~/.m2's.
zk_maven_repo=/bigtemp/vnr3ne/m2/zookeeper
# GraphChecker's jar follows the tree's classpath: the tree's own libraries
# (slf4j and its binding, Netty) are not the engine's versions.
system_jar_first=false
# The tree's own sources, as "<root>:<tree-relative source dir>": where
# tools/lib/annotated.py finds the throws a known bug's case is marked at.
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
  # The lineage scope (plan.LineageScan): the tree's class roots the
  # workload's classpath holds -- its module's, the server's and jute's, the
  # ones classpath.py puts first and the build makes (-am).  A recipe another
  # module holds is no class the workload can load: woven, it does not verify
  # against the workload's classpath (ZK5: the lock recipe's ProtocolSupport).
  local each
  lineage_roots=
  for each in "${zk_module}" zookeeper-server zookeeper-jute; do
    [[ ":${lineage_roots}:" == *":${repo}/${each}/target/classes:"* ]] \
      || lineage_roots+=${lineage_roots:+:}${repo}/${each}/target/classes
  done
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

# What surefire hands every test JVM of the tree, for a workload JVM the
# engine starts: the directory ClientBase makes its servers' data in (a
# relative default would write into the tree), the super user digest some
# tests authenticate with, a logging configuration that logs warnings only
# (the tree's logs every request at INFO with its caller's line, which a
# replay on the interpreter pays for), and the automatic cluster.
system_jvm_properties() {
  jvm_properties=(
    "-Dbuild.test.dir=$2"
    "-Dzookeeper.DigestAuthenticationProvider.superDigest=super:D/InIHSb7yEEbrWz8b9l71RjZJU="
    "-Dlogback.configurationFile=${system_dir}/logback.xml"
    "-Dcausynth.cluster.automatic=true"
  )
}

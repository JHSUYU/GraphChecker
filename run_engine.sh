#!/bin/bash

graphchecker_dir=$(cd "$(dirname "${BASH_SOURCE-$0}")"; pwd)
graphchecker_jar="${graphchecker_dir}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar"

banner() {
  echo ""
  echo "  ╔═══════════════════════════════════════════╗"
  echo "  ║           G R A P H C H E C K E R         ║"
  echo "  ║       Soot-based Bytecode Transformer      ║"
  echo "  ╚═══════════════════════════════════════════╝"
  echo ""
}

usage() {
  echo "Usage: ./run_engine.sh <command> [args...]"
  echo ""
  echo "  Commands:"
  echo "    build              Build the GraphChecker tool"
  echo "    transform <conf>   Transform target system bytecode"
  echo "    help               Print this help message"
  echo ""
}

banner

if [[ $# -eq 0 || "$1" == "help" ]]; then
  usage
  exit 0
fi

if [[ "$1" == "build" ]]; then
  echo "Building GraphChecker..."
  mvn -f "${graphchecker_dir}/pom.xml" clean package -DskipTests
  exit $?
fi

if [[ "$1" == "transform" ]]; then
  if [[ -z "$2" ]]; then
    echo "Error: transform requires a config file argument"
    echo "Usage: ./run_engine.sh transform <config-file>"
    exit 1
  fi

  conf_file_path="$2"
  conf_file_realpath=$(realpath "${conf_file_path}")

  if [[ ! -f "${conf_file_realpath}" ]]; then
    echo "Error: config file not found: ${conf_file_realpath}"
    exit 1
  fi

  # Source the config to get system_classes_path, java_class_path, etc.
  source "${conf_file_path}"

  echo "Config file: ${conf_file_realpath}"
  echo "system_dir_path: ${system_dir_path}"
  echo "system_classes_path: ${system_classes_path}"
  echo "java_class_path: ${java_class_path}"

  export SOOT_CLASSPATH="${java_class_path}"

  if [[ ! -f "${graphchecker_jar}" ]]; then
    echo "Error: GraphChecker jar not found at ${graphchecker_jar}"
    echo "Run './run_engine.sh build' first."
    exit 1
  fi

  full_class_path="${graphchecker_jar}:${java_class_path}"

  echo "Transforming bytecode..."
  SECONDS=0
  java -cp "${full_class_path}" edu.uva.liftlab.graphchecker.GraphCheckerMain \
    -i "${system_classes_path}" \
    -x "${java_class_path}" \
    -C "${conf_file_realpath}" \
    -o "${system_classes_path}"
  duration=$SECONDS
  echo "[Profiler] Transform spent ${duration} seconds"
  exit $?
fi

echo "Error: unknown command '$1'"
usage
exit 1

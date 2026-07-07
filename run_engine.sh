#!/bin/bash

set -euo pipefail

graphchecker_dir=$(cd "$(dirname "${BASH_SOURCE-$0}")"; pwd)
graphchecker_jar="${graphchecker_dir}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar"

usage() {
  echo "Usage: ./run_engine.sh <command> [args...]"
  echo ""
  echo "Commands:"
  echo "  build              Build the GraphChecker tool"
  echo "  process <conf>     Run the Causynth Soot transformer over configured classes"
  echo "  transform <conf>   Alias for process"
  echo "  help               Print this help message"
}

if [[ $# -eq 0 || "$1" == "help" ]]; then
  usage
  exit 0
fi

if [[ "$1" == "build" ]]; then
  mvn -f "${graphchecker_dir}/pom.xml" clean package -DskipTests
  exit $?
fi

if [[ "$1" == "process" || "$1" == "transform" ]]; then
  if [[ $# -lt 2 ]]; then
    echo "Error: process requires a config file argument"
    usage
    exit 1
  fi

  conf_file_path="$2"
  conf_file_realpath=$(realpath "${conf_file_path}")
  if [[ ! -f "${conf_file_realpath}" ]]; then
    echo "Error: config file not found: ${conf_file_realpath}"
    exit 1
  fi

  source "${conf_file_realpath}"

  if [[ ! -f "${graphchecker_jar}" ]]; then
    echo "Error: GraphChecker jar not found at ${graphchecker_jar}"
    echo "Run './run_engine.sh build' first."
    exit 1
  fi

  SECONDS=0
  java -cp "${graphchecker_jar}:${java_class_path}" \
    edu.uva.liftlab.graphchecker.GraphCheckerMain \
    -i "${system_classes_path}" \
    -x "${java_class_path}" \
    -C "${conf_file_realpath}" \
    -o "${system_classes_path}"
  echo "[Profiler] process spent ${SECONDS} seconds"
  exit $?
fi

echo "Error: unknown command '$1'"
usage
exit 1

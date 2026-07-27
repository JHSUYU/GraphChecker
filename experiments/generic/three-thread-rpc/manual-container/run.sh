#!/usr/bin/env bash

set -euo pipefail

fixture_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker_dir=$(cd "${fixture_dir}/../../../.." && pwd -P)
workflow="${fixture_dir}/workflow.properties"
pipeline="${fixture_dir}/../run.sh"
source_file="${graphchecker_dir}/src/test/java/edu/uva/liftlab/graphchecker/manual/ContainerThreeThreadRpcWorkload.java"
class_root="${graphchecker_dir}/target/manual-container-test-classes"
work_root="${graphchecker_dir}/target/manual-container-three-thread-rpc"
smt="${work_root}/candidate/candidate.smt2"
workflow_log="${work_root}/workflow.log"
legacy_workflow_log="${graphchecker_dir}/target/manual-container-workflow.log"

die() {
  echo "[manual-container] $*" >&2
  exit 1
}

clean_classes() {
  [[ ! -L "${class_root}" ]] \
    || die "refusing to clean symlinked class directory: ${class_root}"
  if [[ -d "${class_root}" ]]; then
    find "${class_root}" -mindepth 1 -delete
  fi
}

do_clean() {
  CAUSYNTH_WORKFLOW_CONFIG="${workflow}" "${pipeline}" clean
  clean_classes
  rm -f "${legacy_workflow_log}"
}

do_build() {
  [[ -f "${source_file}" ]] || die "workload source not found: ${source_file}"
  (cd "${graphchecker_dir}" && mvn -q -Dmaven.test.skip=true package)
  clean_classes
  mkdir -p "${class_root}"
  javac -source 8 -target 8 \
    -cp "${graphchecker_dir}/target/classes" \
    -d "${class_root}" "${source_file}"
}

do_z3() {
  [[ -s "${smt}" ]] || die "candidate SMT not found: ${smt}"
  local result
  result=$(z3 "${smt}" | sed -n '1p')
  [[ "${result}" == "sat" || "${result}" == "unsat" ]] \
    || die "Z3 returned an unexpected result: ${result:-<empty>}"
  printf '%s\n' "${result}"
}

do_run() {
  local workflow_status
  do_clean
  mkdir -p "${work_root}"
  echo "[manual-container] running; live log: ${workflow_log}" >&2
  set +e
  {
    do_build &&
      (cd "${graphchecker_dir}" && \
        CAUSYNTH_WORKFLOW_CONFIG="${workflow}" \
        GRAPH_CHECKER_SKIP_BUILD=true \
        "${pipeline}" candidate-smt) &&
      do_z3
  } 2>&1 | tee "${workflow_log}"
  workflow_status=${PIPESTATUS[0]}
  set -e
  [[ "${workflow_status}" -eq 0 ]] \
    || die "workflow failed; inspect ${workflow_log}"
}

case "${1:-run}" in
  clean) [[ $# -eq 1 ]] || die "clean takes no arguments"; do_clean ;;
  build) [[ $# -eq 1 ]] || die "build takes no arguments"; do_build ;;
  run) [[ $# -le 1 ]] || die "run takes no arguments"; do_run ;;
  z3) [[ $# -eq 1 ]] || die "z3 takes no arguments"; do_z3 ;;
  *) die "usage: $0 [clean|build|run|z3]" ;;
esac

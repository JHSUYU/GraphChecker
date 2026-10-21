#!/usr/bin/env bash
# prepare-trees.sh [name...]: check out every ZooKeeper tree of trees.tsv under GC_TREES (from the fork, ZOOKEEPER_FORK)
# and build it with the workload of every case of zookeeper-cases.tsv that runs on it, each checked to pass natively
# (build.sh). Each workload module is installed once (with what it needs), then each workload's test runs alone. Maven repository: ZOOKEEPER_MAVEN_REPO
# (default ${GC_M2}/zookeeper<tree path>). Prints PASSED/FAILED <class>#<method> <s> per case.
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker=$(cd "${here}/../.." && pwd -P)
source "${graphchecker}/tools/lib/gc-env.sh"
source "${graphchecker}/experiments/lib/case-id.sh"
fork=${ZOOKEEPER_FORK:-https://github.com/JHSUYU/zookeeper.git}

names=("$@")
((${#names[@]} > 0)) || mapfile -t names < <(awk -F'\t' '$1 !~ /^#/ && NF {print $1}' "${here}/trees.tsv")
(cd "${graphchecker}" && mvn -q -o -DskipTests package)
failed=0
for name in "${names[@]}"; do
  branch=$(awk -F'\t' -v n="${name}" '$1 == n {print $2}' "${here}/trees.tsv")
  [[ -n "${branch}" ]] || { echo "${name}: not in trees.tsv" >&2; exit 2; }
  tree=${GC_TREES}/${name}
  if [[ ! -d "${tree}/.git" && ! -f "${tree}/.git" ]]; then
    mkdir -p "${GC_TREES}"
    git clone -q --branch "${branch}" --single-branch "${fork}" "${tree}"
  fi
  echo "== ${name}: ${branch} at $(git -C "${tree}" rev-parse --short HEAD), $(date +%T) on $(hostname)"
  installed=" "
  while IFS=$'\t' read -r id _; do
    [[ -n "${id}" && "${id}" != \#* ]] || continue
    read -r dir arg <<<"$(case_dir_of "${graphchecker}" "${id}")"
    [[ "${arg}" != - ]] || arg=""
    spec=$(bash -c 'source "$1" "$2" "$3" >/dev/null && [[ "$(basename "${repo}")" == "$4" ]] && \
        echo "$(zk_test_module)|${test_class}|${test_method}|${zk_run_properties[*]} ${zk_jvm_properties[*]-}|${zk_maven_profiles[*]-}"' \
      _ "${graphchecker}/experiments/lib/case-env.sh" "${dir}" "${arg}" "${name}") || continue
    IFS='|' read -r module test_class test_method properties profiles <<<"${spec}"
    started=${SECONDS} skip=0
    [[ "${installed}" != *" ${module} "* ]] || skip=1
    if SKIP_GRAPHCHECKER_INSTALL=1 SKIP_TREE_INSTALL=${skip} ZK_TEST_PROPERTIES="${properties}" ZK_MAVEN_PROFILES="${profiles}" \
        MAVEN_REPO_LOCAL=${ZOOKEEPER_MAVEN_REPO:-${GC_M2}/zookeeper${tree//\//_}} \
        bash "${here}/build.sh" "${tree}" "${module}" "${test_class}" "${test_method}" >/dev/null 2>&1; then
      echo "PASSED   ${id} ${test_class}#${test_method} $((SECONDS - started)) s"
    else
      echo "FAILED   ${id} ${test_class}#${test_method} $((SECONDS - started)) s"
      failed=$((failed + 1))
    fi
    installed+="${module} "
  done <"${here}/zookeeper-cases.tsv"
  echo "== ${name}: ready $(date +%T), ${failed} failed"
done
((failed == 0))

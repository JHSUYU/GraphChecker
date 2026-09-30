#!/usr/bin/env bash
# nightly.sh <system>/<adhoc-experiment> [date]
#   e.g. tools/adhoc/nightly.sh hadoop/adhoc; tools/adhoc/nightly.sh solr/solr-adhoc
#
# One frozen, complete ad-hoc sweep of one experiment, comparable night to
# night, in $GC_OUT/nightly/<date>-<experiment>/ (<date> default today,
# YYYY-MM-DD).  It is never stopped for an engine fix: fixes are tested on
# snapshots of their own.
#
# 1. Freeze.  The snapshot is the newest commit of this repository tagged
#    regress-pass-* -- an annotated tag whose message holds a line
#    "vm=<concolic VM image>", the image the commit passed its regressions
#    on -- checked out detached as ~/gc-run/n<date>-<experiment> and built.
#    $GC_OUT/snapshots-in-use/<snapshot name> locks it until the sweep has
#    ended (tools/rounds/snapshot-gc.sh refuses a locked snapshot).
#    manifest.json states the commit and tag, the jar's sha256, the VM image
#    and its libjvm.so's sha256, the tree and its commit, and the build key
#    (buildkey.sh).
# 2. Select, each step cached where its inputs are:
#    - per tree commit, $GC_OUT/coverage/<experiment>-<commit>/: the cluster
#      tests (workloads.py), the checks (sites.py), one coverage run per test
#      on the lifts (coverage.sh through fanout.sh), the reached checks
#      (reach.py); run again only for a new tree;
#    - select.py declare and targets.py, in the snapshot's own experiment;
#    - per build key: every declared check's slice and score (slice.sh), then
#      select.py rank: the kept checks and the calibration tail, every
#      twentieth dropped check (5%), scheduled every night to measure what the
#      static selection drops;
#    - cover.py jobs, the pre-screen recordings (prescreen.sh, per build key),
#      cover.py cases.
# 3. Run: sweep.sh over the cases from the snapshot, with this night's
#    directory as GC_OUT (the cluster's one host ledger stays), at most
#    NIGHTLY_HEADS (default 2) heads per lift, on the tag's VM image.  Then,
#    once: a case triage.py classes DEAD, or STOPPED because a disk or quota
#    filled, ssh failed or the case timeout killed it, lost to the
#    infrastructure, runs again (its accept-<round>-<n> moved aside to
#    .lost, its fanout .exit removed).  A second loss, or a seed replay past
#    its bound, is a result.
# 4. Report: triage.tsv; findings.tsv (findings.py, with the cluster's
#    ledger $GC_OUT/findings/ledger.jsonl); report.md (funnel.py: every
#    step's count, and the kept checks' outcomes beside the calibration
#    tail's).  Then the lock goes.
#
# Started again with the same date it resumes: every step keeps or resumes
# what it finished, and the infrastructure re-run happens once.
set -euo pipefail
experiment_rel=${1:?usage: nightly.sh <system>/<adhoc-experiment> [date]}
date=${2:-$(date +%F)}
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
repo=$(cd "${here}/../.." && pwd -P)
# shellcheck source=../lib/gc-env.sh
source "${repo}/tools/lib/gc-env.sh"
name=$(basename "${experiment_rel}")
night=${GC_OUT}/nightly/${date}-${name}
snapshot=${HOME}/gc-run/n${date}-${name}
lock=${GC_OUT}/snapshots-in-use/$(basename "${snapshot}")
round=n${date//-/}-${name}
say() { echo "$(date +%T) nightly ${date}-${name}: $*" >&2; }
mkdir -p "${night}" "$(dirname "${lock}")"

# 1. Freeze.
tag=$(git -C "${repo}" for-each-ref --sort=-creatordate --count=1 \
  --format='%(refname:short)' 'refs/tags/regress-pass-*')
[[ -n "${tag}" ]] || { say "no regress-pass-* tag names a snapshot"; exit 2; }
commit=$(git -C "${repo}" rev-parse "${tag}^{commit}")
vm=$(git -C "${repo}" tag -l --format='%(contents)' "${tag}" \
  | sed -n 's/^vm=//p' | head -n 1)
[[ -n "${vm}" && -x "${vm}/bin/java" ]] \
  || { say "tag ${tag} names no VM image (a line vm=<image>): '${vm}'"; exit 2; }
echo "${night}" >"${lock}"
if [[ ! -e "${snapshot}" ]]; then
  git -C "${repo}" worktree add --detach "${snapshot}" "${commit}"
fi
[[ "$(git -C "${snapshot}" rev-parse HEAD)" == "${commit}" ]] \
  || { say "${snapshot} is not at ${tag} (${commit})"; exit 2; }
jar=${snapshot}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar
if [[ ! -s "${jar}" ]]; then
  say "building ${snapshot} at ${tag}"
  (cd "${snapshot}" && env JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64 \
    PATH=/usr/lib/jvm/java-8-openjdk-amd64/bin:/usr/lib/maven/bin:${PATH} \
    mvn -q -o package -DskipTests)
fi
experiment=${snapshot}/experiments/${experiment_rel}
tools=${snapshot}/tools/adhoc
system_dir=$(dirname "${experiment}")
read -r tree <"${experiment}/tree"
tree_commit=$(git -C "${tree}" rev-parse HEAD)
key=$(bash "${tools}/buildkey.sh" "${experiment}")
if [[ ! -s "${night}/manifest.json" ]]; then
  jq -n --arg tag "${tag}" --arg commit "${commit}" --arg snapshot "${snapshot}" \
    --arg jarSha "$(sha256sum <"${jar}" | cut -d' ' -f1)" --arg vm "${vm}" \
    --arg libjvm "$(find "${vm}/" -name libjvm.so -print0 | sort -z \
      | xargs -0 cat | sha256sum | cut -d' ' -f1)" \
    --arg tree "${tree}" --arg treeCommit "${tree_commit}" --arg key "${key}" \
    --arg round "${round}" --arg experiment "${name}" \
    '{experiment: $experiment, tag: $tag, commit: $commit, snapshot: $snapshot,
      jar: {sha256: $jarSha}, vm: {path: $vm, libjvmSha256: $libjvm},
      tree: {path: $tree, commit: $treeCommit}, buildKey: $key,
      round: $round}' >"${night}/manifest.json"
fi
say "snapshot ${snapshot} (${tag}), build ${key}, tree ${tree}@${tree_commit:0:12}"

# 2. Select.  Coverage, per tree commit.
cov=${GC_OUT}/coverage/${name}-${tree_commit:0:12}
if [[ ! -s "${cov}/reached.jsonl" ]]; then
  say "coverage of ${tree}@${tree_commit:0:12} into ${cov}"
  mkdir -p "${cov}/cov"
  python3 "${tools}/workloads.py" "${system_dir}" "${tree}" >"${cov}/workloads.tsv"
  python3 "${tools}/sites.py" "${system_dir}" "${tree}" >"${cov}/sites.jsonl"
  # The experiment's own reading of a "<TestClass>-<method>" workload: the
  # test report that states the module's classpath, and the properties its
  # workload JVMs get.
  read -r first_class first_method <"${cov}/workloads.tsv"
  first_check=$(awk -F'\t' '!/^#/ && NF {print $1; exit}' "${experiment}/checks.tsv")
  mapfile -t declared < <(bash -c 'source "$1/experiments/lib/case-env.sh" \
    "$2" "$3" >/dev/null || exit 2
    printf "%s\n" "${classpath_test}" "${workload_properties[*]}"' _ \
    "${snapshot}" "${experiment}" \
    "${first_check}.${first_class##*.}-${first_method}")
  [[ -n "${declared[0]:-}" ]] || { say "the experiment names no test report \
for ${first_class}.${first_method}: build the tree first"; exit 2; }
  while IFS=$'\t' read -r test_class test_method; do
    printf 'WORKLOAD_JAVA_OPTS=%q bash tools/adhoc/coverage.sh %s %s %s %s %s %s/cov/%s.%s\n' \
      "${declared[1]}" "${system_dir}" "${tree}" "${declared[0]}" "${test_class}" \
      "${test_method}" "${cov}" "${test_class##*.}" "${test_method}"
  done <"${cov}/workloads.tsv" >"${cov}/cov-jobs.txt"
  bash "${tools}/fanout.sh" "${cov}/cov-jobs.txt" "${cov}/cov-logs" \
    >"${cov}/cov-fanout.log"
  python3 "${tools}/reach.py" "${cov}/sites.jsonl" "${cov}/cov" \
    >"${cov}/reached.jsonl.partial"
  mv "${cov}/reached.jsonl.partial" "${cov}/reached.jsonl"
fi
# The night is a sweep directory over that coverage (coverage_runs.py).
for file in reached.jsonl workloads.tsv cov-jobs.txt cov-fanout.log cov; do
  ln -sfn "${cov}/${file}" "${night}/${file}"
done
python3 "${tools}/select.py" "${night}" "${experiment}" declare "${tree}" \
  >"${night}/declared.txt"
python3 "${tools}/targets.py" "${experiment}" "${tree}"
say "$(wc -l <"${night}/declared.txt") declared checks; slicing"
bash "${tools}/slice.sh" "${experiment}" "${night}/declared.txt" \
  >"${night}/slice.log"
python3 "${tools}/select.py" "${night}" "${experiment}" rank \
  "${GC_OUT}/static/${key}" "${night}/declared.txt"
python3 "${tools}/cover.py" "${night}" "${experiment}" jobs
say "$(wc -l <"${night}/prescreen-jobs.tsv") pre-screen recordings"
bash "${tools}/prescreen.sh" "${experiment}" "${night}/prescreen-jobs.tsv" \
  >"${night}/prescreen.log"
python3 "${tools}/cover.py" "${night}" "${experiment}" cases \
  "${GC_OUT}/prescreen/${key}"

# 3. Run.
sweep() {
  GC_OUT=${night} VM_IMAGE=${vm} bash "${tools}/sweep.sh" "${snapshot}" \
    "${round}" "${night}/cases.txt" "${NIGHTLY_HEADS:-2}" \
    >>"${night}/sweep.log" 2>&1
}
say "$(wc -l <"${night}/cases.txt") cases, round ${round}"
sweep
if [[ ! -e "${night}/requeued.txt" ]]; then
  python3 "${tools}/triage.py" "${round}" "${night}" >"${night}/triage.tsv"
  awk -F'\t' 'NR > 1 && ($3 == "DEAD" || ($3 == "STOPPED" && $8 ~ \
    /Disk quota exceeded|No space left on device|killed at the case timeout|ssh|[Cc]onnection (refused|reset|closed)/)) \
    {print $1}' "${night}/triage.tsv" >"${night}/requeued.txt"
  while read -r n; do
    mv -- "${night}/accept-${round}-${n}" "${night}/accept-${round}-${n}.lost"
    rm -f -- "${night}/sweep-${round}-logs/${n}.exit"
  done <"${night}/requeued.txt"
  if [[ -s "${night}/requeued.txt" ]]; then
    say "$(wc -l <"${night}/requeued.txt") case(s) lost to the infrastructure run again"
    sweep
  fi
fi

# 4. Report.
python3 "${tools}/triage.py" "${round}" "${night}" >"${night}/triage.tsv"
python3 "${tools}/findings.py" "${night}" --ledger "${GC_OUT}/findings/ledger.jsonl" \
  --static "${GC_OUT}/static/${key}"
python3 "${tools}/funnel.py" "${night}" "${GC_OUT}/static/${key}" \
  "${GC_OUT}/prescreen/${key}" >"${night}/report.md"
rm -f -- "${lock}"
say "done: ${night}/report.md"

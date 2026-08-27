#!/usr/bin/env bash
#
# Drive the whole 20-case RPC matrix and report one verdict per scenario.
#
# The matrix is twenty independent campaigns, not twenty assertions inside one
# run.  Each row selects its producer pair with a compile-time constant
# (DataNode.CAUSYNTH_RPC_SCENARIO), so a row owns a Hadoop checkout for as long
# as it runs: two rows sharing one checkout would race on that constant and on
# the class files the setup stage rebuilds from it.
#
# The checkouts are leased per LANE rather than per row.  A lane keeps its
# worktree across the rows it runs, so only DataNode.java changes between them
# and the setup stage recompiles incrementally; a lease per row would instead
# pay a full Hadoop build twenty times and hold twenty build trees at once.
#
# Usage:
#   run-matrix.sh                  # all twenty rows
#   run-matrix.sh 3 7 14           # only those rows
#   run-matrix.sh --lanes 4        # four rows in flight at once
#
# Environment:
#   CAUSYNTH_RPC_HADOOP_ROOT  Hadoop checkout to branch the leases from
#                             (default: /users/ZhenyuLi/dev/hadoop).  This must
#                             be the checkout carrying the Causynth commits --
#                             /opt/hadoop is a stale tree without them.
#   CAUSYNTH_RPC_MATRIX_BASE  where campaign roots are written.  A campaign is
#                             ~74 MB, so twenty rows want a couple of gigabytes
#                             free -- not the root disk.
#   CAUSYNTH_RPC_WORKTREE_BASE  where the leases live.  A Hadoop worktree plus
#                             its build output is a few GB per lane.
#   CAUSYNTH_RPC_LANES        rows in flight (default 4).  Each row already
#                             runs an eight-worker replay, so lanes multiply
#                             that: 4 lanes is ~32 replay JVMs.
#   CAUSYNTH_RPC_KEEP_WORKTREES  1 to keep the leases for debugging.  Keeping
#                             them makes the next matrix run start warm.
#
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd -P)
hadoop_root=${CAUSYNTH_RPC_HADOOP_ROOT:-/users/ZhenyuLi/dev/hadoop}
matrix_base=${CAUSYNTH_RPC_MATRIX_BASE:-/proj/silentfailure-PG0/gc-rpc-compare/matrix}
worktree_base=${CAUSYNTH_RPC_WORKTREE_BASE:-${matrix_base}/worktrees}
lanes=${CAUSYNTH_RPC_LANES:-4}
keep_worktrees=${CAUSYNTH_RPC_KEEP_WORKTREES:-0}

datanode_rel=hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/datanode/DataNode.java

scenarios=()
while [[ $# -gt 0 ]]; do
  case $1 in
    --lanes) lanes=$2; shift 2 ;;
    --lanes=*) lanes=${1#*=}; shift ;;
    -h|--help) sed -n '2,34p' "$0"; exit 0 ;;
    *)
      [[ $1 =~ ^([1-9]|1[0-9]|20)$ ]] || {
        printf '[matrix] not a scenario number: %s\n' "$1" >&2
        exit 2
      }
      scenarios+=("$1"); shift ;;
  esac
done
if [[ ${#scenarios[@]} -eq 0 ]]; then
  scenarios=(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20)
fi
[[ ${lanes} =~ ^[0-9]+$ && ${lanes} -ge 1 ]] || {
  printf '[matrix] lanes must be a positive integer: %s\n' "${lanes}" >&2
  exit 2
}
[[ ${lanes} -le ${#scenarios[@]} ]] || lanes=${#scenarios[@]}

[[ -d "${hadoop_root}/.git" ]] || {
  printf '[matrix] not a Hadoop git checkout: %s\n' "${hadoop_root}" >&2
  exit 2
}
grep -q 'CAUSYNTH_RPC_SCENARIO' "${hadoop_root}/${datanode_rel}" || {
  printf '[matrix] checkout carries no RPC matrix: %s\n' "${hadoop_root}" >&2
  printf '[matrix] expected the Causynth commits on this branch.\n' >&2
  exit 2
}

run_stamp=$(date -u +%Y%m%dT%H%M%SZ)
matrix_dir=${matrix_base}/matrix-${run_stamp}
verdict_dir=${matrix_dir}/verdicts
mkdir -p "${verdict_dir}" "${worktree_base}"

printf '[matrix] hadoop=%s\n' "${hadoop_root}"
printf '[matrix] rows=%s lanes=%s\n' "${#scenarios[@]}" "${lanes}"
printf '[matrix] output=%s\n' "${matrix_dir}"

# The GraphChecker jar is shared by every row and is not scenario dependent.
# Build it once here so twenty campaigns do not each rebuild it, and so a
# compile error surfaces before any worktree is leased.  A caller that has
# just built and gated the jar itself says so with
# CAUSYNTH_SKIP_GRAPHCHECKER_BUILD=1: rebuilding here would race anything
# else reading target/*.jar at the same moment (the replay drift checks did,
# and lost nine rows to "Could not find or load main class").
if [[ ${CAUSYNTH_SKIP_GRAPHCHECKER_BUILD:-0} == 1 ]]; then
  printf '[matrix] using the existing GraphChecker jar (skip-build requested)\n'
else
  printf '[matrix] building GraphChecker once\n'
  ( cd "${repo_root}" && mvn -q -DskipTests package )
fi
export CAUSYNTH_SKIP_GRAPHCHECKER_BUILD=1

lease_for_lane() {
  # A lane's checkout, created once and reused for every row it runs.
  local lane=$1 lease
  printf -v lease '%s/lane-%02d' "${worktree_base}" "${lane}"
  if [[ ! -e "${lease}/.git" ]]; then
    git -C "${hadoop_root}" worktree add --detach --force "${lease}" HEAD >/dev/null 2>&1
  fi
  printf '%s' "${lease}"
}

select_scenario() {
  # Rewrite only the selector, from a clean copy of the file, so a lane's
  # previous row cannot leave anything behind.
  local lease=$1 scenario=$2
  git -C "${lease}" checkout --quiet --force HEAD -- "${datanode_rel}"
  sed -i -E "s/(CAUSYNTH_RPC_SCENARIO = )[0-9]+;/\1${scenario};/" \
    "${lease}/${datanode_rel}"
  grep -Eq "CAUSYNTH_RPC_SCENARIO = ${scenario};" "${lease}/${datanode_rel}"
}

summarise_row() {
  local scenario=$1 label=$2 rc=$3 elapsed=$4 run_dir=$5 log=$6
  local final=${run_dir}/final
  local result=${final}/result.json
  local candidate=${final}/candidate.smt2
  local z3=${final}/z3-result.json

  local status=FAILED sha='' models=0 fastest='' detail=''

  if [[ -n "${run_dir}" && -s "${result}" ]]; then
    # The solver report is the authority, not the exit code and not the
    # directory existing.  These are exactly the four fields the README's
    # acceptance jq checks.
    if jq -e '
          .finalStatus == "FINAL_READY"
          and .claim == "SAT_CANDIDATE"
          and .reachability == "REACHABLE"
          and .gapCount == 0
        ' "${result}" >/dev/null 2>&1; then
      status=PASS
    else
      status=REFUSED
      detail=$(jq -r '"finalStatus=\(.finalStatus) claim=\(.claim) reachability=\(.reachability) gaps=\(.gapCount)"' \
                 "${result}" 2>/dev/null || echo 'unreadable result.json')
    fi
    [[ -s "${candidate}" ]] && sha=$(sha256sum "${candidate}" | cut -c1-12)
    if [[ -s "${z3}" ]]; then
      models=$(jq -r '(.symbolicVariableModels // []) | length' "${z3}" 2>/dev/null || echo 0)
      fastest=$(jq -r '
        [ .solverAttempts[]? | select(.status == "sat") | .elapsedMillis ]
        | if length == 0 then "" else (min | tostring) end' "${z3}" 2>/dev/null || echo '')
    fi
  else
    detail="no result.json; see ${log}"
  fi

  jq -n \
    --argjson scenario "${scenario}" \
    --arg label "${label}" \
    --arg status "${status}" \
    --argjson rc "${rc}" \
    --argjson elapsed "${elapsed}" \
    --arg runDir "${run_dir}" \
    --arg candidateSha "${sha}" \
    --argjson models "${models:-0}" \
    --arg fastestSatMillis "${fastest}" \
    --arg detail "${detail}" \
    --arg log "${log}" \
    '$ARGS.named'
}

run_scenario_in_lease() {
  local scenario=$1 lease=$2 label log verdict
  printf -v label 'scenario-%02d' "${scenario}"
  log=${matrix_dir}/${label}.log
  verdict=${verdict_dir}/${label}.json

  if ! select_scenario "${lease}" "${scenario}"; then
    printf '[matrix] %s could not select the scenario in %s\n' "${label}" "${lease}" >&2
    printf '{"scenario":%s,"label":"%s","status":"LEASE_FAILED"}\n' \
      "${scenario}" "${label}" > "${verdict}"
    return 0
  fi

  printf '[matrix] %s start (lease=%s)\n' "${label}" "${lease}"
  local started=${SECONDS} rc=0
  CAUSYNTH_RPC_SCENARIO="${scenario}" \
  CAUSYNTH_RPC_HADOOP_ROOT="${lease}" \
  CAUSYNTH_RPC_RUN_BASE="${matrix_dir}" \
    "${repo_root}/experiments/hdfs/causynth-rpc-compare/run-z3.sh" \
    >"${log}" 2>&1 || rc=$?
  local elapsed=$((SECONDS - started))

  # run-z3.sh mktemp's its own directory under the run base; recover the one
  # this row produced rather than guessing the suffix.
  local run_dir
  run_dir=$(grep -m1 -oE "${matrix_dir}/${label}\.[A-Za-z0-9]+" "${log}" || true)

  summarise_row "${scenario}" "${label}" "${rc}" "${elapsed}" "${run_dir}" "${log}" \
    > "${verdict}"
  printf '[matrix] %s done rc=%s elapsed=%ss\n' "${label}" "${rc}" "${elapsed}"
}

run_lane() {
  # One lane: its own checkout, its rows one after another.
  local lane=$1; shift
  local lease
  lease=$(lease_for_lane "${lane}")
  local scenario
  for scenario in "$@"; do
    run_scenario_in_lease "${scenario}" "${lease}"
  done
}

# Deal the rows round robin so neighbouring scenario numbers, which tend to
# stress the solver similarly, do not all land in one lane.
declare -a lane_rows
for ((lane = 0; lane < lanes; lane++)); do lane_rows[lane]=''; done
index=0
for scenario in "${scenarios[@]}"; do
  lane=$((index % lanes))
  lane_rows[lane]="${lane_rows[lane]} ${scenario}"
  index=$((index + 1))
done

pids=()
for ((lane = 0; lane < lanes; lane++)); do
  # The row list is a deliberate word split into separate arguments.
  # shellcheck disable=SC2086
  run_lane "${lane}" ${lane_rows[lane]} &
  pids+=("$!")
done
for pid in "${pids[@]}"; do
  wait "${pid}" || true
done

if [[ "${keep_worktrees}" != "1" ]]; then
  for ((lane = 0; lane < lanes; lane++)); do
    printf -v lease '%s/lane-%02d' "${worktree_base}" "${lane}"
    [[ -d "${lease}" ]] || continue
    git -C "${hadoop_root}" worktree remove --force "${lease}" >/dev/null 2>&1 || true
  done
  git -C "${hadoop_root}" worktree prune >/dev/null 2>&1 || true
fi

summary=${matrix_dir}/matrix-summary.json
jq -s 'sort_by(.scenario)' "${verdict_dir}"/*.json > "${summary}"

printf '\n[matrix] %-3s %-8s %-13s %-7s %-7s %s\n' \
  '#' 'status' 'sha' 'models' 'sat_ms' 'detail'
jq -r '
  .[]
  | [ (.scenario|tostring), .status, (.candidateSha // "-"),
      ((.models // 0)|tostring), (.fastestSatMillis // "-"), (.detail // "") ]
  | @tsv
' "${summary}" | while IFS=$'\t' read -r n st sha models ms detail; do
  printf '[matrix] %-3s %-8s %-13s %-7s %-7s %s\n' \
    "${n}" "${st}" "${sha:--}" "${models}" "${ms:--}" "${detail}"
done

passed=$(jq '[ .[] | select(.status == "PASS") ] | length' "${summary}")
total=$(jq 'length' "${summary}")
printf '\n[matrix] %s/%s rows passed\n' "${passed}" "${total}"
printf '[matrix] summary=%s\n' "${summary}"

[[ "${passed}" == "${total}" ]]

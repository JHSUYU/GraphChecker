#!/usr/bin/env bash
set -uo pipefail
snapshot=$(cd "${1:?snapshot}" && pwd -P)
round=${2:?round}
cases_file=${3:?cases file}
heads=${4:-1}
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
# shellcheck source=../../run_engine.sh
source "${here}/../../run_engine.sh"
set +e
# shellcheck source=../lib/heads.sh
source "${here}/../lib/heads.sh"
out=${GC_OUT}
vm=CAUSYNTH_CUSTOM_JDK_HOME=${VM_IMAGE:?sweep.sh: name the concolic VM image as VM_IMAGE}
mkdir -p "${out}"

mapfile -t cases < <(grep -v '^\s*\(#\|$\)' "${cases_file}")
stop_after=
[[ -z "${CAUSYNTH_CAMPAIGN_STOP_AFTER+x}" ]] \
  || stop_after=" CAUSYNTH_CAMPAIGN_STOP_AFTER='${CAUSYNTH_CAMPAIGN_STOP_AFTER}'"
jobs="${out}/sweep-${round}-jobs.txt"
: > "${jobs}"
: > "${out}/sweep-${round}-cases.tsv"
for n in "${!cases[@]}"; do
  config=$(case_config "${snapshot}" "${cases[$n]}")
  [[ -n "${config}" ]] || {
    echo "sweep.sh: ${cases[$n]} names no case (its configuration could \
not be read): no case is launched" >&2
    exit 2
  }
  printf '%s\t%s\n' "${n}" "${cases[$n]}" >> "${out}/sweep-${round}-cases.tsv"
  printf '%s\n' "ADMIT_MB=$(case_head_reserve_mb "${config}") PRUNE=${PRUNE:-1} CASE_TIMEOUT_SECONDS=${CASE_TIMEOUT_SECONDS:-5400} CAUSYNTH_STREAM_SHARED_POOL=true CAUSYNTH_CAMPAIGN_WORKER_HOSTS='${LIFTS}' $(gc_env_words)${vm}${stop_after} bash ${snapshot}/tools/rounds/launch-run.sh ${snapshot} '${cases[$n]}' ${round}-${n}" >> "${jobs}"
done
exec bash "${here}/fanout.sh" "${jobs}" "${out}/sweep-${round}-logs" "${heads}"

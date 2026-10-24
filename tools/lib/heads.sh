# shellcheck shell=bash

# shellcheck source=../../experiments/lib/case-id.sh
source "$(dirname "${BASH_SOURCE[0]}")/../../experiments/lib/case-id.sh"

case_config() {
  local snapshot=$1 id=$2 dir="" arg=""
  read -r dir arg < <(case_dir_of "${snapshot}" "${id}") || return 0
  [[ "${arg}" != - ]] || arg=""
  (cd "${dir}" && CAUSYNTH_CLASSPATH_OVERRIDE=unread bash \
    "${snapshot}/experiments/lib/run.sh" "${dir}" "${arg}" config 2>/dev/null)
}

case_value() {
  sed -n "s/^$1=//p" <<<"$2"
}

case_engine_heap_mb() {
  local mb
  mb=$(case_value engine_memory_mb "$1")
  echo "${mb:-8192}"
}

case_head_reserve_mb() {
  local engine_memory_mb campaign_engine_outgrown=""
  engine_memory_mb=$(case_value engine_memory_mb "$1")
  campaign_head_need_mb
}

heads_choose() {
  local entry need case_id host best mb free
  local -A room=() cores=() headed=()
  for entry in "$@"; do
    IFS=: read -r host mb free <<<"${entry}"
    room[${host}]=${mb}
    cores[${host}]=${free}
    headed[${host}]=0
  done
  (( ${#room[@]} > 0 )) || return 1
  sort -s -k1,1nr | while read -r need case_id; do
    best=""
    for entry in "$@"; do
      host=${entry%%:*}
      if [[ -z "${best}" ]] || (( headed[${host}] < headed[${best}] )) \
          || { (( headed[${host}] == headed[${best}] )) \
               && campaign_host_roomier "${cores[${host}]}" \
                 "${room[${host}]}" "${cores[${best}]}" "${room[${best}]}"; }
      then
        best=${host}
      fi
    done
    printf '%s %s\n' "${case_id}" "${best}"
    headed[${best}]=$(( headed[${best}] + 1 ))
    room[${best}]=$(( room[${best}] - need ))
    cores[${best}]=$(( cores[${best}] - campaign_engine_cores ))
  done
}

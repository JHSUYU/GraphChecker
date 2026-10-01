# shellcheck shell=bash
# heads.sh -- sourced by the launchers of campaigns (tools/rounds/
# launch-round.sh, tools/adhoc/sweep.sh): what a case's head needs, and
# which host heads it.
#
#   case_head_need_mb <snapshot> <case-id>
#       the heap a case's head needs: the experiment a case id names is the
#       longest "-"-prefix of it with a case.sh (accept.sh acc_experiment_of),
#       and its config states engine_memory_mb, empty for the launcher's
#       8192.  The heap is no function of the workload's classpath, which a
#       tree's test report states only once the workload ran, so the config
#       reads none.
#
#   heads_choose <host>:<room_mb>...  <"<need_mb> <case-id>" lines
#       prints "<case-id> <host>", one line per case, in launch order: the
#       heaviest case first (ties in the order given), each to the host with
#       the most room among those that head the fewest cases so far, that
#       host's room then less the case's need -- no host heads two cases
#       before every host heads one.  The rooms are the host ledger's
#       (run_engine.sh campaign_host_room), read by the caller.

case_head_need_mb() {
  local snapshot=$1 id=$2 exp=$2 dir mb=""
  while :; do
    for dir in "${snapshot}"/experiments/*/"${exp}"; do
      [[ -f "${dir}/case.sh" ]] || continue
      local arg=${id#"${exp}"}
      mb=$(cd "${dir}" && CAUSYNTH_CLASSPATH_OVERRIDE=unread bash \
        "${snapshot}/experiments/lib/run.sh" "${dir}" "${arg#-}" config \
        2>/dev/null | sed -n 's/^engine_memory_mb=//p')
      break 2
    done
    [[ "${exp}" == *-* ]] || break
    exp=${exp%-*}
  done
  echo "${mb:-8192}"
}

heads_choose() {
  local entry need case_id host best
  local -A room=() headed=()
  for entry in "$@"; do
    room[${entry%%:*}]=${entry#*:}
    headed[${entry%%:*}]=0
  done
  (( ${#room[@]} > 0 )) || return 1
  sort -s -k1,1nr | while read -r need case_id; do
    best=""
    for entry in "$@"; do
      host=${entry%%:*}
      if [[ -z "${best}" ]] || (( headed[${host}] < headed[${best}] \
          || (headed[${host}] == headed[${best}] \
              && room[${host}] > room[${best}]) )); then
        best=${host}
      fi
    done
    printf '%s %s\n' "${case_id}" "${best}"
    headed[${best}]=$(( headed[${best}] + 1 ))
    room[${best}]=$(( room[${best}] - need ))
  done
}

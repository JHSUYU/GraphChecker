# shellcheck shell=bash
# heads.sh -- sourced by the launchers of campaigns (tools/rounds/
# launch-round.sh, tools/adhoc/sweep.sh), after run_engine.sh: what a case's
# head needs, and which host heads it.
#
#   case_config <snapshot> <case-id>
#       the case's workflow configuration, one key=value line per key, as
#       run.sh's `config` prints it: the experiment a case id names is the
#       longest "-"-prefix of it with a case.sh (accept.sh acc_experiment_of).
#       The configuration is no function of the workload's classpath, which
#       a tree's test report states only once the workload ran, so it reads
#       none.  Empty when the case id names no experiment.
#
#   case_value <key> <config>
#       one key's value in a case's configuration, empty when it states none.
#
#   case_engine_heap_mb <config>
#       the case's engine heap: engine_memory_mb, else the launcher's 8192
#       -- what launch-round.sh weighs a case's head by (heads_choose).
#
#   case_head_reserve_mb <config>
#       the room the case's head reserves on its host from its launch on, at
#       that heap (run_engine.sh campaign_head_need_mb: what its planner or
#       composer starts at): every other step it runs is charged where it is
#       placed, so this is what a sweep's head is admitted for (fanout.sh
#       NEED_MB, tools/adhoc/sweep.sh).
#
#   heads_choose <host>:<room_mb>...  <"<need_mb> <case-id>" lines
#       prints "<case-id> <host>", one line per case, in launch order: the
#       heaviest case first (ties in the order given), each to the host with
#       the most room among those that head the fewest cases so far, that
#       host's room then less the case's need -- no host heads two cases
#       before every host heads one.  The rooms are the host ledger's
#       (run_engine.sh campaign_host_room), read by the caller.

case_config() {
  local snapshot=$1 id=$2 exp=$2 dir
  while :; do
    for dir in "${snapshot}"/experiments/*/"${exp}"; do
      [[ -f "${dir}/case.sh" ]] || continue
      local arg=${id#"${exp}"}
      (cd "${dir}" && CAUSYNTH_CLASSPATH_OVERRIDE=unread bash \
        "${snapshot}/experiments/lib/run.sh" "${dir}" "${arg#-}" config \
        2>/dev/null)
      return 0
    done
    [[ "${exp}" == *-* ]] || return 0
    exp=${exp%-*}
  done
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

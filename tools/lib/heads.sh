# shellcheck shell=bash
# heads.sh -- sourced by the launchers of campaigns (tools/rounds/
# launch-round.sh, tools/adhoc/sweep.sh), after run_engine.sh: what a case's
# head needs, and which host heads it.
#
#   case_config <snapshot> <case-id>
#       the case's workflow configuration, one key=value line per key, as
#       run.sh's `config` prints it, of the case directory the id names
#       (experiments/lib/case-id.sh case_dir_of).
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
#       that heap (run_engine.sh campaign_head_need_mb: the JVM footprint
#       of what its planner or composer starts at, the composer's with its
#       z3 room): every other step it runs is charged where it is
#       placed, so this is what a sweep's head is admitted for (fanout.sh
#       ADMIT_MB, tools/adhoc/sweep.sh) -- admitted, not charged for life:
#       its campaign reserves the room itself (run_engine.sh
#       campaign_head_reserve).
#
#   heads_choose <host>:<room_mb>...  <"<need_mb> <case-id>" lines
#       prints "<case-id> <host>", one line per case, in launch order: the
#       heaviest case first (ties in the order given), each to the host with
#       the most room among those that head the fewest cases so far, that
#       host's room then less the case's need -- no host heads two cases
#       before every host heads one.  The rooms are the host ledger's
#       (run_engine.sh campaign_host_room), read by the caller.

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

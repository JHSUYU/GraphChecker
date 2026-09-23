#!/usr/bin/env bash
# queue-launch.sh <snapshot> <prefix> host:case[,case...][:queued-case,...] ...
# Launch each host's first cases at once (over ssh, detached); a case listed
# after a second ':' starts when one of the cases running on that host has
# written its summary line.  Outputs: $GC_OUT/accept-<prefix>-<case>/, launcher
# log $GC_OUT/launch-<prefix>-<case>.log (its "process group N" line is how to
# stop one run: ssh host kill -TERM -N; then pkill -f 'gc-run/p2[3]' for the
# obligation JVMs the driver keeps spawning).  Two cases per host at most.
#   tools/rounds/queue-launch.sh /u/vnr3ne/gc-run/p23 v20 lift12:hdfs-17899-bug3,hdfs-17967-pathA lift13:hdfs-17899-bug1:hdfs-17967-pathC
set -uo pipefail
snapshot=$1; prefix=$2; shift 2
launch() {
  local host=$1 case_id=$2
  local suffix=${prefix}-${case_id#hdfs-}
  ssh -n -o BatchMode=yes "$host" "setsid nohup bash ${snapshot}/tools/rounds/launch-run.sh ${snapshot} ${case_id} ${suffix} > ${GC_OUT:-/u/vnr3ne/gc-out}/launch-${suffix}.log 2>&1 < /dev/null &"
  echo "$(date +%T) LAUNCHED ${case_id} on ${host} -> accept-${suffix}"
}
done_yet() {  # a summary with its result line
  local f=${GC_OUT:-/u/vnr3ne/gc-out}/accept-${prefix}-${1#hdfs-}/summary.tsv
  [ -f "$f" ] && [ "$(wc -l < "$f")" -ge 2 ]
}
for spec in "$@"; do
  host=${spec%%:*}; rest=${spec#*:}
  first=${rest%%:*}; later=""
  [[ "$rest" == *:* ]] && later=${rest#*:}
  IFS=, read -ra now <<<"$first"
  for c in "${now[@]}"; do launch "$host" "$c"; done
  if [[ -n "$later" ]]; then
    IFS=, read -ra queue <<<"$later"
    ( waiting=("${now[@]}")
      for c in "${queue[@]}"; do
        # start when ANY of the cases currently running on this host is done
        while :; do
          for w in "${waiting[@]}"; do done_yet "$w" && { waiting=("${waiting[@]/$w}"); break 2; }; done
          sleep 60
        done
        launch "$host" "$c"; waiting+=("$c")
      done ) &
  fi
done
wait
echo "$(date +%T) queue drained"

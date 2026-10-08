# case-id.sh -- sourced: the one rule for which case directory a case id
# names (the harness, the round and sweep launchers and the offline gate).
#
#   case_dir_of <repo> <case-id>
#       prints "<case dir> <case arg>": the experiment, under any system of
#       <repo>/experiments, whose name is the longest "-"-prefix of the id
#       holding a case.sh, and the id's rest after it, "-" when there is
#       none (hdfs-17899-bug1: .../hadoop/hdfs-17899 bug1; solr-18413:
#       .../solr/solr-18413 -).  Fails when no experiment holds the id.
case_dir_of() {
  local repo=$1 id=$2 exp=$2 dir="" arg=""
  while :; do
    for dir in "${repo}"/experiments/*/"${exp}"; do
      [[ -f "${dir}/case.sh" ]] || continue
      arg=${id#"${exp}"}
      arg=${arg#-}
      printf '%s %s\n' "${dir}" "${arg:--}"
      return 0
    done
    [[ "${exp}" == *-* ]] || return 1
    exp=${exp%-*}
  done
}

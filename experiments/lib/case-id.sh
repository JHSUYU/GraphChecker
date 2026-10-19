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

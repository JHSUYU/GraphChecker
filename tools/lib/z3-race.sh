Z3_RACE_CAP_MB=4096
z3_race() {
  local file=$1 seconds=$2 dir engine winner="" pid
  local -a pids=()
  dir=$(mktemp -d "${TMPDIR:-/tmp}/z3race.XXXXXX")
  for engine in 2 6; do
    setsid bash -c 'sed "s/(set-option :smt.arith.solver [0-9]*)/(set-option :smt.arith.solver $1)/" "$2" \
        | timeout $(($3 + 30)) "$4" memory_max_size="$6" -T:"$3" -in 2>&1 \
        | sed "s/^(error \"out of memory\")\$/memout/" >"$5.part"; mv "$5.part" "$5"' \
      _ "${engine}" "${file}" "${seconds}" "${Z3_BIN}" "${dir}/${engine}" \
      "${Z3_RACE_CAP_MB}" </dev/null &
    pids+=($!)
  done
  while [[ -z "${winner}" ]]; do
    for engine in 2 6; do
      [[ -f "${dir}/${engine}" ]] && grep -qxE 'sat|unsat' "${dir}/${engine}" && winner=${engine} && break
    done
    [[ -n "${winner}" || ! ( -f "${dir}/2" && -f "${dir}/6" ) ]] || winner=2
    [[ -n "${winner}" ]] || sleep 0.2
  done
  for pid in "${pids[@]}"; do kill -- "-${pid}" 2>/dev/null; done
  wait 2>/dev/null
  cat "${dir}/${winner}"
  rm -rf "${dir}"
}

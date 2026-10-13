# z3-race.sh -- sourced: z3_race <file> <seconds>, z3 on one query under both arithmetic
# engines the engine itself races (smt.arith.solver 2 and 6, smt/Z3#ARITHMETIC), each a copy of
# the query with its stated engine option replaced as the text streams; prints the output of the
# first that decides (a line `sat` or `unsat`), else that of engine 2.  z3's time on one query
# swings by orders of magnitude with the engine (solr-18413 SC1: undecided in 300 s under 2, sat
# in 0.2 s under 6), so a check that asks one engine only reports "undecided" for a decided file.
# Each engine runs under z3's own memory cap, Z3_RACE_CAP_MB (4096 MB): uncapped, one z3 of a
# composed query can take a host (SGF3-adhoc-13's grew to 10.9 GB); one at its cap prints
# `(error "out of memory")`, printed here as `memout`, undecided like any answer but sat or unsat.
# Needs Z3_BIN (tools/lib/gc-env.sh).
Z3_RACE_CAP_MB=4096
z3_race() {
  local file=$1 seconds=$2 dir engine winner="" pid
  local -a pids=()
  dir=$(mktemp -d "${TMPDIR:-/tmp}/z3race.XXXXXX")
  for engine in 2 6; do
    # A session of its own, so the loser's whole pipeline ends with one kill.
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

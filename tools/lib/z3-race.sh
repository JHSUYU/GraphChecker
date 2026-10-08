# z3-race.sh -- sourced: z3_race <file> <seconds>, z3 on one query under both arithmetic
# engines the engine itself races (smt.arith.solver 2 and 6, smt/Z3#ARITHMETIC), each a copy of
# the query with its stated engine option replaced as the text streams; prints the output of the
# first that decides (a line `sat` or `unsat`), else that of engine 2.  z3's time on one query
# swings by orders of magnitude with the engine (solr-18413 SC1: undecided in 300 s under 2, sat
# in 0.2 s under 6), so a check that asks one engine only reports "undecided" for a decided file.
# Needs Z3_BIN (tools/lib/gc-env.sh).
z3_race() {
  local file=$1 seconds=$2 dir engine winner="" pid
  local -a pids=()
  dir=$(mktemp -d "${TMPDIR:-/tmp}/z3race.XXXXXX")
  for engine in 2 6; do
    # A session of its own, so the loser's whole pipeline ends with one kill.
    setsid bash -c 'sed "s/(set-option :smt.arith.solver [0-9]*)/(set-option :smt.arith.solver $1)/" "$2" \
        | timeout $(($3 + 30)) "$4" -T:"$3" -in >"$5.part" 2>&1; mv "$5.part" "$5"' \
      _ "${engine}" "${file}" "${seconds}" "${Z3_BIN}" "${dir}/${engine}" </dev/null &
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

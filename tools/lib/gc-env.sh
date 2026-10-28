: "${GC_BULK:=/bigtemp/vnr3ne}"
: "${GC_REPO:=${HOME}/GraphChecker}"
: "${GC_OUT:=${GC_BULK}/gc-out}"
: "${GC_TREES:=${GC_BULK}/wt}"
: "${GC_M2:=${GC_BULK}/m2}"
: "${Z3_BIN:=${HOME}/.local/bin/z3}"
: "${CAUSYNTH_HOST_LEDGER:=${GC_BULK}/gc-out/hosts}"
# liftlab: the worker lifts; lift11 is the control host (the lead's sessions), out of the workers
: "${LIFTS:=lift02 lift03 lift04 lift05 lift06 lift07 lift08 lift09 lift10 lift12 lift13 lift14 lift15}"
: "${GC_CONTROL_HOST:=lift11}"
: "${CAUSYNTH_HOST_MAX_USED_PCT:=70}"
export GC_BULK GC_REPO GC_OUT GC_TREES GC_M2 Z3_BIN CAUSYNTH_HOST_LEDGER LIFTS GC_CONTROL_HOST CAUSYNTH_HOST_MAX_USED_PCT

round_runs() {
  local dir case_id
  for dir in "${GC_OUT}/accept-$1-"*/; do
    case_id=$(ls "${dir}out" 2>/dev/null | head -1)
    [[ -n ${case_id} ]] || continue
    dir=${dir%/}
    printf '%s\t%s\n' "${dir##*/accept-$1-}" "${case_id}"
  done
}

gc_env_names=(GC_BULK GC_REPO GC_OUT GC_TREES GC_M2 Z3_BIN CAUSYNTH_HOST_LEDGER LIFTS GC_CONTROL_HOST CAUSYNTH_HOST_MAX_USED_PCT)
gc_env_words() {
  local name
  for name in "${gc_env_names[@]}"; do
    printf '%s=%q ' "${name}" "${!name}"
  done
}

# gc-env.sh -- where runs write and which hosts run them, stated once.
# Sourced by run_engine.sh and by every tool that launches, fans out, watches
# or stops runs; each value is the environment's when it is set.
#
#   GC_BULK               the bulk storage every lift mounts at the same
#                         path; the defaults below live under it
#   GC_OUT                a run's output root (accept-<round>-<n>/, sweep and
#                         launch logs)
#   GC_TREES              the systems' trees, each at the name its cases'
#                         case.sh gives it (experiments/hadoop/trees.tsv)
#   GC_M2                 the trees' Maven repositories, one per tree
#   Z3_BIN                the z3 every stage and probe runs (4.14.1)
#   CAUSYNTH_HOST_LEDGER  the per-host memory ledger every campaign head,
#                         obligation and fanout job is charged to
#                         (run_engine.sh campaign_host_try_start): one for
#                         the whole cluster, whatever GC_OUT a run writes to,
#                         since two ledgers do not see each other -- change
#                         it only when no run is going
#   LIFTS                 the hosts, as one word list
#   CAUSYNTH_HOST_MAX_USED_PCT
#                         the most of a host's memory, in percent of its
#                         MemTotal, that a start admitted by the ledger may
#                         leave in use (the owner's ceiling: 70)
: "${GC_BULK:=/bigtemp/vnr3ne}"
: "${GC_OUT:=${GC_BULK}/gc-out}"
: "${GC_TREES:=${GC_BULK}/wt}"
: "${GC_M2:=${GC_BULK}/m2}"
: "${Z3_BIN:=${HOME}/.local/bin/z3}"
: "${CAUSYNTH_HOST_LEDGER:=${GC_BULK}/gc-out/hosts}"
: "${LIFTS:=lift06 lift07 lift08 lift09 lift10 lift11 lift12 lift13 lift14 lift15}"
: "${CAUSYNTH_HOST_MAX_USED_PCT:=70}"
export GC_BULK GC_OUT GC_TREES GC_M2 Z3_BIN CAUSYNTH_HOST_LEDGER LIFTS CAUSYNTH_HOST_MAX_USED_PCT

# gc_env_words: the values above as NAME=value words, for a command another
# host runs.  ssh drops the environment, and each replay re-reads its case.sh
# (experiments/lib/execute.sh), so every hop that starts a run or a piece of
# one elsewhere (launch-round.sh's heads, a sweep's jobs, a campaign's remote
# workers) passes them: the whole run sees one tree, one z3, one ledger.
# round_runs <round>: one "<n>\t<case>" line per run of the round under
# GC_OUT, accept-<round>-<n>, whatever started it (a sweep numbers its runs;
# launch-run.sh, launch-round.sh and run-series.sh name them by case): the
# case is the run's own out/<case>.  A run that has not made it yet is left out.
round_runs() {
  local dir case_id
  for dir in "${GC_OUT}/accept-$1-"*/; do
    case_id=$(ls "${dir}out" 2>/dev/null | head -1)
    [[ -n ${case_id} ]] || continue
    dir=${dir%/}
    printf '%s\t%s\n' "${dir##*/accept-$1-}" "${case_id}"
  done
}

gc_env_names=(GC_BULK GC_OUT GC_TREES GC_M2 Z3_BIN CAUSYNTH_HOST_LEDGER LIFTS CAUSYNTH_HOST_MAX_USED_PCT)
gc_env_words() {
  local name
  for name in "${gc_env_names[@]}"; do
    printf '%s=%q ' "${name}" "${!name}"
  done
}

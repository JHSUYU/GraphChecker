# gc-env.sh -- where runs write and which hosts run them, stated once.
# Sourced by run_engine.sh and by every tool that launches, fans out, watches
# or stops runs; each value is the environment's when it is set.
#
#   GC_OUT                a run's output root (accept-<round>-<n>/, sweep and
#                         launch logs), on a filesystem every lift mounts
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
gc_root=/bigtemp/vnr3ne/gc-out
: "${GC_OUT:=${gc_root}}"
: "${CAUSYNTH_HOST_LEDGER:=${gc_root}/hosts}"
: "${LIFTS:=lift06 lift07 lift08 lift09 lift10 lift11 lift12 lift13 lift14 lift15}"
: "${CAUSYNTH_HOST_MAX_USED_PCT:=70}"
export GC_OUT CAUSYNTH_HOST_LEDGER LIFTS CAUSYNTH_HOST_MAX_USED_PCT

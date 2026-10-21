repo=${GC_TREES}/hbase-checks
row=$(awk -F'\t' -v id="${1:?usage: case.sh <NN>}" '$1 == id' "${here}/checks.tsv")
[[ -n "${row}" ]] || { echo "unknown HBase ad hoc check: $1" >&2; return 2; }
IFS=$'\t' read -r _ test_class test_method window target_occurrence classes <<<"${row}"
case "${window}" in
  up) ;;
  startup) recording_window=startup ;;
  *) echo "check $1: unknown window '${window}' (up: once the cluster is up; startup: before its HBase cluster starts)" >&2; return 2 ;;
esac
read -r -a scope <<<"${classes}"
case "$1" in
  34)
    export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=1
    client_fault_transports+=(ZOOKEEPER)
    ;;
  07)
    export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
    client_fault_transports=(ZOOKEEPER)
    ;;
  21)
    export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
    export CAUSYNTH_REGION_PATH_MAX_TASKS=128
    ;;
  11|12|14|15)
    # scope cut (owner 2026-10-21): the heavy TestRegionMove / TestMergeTableRegionsProcedure workloads -- no client
    # HBASE_RPC faults (their claims are state pairings), the first claim only, a 60 min campaign, a 16 GB engine heap
    export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
    client_fault_transports=(ZOOKEEPER)
    export CAUSYNTH_CAMPAIGN_MAX_CLAIMS=1 CAUSYNTH_CAMPAIGN_BUDGET_S=3600 GRAPH_CHECKER_ENGINE_MEMORY_MB=16384
    ;;
  *) export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0 ;;
esac

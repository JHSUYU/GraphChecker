repo=${GC_TREES}/lucene-solr-checks
row=$(awk -F'\t' -v id="${1:?usage: case.sh <NN>}" '$1 == id' "${here}/checks.tsv")
[[ -n "${row}" ]] || { echo "unknown Solr ad hoc check: $1" >&2; return 2; }
IFS=$'\t' read -r _ test_class test_method window target_occurrence classes <<<"${row}"
case "${window}" in
  up) ;;
  *) echo "check $1: unknown window '${window}' (the Solr adapter opens its window once a cluster is up)" >&2; return 2 ;;
esac
read -r -a scope <<<"${classes}"
if [[ "$1" == 05 ]]; then
  loop_bounds=${here}/loop-bounds-05.jsonl
fi
case "$1" in
  05|07|14|31)
    # scope cut (owner 2026-10-22: "如果case扩大，控制一下scope，降低我们的用时", HBase's 11 12 14 15 cut): the cases
    # that outgrew a 4-6 h budget (05 14400 s in DECIDE, 07 309 paths, 14 out of heap, 31 killed at round 26) -- no
    # client faults (their counterfactuals are state re-pairings, clocks and session loss; NONE names no transport of
    # doors.jsonl, so no door fails in the workload client's root contexts -- an empty list would fail every door
    # there, ClientFaults#read) and the first claim only; their exploration is capped as every case's
    # (workflow.properties explore_budget_s)
    export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
    client_fault_transports=(NONE)
    export CAUSYNTH_CAMPAIGN_MAX_CLAIMS=1
    ;;
  09|10|13|19|21|39|40)
    export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0 ;;
esac

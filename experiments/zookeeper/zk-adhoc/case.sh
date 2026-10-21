repo=${GC_TREES}/zookeeper-checks
row=$(awk -F'\t' -v id="${1:?usage: case.sh <NN>}" '$1 == id' "${here}/checks.tsv")
[[ -n "${row}" ]] || { echo "unknown ZooKeeper ad hoc check: $1" >&2; return 2; }
IFS=$'\t' read -r _ test_class test_method window target_occurrence classes <<<"${row}"
case "${window}" in
  up) ;;
  startup) recording_window=startup ;;
  *) echo "check $1: unknown window '${window}' (up: once the ensemble is up; startup: before it starts)" >&2; return 2 ;;
esac
read -r -a scope <<<"${classes}"
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
case "$1" in
  02)
    # scope cut (lead 2026-10-21): the mechanism is the session.owner re-pairing, so the workload client's ZOOKEEPER
    # doors do not fail -- a transport this client never calls, as HBase 07 (an empty list fails every client door)
    client_fault_transports=(ZK_QUORUM)
    ;;
esac

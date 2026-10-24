export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
export CAUSYNTH_REGION_PATH_MAX_TASKS=128
repo=${GC_TREES}/hadoop-hdfs-study-r7
if [[ "$1" == 21 ]]; then
  repo=${GC_TREES}/hadoop-hdfs-21
  loop_bounds=${here}/loop-bounds-21.jsonl
fi
row=$(awk -F'\t' -v id="${1:?usage: case.sh <NN>}" '$1 == id' "${here}/checks.tsv")
[[ -n "${row}" ]] || { echo "unknown HDFS ad hoc check: $1" >&2; return 2; }
IFS=$'\t' read -r _ test_class test_method window target_occurrence classes <<<"${row}"
if [[ "$1" == 07 ]]; then
  export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=6
fi
if [[ "$1" == 14 ]]; then
  export CAUSYNTH_REGION_PATH_MAX_TASKS=256
fi
if [[ "$1" == 24 || "$1" == 26 || "$1" == 37 ]]; then
  export CAUSYNTH_REPLAY_TIMEOUT_S=7200
fi
case "${window}" in
  up) ;;
  startup) recording_window=startup ;;
  *) echo "check $1: unknown window '${window}'" >&2; return 2 ;;
esac
[[ "${test_class##*.}" == TestCausynth* ]] || cluster_automatic=true
read -r -a scope <<<"${classes}"

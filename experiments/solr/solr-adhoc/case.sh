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
  05|07|09|10|13|14|19|21|31|39|40)
    export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0 ;;
esac

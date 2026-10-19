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

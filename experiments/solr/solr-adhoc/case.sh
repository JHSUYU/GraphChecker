# Ad-hoc coordination checks of Solr: a guarded throw a SolrCloud cluster
# test's healthy path evaluates and passes (tools/adhoc: sites.py,
# coverage.sh, reach.py; a sweep's are declared and chosen by their static
# slice by select.py, slice.sh and score.py).  A case is one check on one
# workload, "<check>.<TestClass>-<method>", or a batch of checks on one
# workload, "B<n>": a row "B<n><TAB><TestClass>-<method><TAB><check>..." of
# batches.tsv, whose target spec is targets/B<n>.yaml (tools/adhoc/
# prescreen.sh writes both).  checks.tsv declares each check, and the
# workload is any MiniSolrCloudCluster test of solr/core as it is written
# (CausynthSolrCluster's automatic cluster).  All run one tree, the one the
# file `tree` names, unedited: tools/adhoc/targets.py writes targets/, each
# check's class and throw line.  A sweep has no failure to name an
# occurrence by: the target is the first observed occurrence of the check in
# the campaign's own recording, unless occurrences.tsv names one.
if [[ "$1" =~ ^B[0-9]+$ ]]; then
  batch=$(awk -F'\t' -v b="$1" '$1 == b' "${here}/batches.tsv")
  [[ -n "${batch}" ]] || { echo "unknown batch: $1" >&2; return 2; }
  IFS=$'\t' read -r _ workload checks <<<"${batch}"
  target_spec=${here}/targets/$1.yaml
else
  checks=${1%%.*}
  workload=${1#*.}
  target_spec=${here}/targets/${checks}.yaml
fi
[[ -n "${checks}" && "${workload}" == *-* ]] || {
  echo "usage: case.sh <check>.<TestClass>-<method>|B<n>" >&2
  return 2
}
read -r repo <"${here}/tree"
target_occurrence=$(awk -F'\t' -v c="$1" '$1 == c {print $2}' \
  "${here}/occurrences.tsv")
target_occurrence=${target_occurrence:-first}
# The cluster state's family (system.sh) and each check's own class; the
# library doors' classes join the scope by themselves (ScopeGrowth --doors).
scope=("${solr_state_scope[@]}")
for check in ${checks}; do
  row=$(awk -F'\t' -v c="${check}" '$1 == c' "${here}/checks.tsv")
  [[ -n "${row}" ]] || { echo "unknown ad-hoc check: ${check}" >&2; return 2; }
  IFS=$'\t' read -r _ _ _ own _ <<<"${row}"
  scope+=("${own}")
done
test_method=${workload#*-}
test_class=$(cd "${repo}/solr/build/solr-core/classes/test" \
  && find . -name "${workload%%-*}.class" | sed 's#^\./##; s#\.class$##; s#/#.#g')
[[ -n "${test_class}" && "${test_class}" != *$'\n'* ]] || {
  echo "no single test class ${workload%%-*} in ${repo}" >&2
  return 2
}
# Every test of the module runs on one classpath, which any of its junit4
# reports states.
classpath_test=$(cd "${repo}/solr/build/solr-core/test" 2>/dev/null \
  && ls TEST-*.xml 2>/dev/null | sed -n '1{s/^TEST-//; s/\.xml$//; p}')

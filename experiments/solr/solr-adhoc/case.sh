# Ad-hoc coordination checks of Solr: a guarded throw a SolrCloud cluster
# test's healthy path evaluates and passes (tools/adhoc: sites.py,
# coverage.sh, reach.py; a sweep's are chosen by select.py).  One case per check and workload,
# "<check>.<TestClass>-<method>": checks.tsv declares each check, and the
# workload is any MiniSolrCloudCluster test of solr/core as it is written
# (CausynthSolrCluster's automatic cluster).  All run one tree;
# tools/adhoc/annotate.py annotates it and writes targets/.  A sweep has no
# failure to name an occurrence by: the target is the first observed
# occurrence of the check in the campaign's own recording, unless
# occurrences.tsv names one.
check=${1%%.*}
workload=${1#*.}
[[ -n "${check}" && "${workload}" != "$1" && "${workload}" == *-* ]] || {
  echo "usage: case.sh <check>.<TestClass>-<method>" >&2
  return 2
}
repo=/u/vnr3ne/lucene-solr-8_11-adhoc
row=$(awk -F'\t' -v c="${check}" '$1 == c' "${here}/checks.tsv")
[[ -n "${row}" ]] || { echo "unknown ad-hoc check: ${check}" >&2; return 2; }
IFS=$'\t' read -r _ _ _ own _ <<<"${row}"
target_spec=${here}/targets/${check}.yaml
target_occurrence=$(awk -F'\t' -v c="$1" '$1 == c {print $2}' \
  "${here}/occurrences.tsv" 2>/dev/null)
target_occurrence=${target_occurrence:-first}
scope=("${own}")
test_method=${workload#*-}
test_class=$(cd "${repo}/solr/build/solr-core/classes/test" \
  && find . -name "${workload%%-*}.class" | sed 's#^\./##; s#\.class$##; s#/#.#g')
[[ -n "${test_class}" && "${test_class}" != *$'\n'* ]] || {
  echo "no single test class ${workload%%-*} in ${repo}" >&2
  return 2
}
classpath_test=org.apache.solr.cloud.TestCausynthMigrateRuleTarget

# Solr ad hoc coordination checks: the Solr sites of the owner's static study
# (docs/checks/study.txt [SOLR-NN], docs/checks/SOLR.md part D.1) on the tree
# gc/solr-checks (the fork's graphchecker/solr-checks).  The tree marks each
# check's throw with @CausynthExceptionTarget("solr-adhoc-NN"); checks.tsv
# declares, per NN, the workload, where its window opens and the classes the
# analysis starts from.  Declarations only.
# A row is NN, test class, test method, window, target occurrence (`first`,
# or a selector), then the scope entries; no column is empty, since `read`
# takes a run of tabs as one separator.
#
# The workload is the cluster test the study names, as it is written, or,
# where that test cannot reach the check's guard inside the window, another
# test of the tree that does (19: AddReplicaTest never sets legacyCloud, so
# DeleteReplicaTest#deleteReplicaFromClusterStateLegacy, SOLR.md).  Every
# MiniSolrCloudCluster a test builds registers its nodes and opens the window
# by itself (CausynthSolrCluster, causynth.cluster.automatic), and so do the
# servers an AbstractFullDistribZkTestBase test builds (31: ForceLeaderTest).
# The window opens once the first cluster is up (`up`): the Solr adapter has
# no window before a cluster starts.
repo=${GC_TREES}/lucene-solr-checks
row=$(awk -F'\t' -v id="${1:?usage: case.sh <NN>}" '$1 == id' "${here}/checks.tsv")
[[ -n "${row}" ]] || { echo "unknown Solr ad hoc check: $1" >&2; return 2; }
IFS=$'\t' read -r _ test_class test_method window target_occurrence classes <<<"${row}"
case "${window}" in
  up) ;;
  *) echo "check $1: unknown window '${window}' (the Solr adapter opens its window once a cluster is up)" >&2; return 2 ;;
esac
read -r -a scope <<<"${classes}"
# 05's loop bounds (STATUS "Per-system surface"): SolrResourceLoader.inform's
# loop over a core's SolrInfoBeans runs past the 32-body work cap in the core
# creation its FORCE run forces.  No other check reads them.
if [[ "$1" == 05 ]]; then
  loop_bounds=${here}/loop-bounds-05.jsonl
fi

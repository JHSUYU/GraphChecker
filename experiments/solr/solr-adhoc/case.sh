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
# 05's loop bounds (STATUS "Per-system surface"): in the core creation it
# declares, SolrResourceLoader.inform's loop over a core's SolrInfoBeans runs
# past the 32-body work cap, and SolrCore.createInstances' loop over the
# standard search components past the default K_L.  No other check reads them.
if [[ "$1" == 05 ]]; then
  loop_bounds=${here}/loop-bounds-05.jsonl
fi
# 07's, 19's and 21's exploration bound (owner 2026-10-12: the redundant
# re-asks fixed first, then a named bound where the size is genuine): every
# admitted world re-asks the arms of the worlds before it, each another
# question, for its own path decides other kept conditions and its producers'
# paths other conditions (solr-adhoc-21 RX7, by round 19: 2612 asks from
# worlds of one flip, 184 of them new arms, from 119 admitted worlds;
# solr-adhoc-19 SC9 r13: 3722 asks over 1013 arms).  One nesting level: a
# flip in a world that already holds one is asked, one in a world of two
# flips is not, named BOUNDED (region_path_max_world_depth, campaign_bounds).
if [[ "$1" == 07 || "$1" == 19 || "$1" == 21 ]]; then
  export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=1
fi

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
# The study checks' exploration bound (owner 2026-10-12: every case ends in
# its budget -- fixed point, witness, or a declared named bound -- once the
# redundant re-asks are fixed).  What grows past a budget is the arms asked
# again in every world of one flip, each another question as the query is
# built (its own kept conditions, its handoffs' producer paths): of the
# asks cut from one-flip worlds 88-99 % were arms asked before (SC9-19 r13
# 590 new of 3722, SC10-09 r2-3 244 of 3539, SL1-40 r5 10 of 3661, SP5-13
# r7-8 29 of 2276, RX7-21 184 of 2612, RX8-21 r1-6 123 of 1214 in 24 min).
# Depth 0 -- a flip is asked from the seed's paths only, the flip's own
# replay its witness -- where that growth is measured or the case is of the
# routed-alias family, and each expected mechanism is one flip there (09 a
# TIMED_WAIT fault, 19 a pairing flip on a stale view, 40 a READ-door fault
# asked at round 0); depth 1 where the case forces its arm (05, 14: the
# forced world's arms) or one-flip worlds have not grown (31).  39 moved to
# depth 0 when its growth was measured (SGF3-adhoc-39, 2026-10-13: rounds 4-5
# planned 2522 and 3145 obligations over one-flip worlds, 7.72 ids per arm,
# the top arms asked in 59 worlds each; the 4 h budget ended it).  Named
# BOUNDED (region_path_max_world_depth, campaign_bounds); what stays
# unasked is every flip in a world of more flips than that.
case "$1" in
  07|09|10|13|19|21|39|40) export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0 ;;
  05|14|31) export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=1 ;;
esac

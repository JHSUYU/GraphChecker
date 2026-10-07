# HDFS ad hoc coordination checks: the HDFS sites of the owner's static
# study (GraphChecker branch `study`, study.txt [HDFS-NN]) on the one tree
# gc/hdfs-study.  The tree marks each check's throw with
# @CausynthExceptionTarget("hdfs-adhoc-NN"); checks.tsv declares, per NN, the
# workload, where its window opens and the classes the analysis starts from.
# Declarations only.
# A row is NN, test class, test method (m[k] for one invocation of a
# parameterized test or class, README "Run one case"), window, target
# occurrence (`first`, or a selector), then the scope entries; no column is
# empty, since `read` takes a run of tabs as one separator.
#
# The workload is the cluster test the study names, as it is written, or,
# where that test cannot reach the check's guard inside the window
# (hdfs.md part A), another test of the tree that does (47: an fsimage
# holding a striped file is loaded only after a saveNamespace).  One rule
# decides automatic mode: an upstream test runs in it -- every
# MiniDFSCluster or MiniJournalCluster it builds is registered and opens the
# window by itself (CausynthCluster#AUTOMATIC) -- and a fine-tuned workload
# of the tree's own (a TestCausynth* class, written against CausynthCluster:
# it registers its nodes and opens its window itself) runs without it (12:
# TestCausynthDataTransferRpcFailure with encryption off, since under
# encryption the SASL key check at :582 always fires before the token's).
#
# The window opens once the first cluster is up (`up`), or before it starts
# (`startup`, the owner's opt-in for a guard that runs only while a cluster
# starts: 21 the DataNode handshake, 27 a layout upgrade, 46 the format).
repo=/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r7
# hdfs-adhoc-21's per-case workarounds (STATUS): its tree (gc/hdfs-study-r7-21)
# runs the DataNode handshake on a thread of its own, so the handshake, which
# holds the guard, is an occurrence that ends rather than the prefix of the
# actor's service loop; and its loop bounds declare the version check's
# character loop.  No other check reads either.
if [[ "$1" == 21 ]]; then
  repo=/bigtemp/vnr3ne/wt/hadoop-hdfs-21
  loop_bounds=${here}/loop-bounds-21.jsonl
fi
row=$(awk -F'\t' -v id="${1:?usage: case.sh <NN>}" '$1 == id' "${here}/checks.tsv")
[[ -n "${row}" ]] || { echo "unknown HDFS ad hoc check: $1" >&2; return 2; }
IFS=$'\t' read -r _ test_class test_method window target_occurrence classes <<<"${row}"
# 07's workarounds (owner 2026-10-06, STATUS "Per-system surface"): its tree
# r8 is r7 plus QJM reading the journal nodes' replies in its loggers' order
# (a HashMap keyed by identity hash read them in another order every JVM,
# STATUS defect 57), and its fault combinations nest past the default world
# depth of 3 (CC7: 181, 281, 62 and 15 sessions in worlds of 1-4 flips; each
# depth cut from makes the next one's paths, so 6, not 4).
if [[ "$1" == 07 ]]; then
  repo=/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r8
  export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=6
fi
case "${window}" in
  up) ;;
  startup) recording_window=startup ;;
  *) echo "check $1: unknown window '${window}'" >&2; return 2 ;;
esac
[[ "${test_class##*.}" == TestCausynth* ]] || cluster_automatic=true
read -r -a scope <<<"${classes}"

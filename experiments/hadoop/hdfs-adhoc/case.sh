# HDFS ad hoc coordination checks: the HDFS sites of the owner's static
# study (GraphChecker branch `study`, study.txt [HDFS-NN]) on the one tree
# gc/hdfs-study.  The tree marks each check's throw with
# @CausynthExceptionTarget("hdfs-adhoc-NN"); checks.tsv declares, per NN, the
# workload, where its window opens and the classes the analysis starts from.
# Declarations only.
# A row is NN, test class, test method, window, target occurrence (`first`,
# or a selector), then the scope entries; no column is empty, since `read`
# takes a run of tabs as one separator.
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
repo=/bigtemp/vnr3ne/wt/hadoop-hdfs-study
row=$(awk -F'\t' -v id="${1:?usage: case.sh <NN>}" '$1 == id' "${here}/checks.tsv")
[[ -n "${row}" ]] || { echo "unknown HDFS ad hoc check: $1" >&2; return 2; }
IFS=$'\t' read -r _ test_class test_method window target_occurrence classes <<<"${row}"
case "${window}" in
  up) ;;
  startup) recording_window=startup ;;
  *) echo "check $1: unknown window '${window}'" >&2; return 2 ;;
esac
[[ "${test_class##*.}" == TestCausynth* ]] || cluster_automatic=true
read -r -a scope <<<"${classes}"

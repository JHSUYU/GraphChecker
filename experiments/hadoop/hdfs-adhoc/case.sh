# HDFS ad hoc coordination checks: the HDFS sites of the owner's static
# study (GraphChecker branch `study`, study.txt [HDFS-NN]), each run on the
# cluster test the study names, as that test is written, on the one tree
# gc/hdfs-study.  The tree marks each check's throw with
# @CausynthExceptionTarget("hdfs-adhoc-NN"); checks.tsv declares, per NN, the
# workload and the classes the analysis starts from.  Declarations only.
# A row is NN, test class, test method, target occurrence (`first`, or a
# selector), then the scope entries; no column is empty, since `read`
# takes a run of tabs as one separator.
repo=/bigtemp/vnr3ne/wt/hadoop-hdfs-study
row=$(awk -F'\t' -v id="${1:?usage: case.sh <NN>}" '$1 == id' "${here}/checks.tsv")
[[ -n "${row}" ]] || { echo "unknown HDFS ad hoc check: $1" >&2; return 2; }
IFS=$'\t' read -r _ test_class test_method target_occurrence classes <<<"${row}"
# Every MiniDFSCluster the test builds is registered and opens the window
# by itself (CausynthCluster#AUTOMATIC).
cluster_automatic=true
read -r -a scope <<<"${classes}"

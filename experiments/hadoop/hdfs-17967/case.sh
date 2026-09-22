#!/usr/bin/env bash

case_id=${1:?usage: case.sh pathA}
loop_bounds=${here}/loop-bounds.jsonl
# Which occurrence of the annotated site this case is about.  HDFS-17967's
# three paths share one annotatable site -- the client-side reconstruction of
# the peer's ERROR_UNKNOWN_KEY frame in DataTransferSaslUtil, because the two
# DataXceiver paths both end in a RETHROW that @CausynthExceptionTarget
# (@Target(TYPE_USE)) cannot sit on -- so they are told apart HERE, by the
# occurrence, exactly as hdfs-17899's three bugs are.
#
# Left empty until a seed recording exists: the address carries a REGION.<uuid>
# the engine mints, so it cannot be written before the first run, and an empty
# value is a hard refusal rather than a fallback.
target_occurrence=
case "${case_id}" in
  pathA)
    repo=/u/vnr3ne/hadoop-hdfs-17967
    test_class=org.apache.hadoop.hdfs.server.datanode.TestCausynthWriteBlockMirrorStaleKey
    test_method=testWritePipelineAfterKeyRotations
    ;;
  *)
    echo "unknown HDFS-17967 case: ${case_id}" >&2
    return 2
    ;;
esac

module=${repo}/hadoop-hdfs-project/hadoop-hdfs
report=${module}/target/surefire-reports/TEST-${test_class}.xml
analysis=/tmp/graphchecker-hdfs-17967-${case_id}-classes
test_name=${test_class}#${test_method}

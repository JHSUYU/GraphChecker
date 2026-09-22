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
    # The mirror DataNode's SASL callback handler, the region every passing
    # case in this family anchors on, under the client's write-block request.
    # The node form carries no @anchor part on purpose: it matches on node and
    # region, and #1 takes the first the recording published.  Both DataNodes
    # serve a handshake here -- the head for the client, the mirror for the
    # head -- and they are identical in shape, so the first is taken.
    target_occurrence="hdfs-17967/dn1#epoch0/region/REGION.7c569c3f-b4d3-305a-bd9c-bebff1048122#1"
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

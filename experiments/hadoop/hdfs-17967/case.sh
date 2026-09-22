#!/usr/bin/env bash

case_id=${1:?usage: case.sh pathA|pathB|pathC}
loop_bounds=${here}/loop-bounds.jsonl
# All three paths share ONE annotated site, the allKeys miss in
# BlockTokenSecretManager.retrieveDataEncryptionKey, and are told apart by
# their target occurrence.  Path C's own throw -- StripedWriter's
# "All targets are failed." -- looks like the better site because it is where
# the failure surfaces, but its only operand is a String, so nothing then
# classifies the key-management methods as writers of tracked state and the
# recording is refused outright ("region skeleton has no authoritative
# execution context root").  Measured 2026-09-22.
target_spec=${here}/target.yaml
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
    # case in this family anchors on.  The workload drives the pipeline from a
    # third DataNode (source -> head -> mirror) with NO client in the recorded
    # window, so exactly ONE handshake is served here: the head's, by the
    # mirror, and the mirror is the party that cannot resolve the head's key.
    # The node form carries no @anchor part on purpose: it matches on node and
    # region, and #1 takes the first the recording published.
    target_occurrence="hdfs-17967/mirror-dn#epoch0/region/REGION.7c569c3f-b4d3-305a-bd9c-bebff1048122#1"
    ;;
  pathB)
    repo=/u/vnr3ne/hadoop-hdfs-17967-b
    test_class=org.apache.hadoop.hdfs.server.datanode.TestCausynthReplaceBlockProxyStaleKey
    test_method=testBlockMoveAfterKeyRotations
    # The PROXY DataNode's SASL callback handler.  A REPLACE_BLOCK move is two
    # handshakes -- mover to target, then target to proxy -- and only the
    # second is this case: the mover holds the master's current key, so its
    # own hop cannot fail, and the proxy is the party that has to resolve the
    # target's rolled-back key.
    target_occurrence="hdfs-17967/proxy-dn#epoch0/region/REGION.7c569c3f-b4d3-305a-bd9c-bebff1048122#1"
    ;;
  pathC)
    repo=/u/vnr3ne/hadoop-hdfs-17967-c
    test_class=org.apache.hadoop.hdfs.server.datanode.TestCausynthStripedReconstructTargetStaleKey
    test_method=testReconstructionAfterKeyRotations
    # The reconstruction TARGET's SASL callback handler: the reconstructing
    # node opens the connection as a client and the target is the party that
    # has to resolve its rolled-back key.  The node that still holds the lost
    # index takes no part, and the helper only serves a source read.
    target_occurrence="hdfs-17967/target-dn#epoch0/region/REGION.7c569c3f-b4d3-305a-bd9c-bebff1048122#1"
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

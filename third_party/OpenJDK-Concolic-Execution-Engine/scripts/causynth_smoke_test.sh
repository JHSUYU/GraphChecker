#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
JDK_ROOT=$(cd "$SCRIPT_DIR/.." && pwd)
CONF=${CONF:-linux-x86_64-normal-zero-release}
JDK_HOME=${JDK_HOME:-"$JDK_ROOT/build/$CONF/images/j2sdk-image"}
OUT=${OUT:-"$JDK_ROOT/build/causynth-smoke"}

mkdir -p "$OUT"
cd "$JDK_ROOT"
"$JDK_HOME/bin/javac" -XDignore.symbol.file=true \
  -bootclasspath "$JDK_HOME/jre/lib/rt.jar:$JDK_HOME/jre/lib/jce.jar" \
  -d "$OUT" \
  test/causynth/RegionApiSmoke.java \
  test/causynth/RegionAtomicApiSmoke.java \
  test/causynth/RegionBoxedPrimitiveApiSmoke.java \
  test/causynth/RegionContainerRelationApiSmoke.java \
  test/causynth/RegionBranchEventApiSmoke.java \
  test/causynth/RegionFieldApiSmoke.java \
  test/causynth/RegionGuardedConcreteWriteSmoke.java \
  test/causynth/RegionViewRemovalSmoke.java \
  test/causynth/RegionFieldExpressionApiSmoke.java \
  test/causynth/RegionPropagatedFieldGuardSmoke.java \
  test/causynth/RegionExpressionHandoffApiSmoke.java \
  test/causynth/RegionLeafBrokerSmoke.java \
  test/causynth/RegionContainerLiveInApiSmoke.java \
  test/causynth/RegionIndexedCarrierApiSmoke.java \
  test/causynth/RegionUnshadowedStringArgumentSmoke.java \
  test/causynth/RegionDeepExpressionSerializeSmoke.java \
  test/causynth/RegionMapApiSmoke.java \
  test/causynth/RegionMapReadOnlyApiSmoke.java \
  test/causynth/RegionListAbandonApiSmoke.java \
  test/causynth/RegionMapIteratorRemoveApiSmoke.java \
  test/causynth/RegionMapValuesToObjectArrayApiSmoke.java \
  test/causynth/RegionNumericLoopApiSmoke.java \
  test/causynth/RegionNumericSemanticsApiSmoke.java \
  test/causynth/RegionObjectArrayMapApiSmoke.java \
  test/causynth/RegionPausedSymbolizationSmoke.java \
  test/causynth/RegionLookupSwitchApiSmoke.java \
  test/causynth/org/slf4j/helpers/CausynthObservationProbe.java \
  test/causynth/RegionLoggingObservationSmoke.java \
  test/causynth/RegionOneWayFunctionSmoke.java \
  test/causynth/RegionSymbolicIndexScanSmoke.java \
  test/causynth/RegionWrittenArrayScanSmoke.java \
  test/causynth/RegionUnattributedWriterSmoke.java \
  test/causynth/RegionLoadedValueSmoke.java \
  test/causynth/RegionMethodReturnValueSmoke.java \
  test/causynth/RegionReferenceBranchApiSmoke.java \
  test/causynth/RegionRepeatedFieldOwnerMapApiSmoke.java \
  test/causynth/RegionShadowStackLifecycleSmoke.java \
  test/causynth/RegionSymbolicKeySourceSmoke.java \
  test/causynth/RegionSharedReadFromSmoke.java \
  test/causynth/RegionObservedConcreteWriteSmoke.java \
  test/causynth/RegionEventSiteSmoke.java \
  test/causynth/RegionReferenceFieldStatedReadSmoke.java \
  test/causynth/RegionExactMintOverCarrierWriteSmoke.java \
  test/causynth/RegionStringContainsApiSmoke.java \
  test/causynth/RegionStringConversionApiSmoke.java \
  test/causynth/RegionStringSplitParseMapApiSmoke.java \
  test/causynth/RegionTableSwitchApiSmoke.java \
  test/causynth/RegionPathConditionTruncationSmoke.java \
  test/causynth/RegionConditionalRemovalApiSmoke.java \
  test/causynth/RegionArrayCopySmoke.java \
  test/causynth/RegionCloneSmoke.java \
  test/causynth/RegionUnsafeWriteSmoke.java \
  test/causynth/RegionSharedBoxSmoke.java \
  test/causynth/RegionTrackedRaceSmoke.java \
  test/causynth/RegionReadExactnessSmoke.java \
  test/causynth/RegionWrapperFieldSmoke.java \
  test/causynth/RegionStringBuilderMutatorSmoke.java \
  test/causynth/RegionVersionDefectsSmoke.java \
  test/causynth/RegionReferenceSwapSmoke.java \
  test/causynth/RegionConcurrentHashMapSmoke.java \
  test/causynth/RegionMapIterationOrderSmoke.java \
  test/causynth/RegionWrapperViewSmoke.java \
  test/causynth/RegionAtomicCarrierSmoke.java \
  test/causynth/RegionRedefineOnStackSmoke.java

for smoke in \
  RegionApiSmoke \
  RegionAtomicApiSmoke \
  RegionBoxedPrimitiveApiSmoke \
  RegionContainerRelationApiSmoke \
  RegionBranchEventApiSmoke \
  RegionFieldApiSmoke \
  RegionGuardedConcreteWriteSmoke \
  RegionViewRemovalSmoke \
  RegionFieldExpressionApiSmoke \
  RegionPropagatedFieldGuardSmoke \
  RegionExpressionHandoffApiSmoke \
  RegionLeafBrokerSmoke \
  RegionContainerLiveInApiSmoke \
  RegionIndexedCarrierApiSmoke \
  RegionUnshadowedStringArgumentSmoke \
  RegionDeepExpressionSerializeSmoke \
  RegionMapApiSmoke \
  RegionMapReadOnlyApiSmoke \
  RegionListAbandonApiSmoke \
  RegionMapIteratorRemoveApiSmoke \
  RegionConditionalRemovalApiSmoke \
  RegionMapValuesToObjectArrayApiSmoke \
  RegionNumericLoopApiSmoke \
  RegionNumericSemanticsApiSmoke \
  RegionObjectArrayMapApiSmoke \
  RegionPausedSymbolizationSmoke \
  RegionLookupSwitchApiSmoke \
  RegionLoggingObservationSmoke \
  RegionOneWayFunctionSmoke \
  RegionSymbolicIndexScanSmoke \
  RegionWrittenArrayScanSmoke \
  RegionUnattributedWriterSmoke \
  RegionLoadedValueSmoke \
  RegionMethodReturnValueSmoke \
  RegionReferenceBranchApiSmoke \
  RegionRepeatedFieldOwnerMapApiSmoke \
  RegionShadowStackLifecycleSmoke \
  RegionSymbolicKeySourceSmoke \
  RegionSharedReadFromSmoke \
  RegionObservedConcreteWriteSmoke \
  RegionEventSiteSmoke \
  RegionReferenceFieldStatedReadSmoke \
  RegionExactMintOverCarrierWriteSmoke \
  RegionStringContainsApiSmoke \
  RegionStringConversionApiSmoke \
  RegionStringSplitParseMapApiSmoke \
  RegionTableSwitchApiSmoke \
  RegionArrayCopySmoke \
  RegionCloneSmoke \
  RegionUnsafeWriteSmoke \
  RegionSharedBoxSmoke \
  RegionTrackedRaceSmoke \
  RegionReadExactnessSmoke \
  RegionWrapperFieldSmoke \
  RegionStringBuilderMutatorSmoke \
  RegionVersionDefectsSmoke \
  RegionReferenceSwapSmoke \
  RegionConcurrentHashMapSmoke \
  RegionMapIterationOrderSmoke \
  RegionWrapperViewSmoke \
  RegionAtomicCarrierSmoke \
  RegionRedefineOnStackSmoke; do
  "$JDK_HOME/bin/java" -Xint -cp "$OUT" "$smoke"
done

# The path-condition serializer's byte bound, on all three of its arms.  The
# shipped bound is 256 MB, so the truncation path is unreachable from a smoke
# unless the bound is lowered for the run -- which is the whole reason it is a
# property.  Each arm asserts that `conditions` is exactly as long as the
# `conditionCount` beside it, which is what the bound used to break.
#   (unset) nothing truncates and the 240 conditions come back whole
#   0       nothing fits, so every index is a named marker
#   8192    a prefix of references, then a marker for every remaining index
"$JDK_HOME/bin/java" -Xint -cp "$OUT" RegionPathConditionTruncationSmoke
"$JDK_HOME/bin/java" -Xint -Dcausynth.vm.pathcondition.bytes=0 \
  -cp "$OUT" RegionPathConditionTruncationSmoke
"$JDK_HOME/bin/java" -Xint -Dcausynth.vm.pathcondition.bytes=8192 \
  -cp "$OUT" RegionPathConditionTruncationSmoke

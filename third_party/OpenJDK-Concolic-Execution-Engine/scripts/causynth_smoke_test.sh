#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
JDK_ROOT=$(cd "$SCRIPT_DIR/.." && pwd)
CONF=${CONF:-linux-x86_64-normal-zero-release}
JDK_HOME=${JDK_HOME:-"$JDK_ROOT/build/$CONF/images/j2sdk-image"}
OUT=${OUT:-"$JDK_ROOT/build/causynth-smoke"}

mkdir -p "$OUT"
cd "$JDK_ROOT"
"$JDK_HOME/bin/javac" -d "$OUT" \
  test/causynth/RegionApiSmoke.java \
  test/causynth/RegionAtomicApiSmoke.java \
  test/causynth/RegionBoxedPrimitiveApiSmoke.java \
  test/causynth/RegionContainerRelationApiSmoke.java \
  test/causynth/RegionBranchEventApiSmoke.java \
  test/causynth/RegionFieldApiSmoke.java \
  test/causynth/RegionFieldExpressionApiSmoke.java \
  test/causynth/RegionContainerLiveInApiSmoke.java \
  test/causynth/RegionMapApiSmoke.java \
  test/causynth/RegionMapIteratorRemoveApiSmoke.java \
  test/causynth/RegionMapValuesToObjectArrayApiSmoke.java \
  test/causynth/RegionNumericLoopApiSmoke.java \
  test/causynth/RegionNumericSemanticsApiSmoke.java \
  test/causynth/RegionObjectArrayMapApiSmoke.java \
  test/causynth/RegionOutputContainerSnapshotApiSmoke.java \
  test/causynth/RegionPausedSymbolizationSmoke.java \
  test/causynth/RegionLookupSwitchApiSmoke.java \
  test/causynth/RegionReferenceBranchApiSmoke.java \
  test/causynth/RegionRepeatedFieldOwnerMapApiSmoke.java \
  test/causynth/RegionShadowStackLifecycleSmoke.java \
  test/causynth/RegionStringContainsApiSmoke.java \
  test/causynth/RegionStringConversionApiSmoke.java \
  test/causynth/RegionStringSplitParseMapApiSmoke.java \
  test/causynth/RegionTableSwitchApiSmoke.java \
  test/causynth/RegionThreadIsolationSmoke.java

for smoke in \
  RegionApiSmoke \
  RegionAtomicApiSmoke \
  RegionBoxedPrimitiveApiSmoke \
  RegionContainerRelationApiSmoke \
  RegionBranchEventApiSmoke \
  RegionFieldApiSmoke \
  RegionFieldExpressionApiSmoke \
  RegionContainerLiveInApiSmoke \
  RegionMapApiSmoke \
  RegionMapIteratorRemoveApiSmoke \
  RegionMapValuesToObjectArrayApiSmoke \
  RegionNumericLoopApiSmoke \
  RegionNumericSemanticsApiSmoke \
  RegionObjectArrayMapApiSmoke \
  RegionOutputContainerSnapshotApiSmoke \
  RegionPausedSymbolizationSmoke \
  RegionLookupSwitchApiSmoke \
  RegionReferenceBranchApiSmoke \
  RegionRepeatedFieldOwnerMapApiSmoke \
  RegionShadowStackLifecycleSmoke \
  RegionStringContainsApiSmoke \
  RegionStringConversionApiSmoke \
  RegionStringSplitParseMapApiSmoke \
  RegionTableSwitchApiSmoke \
  RegionThreadIsolationSmoke; do
  "$JDK_HOME/bin/java" -Xint -cp "$OUT" "$smoke"
done

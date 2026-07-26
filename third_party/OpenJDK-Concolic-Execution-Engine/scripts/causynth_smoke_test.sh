#!/usr/bin/env bash
set -euo pipefail

CONF=${CONF:-linux-x86_64-normal-zero-release}
JDK_HOME=${JDK_HOME:-"$PWD/build/$CONF/images/j2sdk-image"}
OUT=${OUT:-"$PWD/build/causynth-smoke"}

mkdir -p "$OUT"
"$JDK_HOME/bin/javac" -d "$OUT" \
  test/causynth/RegionApiSmoke.java \
  test/causynth/RegionContainerRelationApiSmoke.java \
  test/causynth/RegionBranchEventApiSmoke.java \
  test/causynth/RegionFieldApiSmoke.java \
  test/causynth/RegionMapApiSmoke.java \
  test/causynth/RegionMapIteratorRemoveApiSmoke.java \
  test/causynth/RegionNumericLoopApiSmoke.java \
  test/causynth/RegionNumericSemanticsApiSmoke.java \
  test/causynth/RegionObjectArrayMapApiSmoke.java \
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
  RegionContainerRelationApiSmoke \
  RegionBranchEventApiSmoke \
  RegionFieldApiSmoke \
  RegionMapApiSmoke \
  RegionMapIteratorRemoveApiSmoke \
  RegionNumericLoopApiSmoke \
  RegionNumericSemanticsApiSmoke \
  RegionObjectArrayMapApiSmoke \
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

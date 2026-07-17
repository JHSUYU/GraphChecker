#!/usr/bin/env bash
set -euo pipefail

CONF=${CONF:-linux-x86_64-normal-zero-release}
JDK_HOME=${JDK_HOME:-"$PWD/build/$CONF/images/j2sdk-image"}
OUT=${OUT:-"$PWD/build/causynth-smoke"}

mkdir -p "$OUT"
"$JDK_HOME/bin/javac" -d "$OUT" \
  test/causynth/RegionApiSmoke.java \
  test/causynth/RegionArrayCopyExceptionApiSmoke.java \
  test/causynth/RegionArrayValueApiSmoke.java \
  test/causynth/RegionArrayValueMapProjectionApiSmoke.java \
  test/causynth/RegionBranchEventApiSmoke.java \
  test/causynth/RegionFieldApiSmoke.java \
  test/causynth/RegionMapApiSmoke.java \
  test/causynth/RegionMapIteratorRemoveApiSmoke.java \
  test/causynth/RegionObjectArrayMapApiSmoke.java \
  test/causynth/RegionPausedSymbolizationSmoke.java \
  test/causynth/RegionStringConversionApiSmoke.java \
  test/causynth/RegionStringSplitParseMapApiSmoke.java \
  test/causynth/RegionThreadIsolationSmoke.java

for smoke in \
  RegionApiSmoke \
  RegionArrayCopyExceptionApiSmoke \
  RegionArrayValueApiSmoke \
  RegionArrayValueMapProjectionApiSmoke \
  RegionBranchEventApiSmoke \
  RegionFieldApiSmoke \
  RegionMapApiSmoke \
  RegionMapIteratorRemoveApiSmoke \
  RegionObjectArrayMapApiSmoke \
  RegionPausedSymbolizationSmoke \
  RegionStringConversionApiSmoke \
  RegionStringSplitParseMapApiSmoke \
  RegionThreadIsolationSmoke; do
  "$JDK_HOME/bin/java" -Xint -cp "$OUT" "$smoke"
done

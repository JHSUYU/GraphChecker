#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
base_file=${HBASE_JDK8_CLASSPATH_FILE:-/tmp/graphchecker-hbase-jdk8-pressure/run.20260919T151441Z.xBtxIn/classpath.txt}
[[ -s "$base_file" ]] || {
  printf 'missing Java 8 HBase classpath: %s\n' "$base_file" >&2
  exit 2
}
base=$(cat "$base_file")
printf '%s:%s:%s\n' "$here/overlay/production-classes" \
  "$here/overlay/test-classes" "$base"

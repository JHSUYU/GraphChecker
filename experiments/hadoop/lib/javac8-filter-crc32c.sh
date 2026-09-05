#!/usr/bin/env bash
set -euo pipefail

real_javac=${CAUSYNTH_REAL_JAVAC:-/usr/lib/jvm/java-8-openjdk-amd64/bin/javac}
excluded=src/test/java/org/apache/hadoop/util/TestPureJavaCrc32C.java
forward=()
temporary_files=()

cleanup() {
  ((${#temporary_files[@]} == 0)) || rm -f -- "${temporary_files[@]}"
}
trap cleanup EXIT

for argument in "$@"; do
  if [[ ${argument} == @* ]]; then
    input=${argument#@}
    output=$(mktemp "${TMPDIR:-/tmp}/causynth-javac8.XXXXXX.args")
    temporary_files+=("${output}")
    awk -v suffix="${excluded}" '
      {
        raw = $0
        value = raw
        sub(/^"/, "", value)
        sub(/"$/, "", value)
        if (length(value) >= length(suffix) &&
            substr(value, length(value) - length(suffix) + 1) == suffix) {
          next
        }
        print raw
      }
    ' "${input}" >"${output}"
    forward+=("@${output}")
  elif [[ ${argument} == *"${excluded}" ]]; then
    continue
  else
    forward+=("${argument}")
  fi
done

"${real_javac}" "${forward[@]}"

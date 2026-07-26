#!/usr/bin/env bash

set -euo pipefail

fixture_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker_dir=$(cd "${fixture_dir}/../../.." && pwd -P)
round=${1:-}
generated_parent="${graphchecker_dir}/target/generated-regression"
generated_root="${generated_parent}/current"
generator="${fixture_dir}/generate_regression_round.py"

die() {
  echo "[generated-rpc] $*" >&2
  exit 1
}

[[ "${round}" =~ ^([1-9]|10)$ ]] || die "round must be 1..10"
[[ -f "${generator}" ]] || die "generator not found: ${generator}"
command -v python3 >/dev/null 2>&1 || die "python3 is required"
command -v javac >/dev/null 2>&1 || die "javac is required"
command -v mvn >/dev/null 2>&1 || die "mvn is required"

mkdir -p "${generated_parent}"
[[ "$(realpath -m -- "${generated_root}")" \
    == "$(realpath -m -- "${graphchecker_dir}/target")/"* ]] \
  || die "refusing unsafe generated root: ${generated_root}"
if [[ -d "${generated_root}" ]]; then
  find "${generated_root}" -mindepth 1 -delete
  rmdir "${generated_root}"
elif [[ -e "${generated_root}" ]]; then
  die "generated root is not a directory: ${generated_root}"
fi

cd "${graphchecker_dir}"
mvn -q -DskipTests package
python3 "${generator}" "${round}" \
  "target/generated-regression/current"
mkdir -p "${generated_root}/classes"
mapfile -t sources < <(find "${generated_root}/src" -type f \
  -name '*.java' | LC_ALL=C sort)
[[ ${#sources[@]} -eq 13 ]] \
  || die "generator emitted ${#sources[@]} sources instead of 13"
javac -source 8 -target 8 -Xlint:-options \
  -cp "${graphchecker_dir}/target/classes" \
  -d "${generated_root}/classes" "${sources[@]}"
jq -e --argjson round "${round}" '
  .schemaVersion == 1
  and .kind == "GENERATED_RPC_REGRESSION_ROUND"
  and .round == $round
  and (.cases | length) == 13
  and ([.cases[] | select(.expected == "REACHABLE")] | length) == 6
  and ([.cases[] | select(.expected == "UNREACHABLE")] | length) == 7
' "${generated_root}/manifest.json" >/dev/null \
  || die "generated manifest is invalid"
while IFS=$'\t' read -r class expected; do
  reached=false
  for left in false true; do
    for right in false true; do
      log="${generated_root}/oracle-${class##*.}-${left}-${right}.log"
      if java -cp "${generated_root}/classes:${graphchecker_dir}/target/classes" \
          "${class}" "${left}" "${right}" >"${log}" 2>&1; then
        :
      elif grep -q 'GeneratedBugReachedException' "${log}"; then
        reached=true
      else
        die "ordinary JVM oracle failed for ${class} ${left} ${right}; inspect ${log}"
      fi
    done
  done
  [[ "${expected}" == "REACHABLE" && "${reached}" == "true" \
      || "${expected}" == "UNREACHABLE" && "${reached}" == "false" ]] \
    || die "ordinary JVM oracle disagrees with ${expected} for ${class}"
done < <(jq -r '.cases[] | [.class, .expected] | @tsv' \
  "${generated_root}/manifest.json")
echo "[generated-rpc] round=${round} sources=13 root=${generated_root}"

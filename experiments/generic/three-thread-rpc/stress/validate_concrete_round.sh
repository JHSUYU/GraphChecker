#!/usr/bin/env bash

set -uo pipefail

stress_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker_dir=$(cd "${stress_dir}/../../../.." && pwd -P)
manifest="${stress_dir}/manifest.tsv"
classpath="${graphchecker_dir}/target/test-classes:${graphchecker_dir}/target/classes"

[[ -f "${manifest}" ]] || {
  echo "[stress-concrete] missing manifest" >&2
  exit 1
}

failures=0
checked=0
while IFS=$'\t' read -r case_number class_name _target expectation \
    _producer_a _producer_b _consumer; do
  [[ "${case_number}" =~ ^[0-9][0-9]$ ]] || continue
  reached=0
  seed_reached=false
  for input_a in false true; do
    for input_b in false true; do
      log=$(mktemp)
      java -cp "${classpath}" \
        "edu.uva.liftlab.graphchecker.fixtures.stress.${class_name}" \
        "${input_a}" "${input_b}" >"${log}" 2>&1
      status=$?
      if grep -q 'TargetReachedException' "${log}"; then
        reached=$((reached + 1))
        [[ "${input_a}:${input_b}" == "false:false" ]] \
          && seed_reached=true
      elif [[ ${status} -ne 0 ]]; then
        echo "[stress-concrete] case=${case_number} crashed for" \
          "${input_a},${input_b}: $(tail -1 "${log}")" >&2
        failures=$((failures + 1))
      fi
      rm -f "${log}"
    done
  done
  expected_reached=false
  [[ "${expectation}" == "SAT" ]] && expected_reached=true
  actual_reached=false
  (( reached > 0 )) && actual_reached=true
  if [[ "${seed_reached}" == "true"
        || "${actual_reached}" != "${expected_reached}" ]]; then
    echo "[stress-concrete] case=${case_number} expected=${expectation}" \
      "reached=${reached} seedReached=${seed_reached}" >&2
    failures=$((failures + 1))
  fi
  checked=$((checked + 1))
done <"${manifest}"

echo "[stress-concrete] checked=${checked} failures=${failures}"
[[ ${checked} -eq 20 && ${failures} -eq 0 ]]

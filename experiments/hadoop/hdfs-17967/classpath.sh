#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
source "${here}/case.sh" "${1:?missing case}"
[[ -f "${report}" ]] || {
  echo "missing test report: ${report}; run build first" >&2
  exit 2
}
exec python3 "${here}/../lib/classpath.py" "${repo}" "${report}"

#!/usr/bin/env bash
# classpath.sh <case-dir> <case-id> -- the workload's classpath, read off the
# case's own surefire report and keeping Hadoop classes in its own checkout.
set -euo pipefail
lib=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
source "${lib}/case-env.sh" "${1:?missing case directory}" "${2-}"
[[ -f "${report}" ]] || {
  echo "missing test report: ${report}; run build first" >&2
  exit 2
}
exec python3 "${lib}/classpath.py" "${repo}" "${report}"

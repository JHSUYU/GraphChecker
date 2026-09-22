#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
source "${here}/case.sh" "${1:?missing case}"
exec bash "${here}/../lib/build.sh" "${repo}" "${test_class}" "${test_method}"

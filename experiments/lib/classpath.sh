#!/usr/bin/env bash
# classpath.sh <case-dir> <case-id> -- the workload's classpath, as the
# case's system states it (system_classpath).
set -euo pipefail
lib=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
source "${lib}/case-env.sh" "${1:?missing case directory}" "${2-}"
system_classpath

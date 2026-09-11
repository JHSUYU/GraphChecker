#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
command=${1:?usage: run.sh build|config|validate|campaign}
shift
if [[ "${command}" == build ]]; then
  exec "${here}/build.sh" "$@"
fi

export CAUSYNTH_CLASSPATH
CAUSYNTH_CLASSPATH=$("${here}/classpath.sh")
export CAUSYNTH_WORKLOAD_COMMAND="${here}/execute.sh" CAUSYNTH_CONCOLIC_REPLAY_COMMAND="${here}/execute.sh" CAUSYNTH_CAMPAIGN_SETUP_COMMAND="${here}/prepare-analysis.sh"
exec "${here}/../../../run_engine.sh" --config "${here}/workflow.properties" \
  "${command}" "$@"

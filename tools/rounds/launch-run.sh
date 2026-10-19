#!/usr/bin/env bash
set -uo pipefail
# shellcheck source=../lib/gc-env.sh
source "$(dirname "${BASH_SOURCE[0]}")/../lib/gc-env.sh"
: "${CAUSYNTH_CUSTOM_JDK_HOME:?launch-run.sh: name the concolic VM image as CAUSYNTH_CUSTOM_JDK_HOME}"
export PATH=/usr/lib/maven/bin:$PATH
export SKIP_BUILD=1
export JAR="$1/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar"
export CASES="$2"
export OUT=${GC_OUT}/accept-"$3"
export CAUSYNTH_CUSTOM_JDK_HOME
export CAUSYNTH_CAMPAIGN_WORKER_HOSTS="${CAUSYNTH_CAMPAIGN_WORKER_HOSTS:-${LIFTS}}"
exec bash "$1"/experiments/accept/accept.sh

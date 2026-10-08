#!/usr/bin/env bash
# launch-run.sh <repo> <case-id> <out-suffix> -- one acceptance run from a
# GraphChecker snapshot worktree (its own jar, accept.sh, case dirs), on the
# concolic VM image CAUSYNTH_CUSTOM_JDK_HOME names: a launch must name it
# (docs/handover/OPERATIONS.md §1 lists the images), there is no default.
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
# Its obligations go to every host in LIFTS, as a round's do (launch-round.sh):
# a run left to its head alone replayed two or three at a time (W6C2-W6C4).
export CAUSYNTH_CAMPAIGN_WORKER_HOSTS="${CAUSYNTH_CAMPAIGN_WORKER_HOSTS:-${LIFTS}}"
exec bash "$1"/experiments/accept/accept.sh

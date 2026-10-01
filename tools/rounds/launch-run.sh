#!/usr/bin/env bash
# launch-run.sh <repo> <case-id> <out-suffix> -- one acceptance run from a
# GraphChecker snapshot worktree (its own jar, accept.sh, case dirs), on the
# concolic VM image CAUSYNTH_CUSTOM_JDK_HOME names: a launch must name it
# (README §3.1 lists the images), there is no default.
set -uo pipefail
# shellcheck source=../lib/gc-env.sh
source "$(dirname "${BASH_SOURCE[0]}")/../lib/gc-env.sh"
: "${CAUSYNTH_CUSTOM_JDK_HOME:?launch-run.sh: name the concolic VM image as CAUSYNTH_CUSTOM_JDK_HOME}"
export PATH=/usr/lib/maven/bin:$PATH
export SKIP_BUILD=1
export JAR="$1/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar"
export CASES="$2"
export OUT=${GC_OUT}/accept-"$3"
export Z3_BIN=/u/vnr3ne/.local/bin/z3
export CAUSYNTH_CUSTOM_JDK_HOME
exec bash "$1"/experiments/accept/accept.sh

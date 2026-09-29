#!/usr/bin/env bash
# launch-run.sh <repo> <case-id> <out-suffix> -- one acceptance run from a
# GraphChecker snapshot worktree (its own jar, accept.sh, case dirs).
set -uo pipefail
export PATH=/usr/lib/maven/bin:$PATH
export SKIP_BUILD=1
export JAR="$1/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar"
export CASES="$2"
export OUT=${GC_OUT:-/u/vnr3ne/gc-out}/accept-"$3"
export Z3_BIN=/u/vnr3ne/.local/bin/z3
export CAUSYNTH_CUSTOM_JDK_HOME=${CAUSYNTH_CUSTOM_JDK_HOME:-/u/vnr3ne/GraphChecker/third_party/OpenJDK-Concolic-Execution-Engine/build/linux-x86_64-normal-zero-release/images/j2sdk-image}
exec bash "$1"/experiments/accept/accept.sh

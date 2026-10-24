#!/usr/bin/env bash
set -euo pipefail
(( $# >= 2 )) || { echo "usage: worktree-add.sh <path> <commit-ish> [-b <branch> | --detach]" >&2; exit 2; }
# shellcheck source=gc-env.sh
source "$(dirname "${BASH_SOURCE[0]}")/gc-env.sh"
path=$1; rev=$(git rev-parse --verify --quiet "$2^{commit}" || printf '%s' "$2"); shift 2
mkdir -p "/localtmp/$(id -un)"
exec 9>"/localtmp/$(id -un)/worktree-add.lock"
flock 9
git -C "${GC_REPO}" worktree add -q --no-checkout "$@" "${path}" "${rev}"
git -C "${path}" sparse-checkout set --no-cone '/*' '!/third_party/'
git -C "${path}" checkout -q

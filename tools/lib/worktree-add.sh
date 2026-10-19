#!/usr/bin/env bash
set -euo pipefail
(( $# >= 2 )) || { echo "usage: worktree-add.sh <path> <commit-ish> [-b <branch> | --detach]" >&2; exit 2; }
path=$1; rev=$2; shift 2
git -C "${HOME}/GraphChecker" worktree add -q --no-checkout "$@" "${path}" "${rev}"
git -C "${path}" sparse-checkout set --no-cone '/*' '!/third_party/'
git -C "${path}" checkout -q

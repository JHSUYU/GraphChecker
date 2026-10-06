#!/usr/bin/env bash
# worktree-add.sh <path> <commit-ish> [git worktree add options: -b <branch>, --detach]
#
# A GraphChecker worktree or snapshot without third_party/: 47,665 of the
# repository's 48,098 files are the concolic VM's source, which no build or
# run reads (the VM image is built apart, VM_IMAGE).  A full checkout writes
# them all to NFS, most of an hour; this one takes seconds, and its git status
# a fraction of one.  Read or change the VM's source in a full checkout.
set -euo pipefail
(( $# >= 2 )) || { echo "usage: worktree-add.sh <path> <commit-ish> [-b <branch> | --detach]" >&2; exit 2; }
path=$1; rev=$2; shift 2
git -C "${HOME}/GraphChecker" worktree add -q --no-checkout "$@" "${path}" "${rev}"
git -C "${path}" sparse-checkout set --no-cone '/*' '!/third_party/'
git -C "${path}" checkout -q

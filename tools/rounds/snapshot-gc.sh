#!/usr/bin/env bash
# snapshot-gc.sh <snapshot>... -- removes GraphChecker snapshot worktrees
# (~/gc-run/<name>, `git worktree add --detach`) that nothing uses any more.
#
# A snapshot is kept, and said so, while a process on some lift names it
# (tools/lib/alive.sh), or when a lift did not answer.  Exits 1 when any
# named snapshot was kept.
set -uo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
(( $# > 0 )) || { echo "usage: snapshot-gc.sh <snapshot>..." >&2; exit 2; }
status=0
for snapshot in "$@"; do
  snapshot=$(cd "${snapshot}" && pwd -P) || { status=1; continue; }
  said=$(bash "${here}/../lib/alive.sh" "${snapshot}")
  if [[ -n "${said}" ]]; then
    echo "kept ${snapshot}: ${said//$'\n'/, }"
    status=1
    continue
  fi
  main=$(dirname "$(git -C "${snapshot}" rev-parse --path-format=absolute \
    --git-common-dir)")
  git -C "${main}" worktree remove --force "${snapshot}" \
    && echo "removed ${snapshot}" || status=1
done
exit "${status}"

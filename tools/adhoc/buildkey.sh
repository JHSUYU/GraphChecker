#!/usr/bin/env bash
# buildkey.sh <adhoc-experiment-dir> [--inputs]
#
# The build key of an ad-hoc experiment: the name of its static slices,
# $GC_OUT/static/<key>/, and of its pre-screen recordings,
# $GC_OUT/prescreen/<key>/ (slice.sh, prescreen.sh, nightly.sh).  A slice is
# a function of three things, and the key digests exactly them, never a path
# a snapshot happens to live at:
#   the engine  the GraphChecker jar this checkout runs: the sha256 of its
#               entries' names and bytes in name order, not of the archive,
#               whose entry times and order make every clean rebuild of one
#               commit a different file;
#   the tree    the commit of the tree the experiment's `tree` file names,
#               whose classes the slice reads -- a tree with uncommitted
#               changes to tracked files names no build, and is refused;
#   the scope   the declarations the slice's scope and seeds come from: the
#               system's system.sh, and the experiment's case.sh,
#               workflow.properties, communication-mappings.jsonl and
#               loop-bounds.jsonl (an absent one is digested as absent).
# A check's own row (checks.tsv, targets/<check>.yaml) is the check's: it
# names the check's directory under the key, not the key.
#
# Prints "<experiment>-<12 hex digits>"; with --inputs, one JSON object of
# the key and what it digests (slice.sh keeps it as <key>/key.json).
set -euo pipefail
experiment=$(cd "${1:?adhoc experiment dir}" && pwd -P)
checkout=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)
jar=${checkout}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar
[[ -s "${jar}" ]] || { echo "buildkey: no built jar: ${jar}" >&2; exit 2; }
read -r tree <"${experiment}/tree"
commit=$(git -C "${tree}" rev-parse HEAD)
[[ -z "$(git -C "${tree}" status --porcelain --untracked-files=no)" ]] || {
  echo "buildkey: ${tree} has uncommitted changes to tracked files, so its" \
    "commit ${commit} names no build: commit them first" >&2
  exit 2
}
system=$(dirname "${experiment}")
name=$(basename "${experiment}")
jar_digest=$(python3 -c '
import hashlib, sys, zipfile
digest = hashlib.sha256()
with zipfile.ZipFile(sys.argv[1]) as jar:
    for name in sorted(jar.namelist()):
        digest.update(name.encode() + b"\0" + jar.read(name))
print(digest.hexdigest())' "${jar}")
lines=("jar ${jar_digest}" "tree ${tree} ${commit}")
for file in "${system}/system.sh" "${experiment}"/{case.sh,workflow.properties,communication-mappings.jsonl,loop-bounds.jsonl}; do
  if [[ -f "${file}" ]]; then
    digest=$(sha256sum <"${file}" | cut -d' ' -f1)
  else
    digest=absent
  fi
  lines+=("$(basename "$(dirname "${file}")")/$(basename "${file}") ${digest}")
done
key=${name}-$(printf '%s\n' "${lines[@]}" | sha256sum | cut -c1-12)
if [[ "${2:-}" == --inputs ]]; then
  printf '%s\n' "${lines[@]}" | jq -R -s --arg key "${key}" --arg jar "${jar}" '
    split("\n") | map(select(. != "") | split(" ")) as $rows
    | {key: $key,
       jar: {path: $jar, sha256: ($rows[0][1])},
       tree: {path: $rows[1][1], commit: $rows[1][2]},
       declarations: ($rows[2:] | map({(.[0]): .[1]}) | add)}'
else
  echo "${key}"
fi

#!/usr/bin/env bash
set -euo pipefail
dest=${1:?usage: build-image-docker.sh <dir>}
checkout=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)
src=${checkout}/third_party/OpenJDK-Concolic-Execution-Engine
[[ -f "${src}/docker/causynth/Dockerfile" ]] \
  || { echo "no VM sources at ${src} (a worktree from tools/lib/worktree-add.sh has no third_party/)" >&2; exit 2; }
repo=$(git -C "${checkout}" rev-parse --path-format=absolute --git-common-dir)
scratch=/localtmp/$(id -un)
mkdir -p "${scratch}" "$(dirname "${dest}")"
sudo docker build -q -t causynth-openjdk8-build:ubuntu18 -f "${src}/docker/causynth/Dockerfile" "${src}" >/dev/null
printf 'FROM causynth-openjdk8-build:ubuntu18\nRUN apt-get update && apt-get install -y --no-install-recommends git rsync && rm -rf /var/lib/apt/lists/*\n' \
  | sudo docker build -q -t causynth-openjdk8-build:ubuntu18-git - >/dev/null
sudo docker run --rm --user "$(id -u):$(id -g)" -e HOME=/tmp -e JOBS="${JOBS:-$(nproc)}" \
  -v "${checkout}:${checkout}" -v "${repo}:${repo}" -v "${scratch}:${scratch}" \
  -v "$(dirname "${dest}"):$(dirname "${dest}")" -w "${checkout}" causynth-openjdk8-build:ubuntu18-git \
  bash -c "git config --global --add safe.directory '*' && VM_BUILD_ROOT=${scratch}/vm-build tools/vm/build-image.sh ${dest}"

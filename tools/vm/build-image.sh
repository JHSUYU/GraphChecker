#!/usr/bin/env bash
set -euo pipefail
dest=${1:?usage: build-image.sh <dir>}
checkout=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)
src=${checkout}/third_party/OpenJDK-Concolic-Execution-Engine
[[ -f "${src}/scripts/causynth_build_openjdk.sh" ]] \
  || { echo "no VM sources at ${src} (a worktree from tools/lib/worktree-add.sh has no third_party/)" >&2; exit 2; }
[[ ! -e "${dest}/j2sdk-image" ]] \
  || { echo "${dest}/j2sdk-image exists: never overwrite an image a run may read; name a new directory" >&2; exit 2; }
build=${VM_BUILD_ROOT:-/localtmp/$(id -un)/vm-build}
mkdir -p "${build}" "${dest}"
rsync -a --checksum --delete --exclude=/build "${src}/" "${build}/src/"

export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
export PATH=${JAVA_HOME}/bin:${PATH}
export LIBFFI_CFLAGS=-I/usr/include/x86_64-linux-gnu
export LIBFFI_LIBS=/usr/lib/x86_64-linux-gnu/libffi_pic.a
FULL_JDK=true JOBS=${JOBS:-40} GRAPH_CHECKER_ROOT=${checkout} \
  bash "${build}/src/scripts/causynth_build_openjdk.sh"

image=${build}/src/build/linux-x86_64-normal-zero-release/images/j2sdk-image
rm -rf "${dest}/j2sdk-image.partial"
cp -a "${image}" "${dest}/j2sdk-image.partial"
mv "${dest}/j2sdk-image.partial" "${dest}/j2sdk-image"
{
  echo "VM sources: GraphChecker $(git -C "${checkout}" rev-parse HEAD) third_party/OpenJDK-Concolic-Execution-Engine"
  echo "built $(date -Is) on $(hostname) by tools/vm/build-image.sh"
  (cd "${dest}/j2sdk-image" && md5sum jre/lib/amd64/server/libjvm.so jre/lib/rt.jar)
} >"${dest}/SOURCE.txt"
if JDK_HOME=${dest}/j2sdk-image OUT=${build}/smoke \
    bash "${build}/src/scripts/causynth_smoke_test.sh" >"${dest}/smoke.log" 2>&1; then
  echo "SMOKE_EXIT=0" >>"${dest}/smoke.log"
  echo "image ${dest}/j2sdk-image: smoke suite passed"
else
  echo "SMOKE_EXIT=$?" >>"${dest}/smoke.log"
  echo "image ${dest}/j2sdk-image: smoke suite FAILED, see ${dest}/smoke.log" >&2
  exit 1
fi

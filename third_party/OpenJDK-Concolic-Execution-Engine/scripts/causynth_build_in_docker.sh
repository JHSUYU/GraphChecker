#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
IMAGE=${CAUSYNTH_OPENJDK_BUILD_IMAGE:-causynth-openjdk8-build:ubuntu18}
JOBS=${JOBS:-4}

docker build \
  --platform linux/amd64 \
  -t "$IMAGE" \
  -f "$ROOT/docker/causynth/Dockerfile" \
  "$ROOT"

docker run --rm \
  --platform linux/amd64 \
  --user "$(id -u):$(id -g)" \
  -e HOME=/tmp \
  -e JOBS="$JOBS" \
  -e LIBFFI_CFLAGS=-I/usr/include/x86_64-linux-gnu \
  -e LIBFFI_LIBS=/usr/lib/x86_64-linux-gnu/libffi_pic.a \
  -v "$ROOT:/workspace" \
  -w /workspace \
  "$IMAGE" \
  bash scripts/causynth_build_openjdk.sh

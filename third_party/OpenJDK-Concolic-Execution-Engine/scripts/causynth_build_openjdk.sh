#!/usr/bin/env bash
set -euo pipefail

CONF=${CONF:-linux-x86_64-normal-zero-release}
JOBS=${JOBS:-4}
LOG=${LOG:-info}
BOOT_JDK=${BOOT_JDK:-/usr/lib/jvm/java-8-openjdk-amd64}

if [[ ! -f "build/$CONF/spec.gmk" ]]; then
  bash ./configure \
    CC=gcc-6 \
    CXX=g++-6 \
    --with-boot-jdk="$BOOT_JDK" \
    --with-jvm-variants=zero \
    --with-debug-level=release \
    --with-native-debug-symbols=none \
    --with-extra-cflags="-DENABLE_CONCOLIC -DONELINE -DCONCOLIC_JDBC -DENABLE_WEBRIDGE" \
    --with-extra-cxxflags="-DENABLE_CONCOLIC -DONELINE -DCONCOLIC_JDBC -DENABLE_WEBRIDGE"
fi

make hotspot jdk images JOBS="$JOBS" LOG="$LOG" CONF="$CONF"

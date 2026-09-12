#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
JDK_ROOT=$(cd "$SCRIPT_DIR/.." && pwd)
GRAPH_CHECKER_ROOT=${GRAPH_CHECKER_ROOT:-$(cd "$JDK_ROOT/../.." && pwd)}

CONF=${CONF:-linux-x86_64-normal-zero-release}
# The OpenJDK top-level makefile rejects receiving both CONF and SPEC.  CONF is
# only this wrapper's configuration selector; the exact spec is passed below.
export -n CONF 2>/dev/null || true
JOBS=${JOBS:-4}
LOG=${LOG:-info}
FULL_JDK=${FULL_JDK:-false}
BOOT_JDK=${BOOT_JDK:-/usr/lib/jvm/java-8-openjdk-amd64}
BUILD_DIR="$JDK_ROOT/build/$CONF"
SPEC_FILE="$BUILD_DIR/spec.gmk"

die() {
  printf 'causynth_build_openjdk.sh: %s\n' "$*" >&2
  exit 1
}

find_gcc6_pair() {
  local path_cc path_cxx

  path_cc=$(command -v gcc-6 2>/dev/null || true)
  path_cxx=$(command -v g++-6 2>/dev/null || true)
  if [[ -n "$path_cc" && -n "$path_cxx" ]]; then
    CC_BIN=$path_cc
    CXX_BIN=$path_cxx
    return
  fi

  GCC6_COMPAT_ROOT=${CAUSYNTH_GCC6_COMPAT_ROOT:-$GRAPH_CHECKER_ROOT/target/gcc6-compat/root}
  path_cc="$GCC6_COMPAT_ROOT/usr/bin/gcc-6"
  path_cxx="$GCC6_COMPAT_ROOT/usr/bin/g++-6"
  if [[ -x "$path_cc" && -x "$path_cxx" ]]; then
    CC_BIN=$path_cc
    CXX_BIN=$path_cxx
    PATH="$GCC6_COMPAT_ROOT/usr/bin:$PATH"

    # The unpacked compiler needs its adjacent compatibility libraries, but
    # does not require (or modify) any system packages.
    local compat_lib="$GCC6_COMPAT_ROOT/usr/lib/x86_64-linux-gnu"
    if [[ -d "$compat_lib" ]]; then
      LD_LIBRARY_PATH="$compat_lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
      export LD_LIBRARY_PATH
    fi
    export PATH
    return
  fi

  die "GCC 6 is required. Put gcc-6 and g++-6 on PATH, or set CAUSYNTH_GCC6_COMPAT_ROOT to an unpacked GCC 6 root. Newer GCC versions are deliberately not used because the resulting VM crashes in System.symbolize."
}

require_gcc6() {
  local compiler=$1 version
  version=$("$compiler" -dumpfullversion -dumpversion 2>/dev/null || true)
  [[ "$version" == 6 || "$version" == 6.* ]] ||
    die "$compiler reports version '${version:-unknown}', but this VM must be built with GCC 6; refusing to fall back to another compiler."
}

configure_linker_search_path() {
  local target compiler_libstdcpp system_gcc_lib compat_gcc_lib multiarch_lib
  target=$($CC_BIN -dumpmachine 2>/dev/null || true)
  [[ -n "$target" ]] ||
    die "Could not determine the GCC 6 target triple from $CC_BIN."

  # The repository-local compatibility tree intentionally contains only the
  # GCC 6 compiler/development packages.  Its libstdc++.so linker script may
  # therefore point at a runtime library that is supplied by the host.  Find
  # that host development directory explicitly instead of relying on paths
  # baked into a relocated compiler package.
  compiler_libstdcpp=$($CXX_BIN -print-file-name=libstdc++.so \
    2>/dev/null || true)
  if [[ "$compiler_libstdcpp" = /* && -e "$compiler_libstdcpp" ]]; then
    system_gcc_lib=$(dirname "$compiler_libstdcpp")
  else
    system_gcc_lib=$(find "/usr/lib/gcc/$target" -mindepth 2 -maxdepth 2 \
      -name libstdc++.so -print 2>/dev/null | sort -V | tail -n 1 || true)
  fi
  [[ -n "$system_gcc_lib" && -e "$system_gcc_lib" ]] ||
    die "A host libstdc++ development linker entry was not found under /usr/lib/gcc/$target. Install/provide it before building the customized VM."
  if [[ ! -d "$system_gcc_lib" ]]; then
    system_gcc_lib=$(dirname "$system_gcc_lib")
  fi

  compat_gcc_lib="${GCC6_COMPAT_ROOT:-}/usr/lib/gcc/$target/6"
  multiarch_lib="/usr/lib/$target"
  LIBRARY_PATH="$system_gcc_lib"
  if [[ -d "$multiarch_lib" ]]; then
    LIBRARY_PATH="$LIBRARY_PATH:$multiarch_lib"
  fi
  if [[ -n "${GCC6_COMPAT_ROOT:-}" && -d "$compat_gcc_lib" ]]; then
    LIBRARY_PATH="$compat_gcc_lib:$LIBRARY_PATH"
  fi
  LIBRARY_PATH="$LIBRARY_PATH${LIBRARY_PATH_ORIGINAL:+:$LIBRARY_PATH_ORIGINAL}"
  export LIBRARY_PATH
}

find_libffi() {
  if [[ ${LIBFFI_CFLAGS+x} == x || ${LIBFFI_LIBS+x} == x ]]; then
    [[ ${LIBFFI_CFLAGS+x} == x && ${LIBFFI_LIBS+x} == x ]] ||
      die "Set both LIBFFI_CFLAGS and LIBFFI_LIBS, or leave both unset for automatic compatibility-tree detection."
    FFI_CFLAGS=$LIBFFI_CFLAGS
    FFI_LIBS=$LIBFFI_LIBS
    return
  fi

  local ffi_root=${CAUSYNTH_LIBFFI_ROOT:-$GRAPH_CHECKER_ROOT/target/libffi-dev-compat/usr}
  local ffi_include="$ffi_root/include/x86_64-linux-gnu"
  local ffi_lib_dir="$ffi_root/lib/x86_64-linux-gnu"
  local ffi_archive

  if [[ -f "$ffi_lib_dir/libffi_pic.a" ]]; then
    ffi_archive="$ffi_lib_dir/libffi_pic.a"
  elif [[ -f "$ffi_lib_dir/libffi.a" ]]; then
    ffi_archive="$ffi_lib_dir/libffi.a"
  else
    die "libffi static library not found under $ffi_lib_dir. Set LIBFFI_CFLAGS and LIBFFI_LIBS, or set CAUSYNTH_LIBFFI_ROOT to an unpacked libffi development tree."
  fi
  [[ -f "$ffi_include/ffi.h" && -f "$ffi_include/ffitarget.h" ]] ||
    die "libffi headers not found under $ffi_include. Set LIBFFI_CFLAGS and LIBFFI_LIBS, or set CAUSYNTH_LIBFFI_ROOT correctly."

  FFI_CFLAGS="-I$ffi_include"
  FFI_LIBS=$ffi_archive
}

atomic_copy() {
  local source=$1 destination=$2 destination_dir temporary
  [[ -s "$source" ]] || die "HotSpot output is missing or empty: $source"
  destination_dir=$(dirname "$destination")
  [[ -d "$destination_dir" ]] ||
    die "Refusing to create an unexpected runtime directory: $destination_dir"

  temporary=$(mktemp "$destination_dir/.causynth.$(basename "$destination").XXXXXX")
  if ! cp -p -- "$source" "$temporary"; then
    rm -f -- "$temporary"
    die "Could not stage $source for $destination"
  fi
  if ! mv -f -- "$temporary" "$destination"; then
    rm -f -- "$temporary"
    die "Could not atomically replace $destination"
  fi
}

sync_hotspot_runtime() {
  local source_runtime="$BUILD_DIR/hotspot/dist/jre"
  local runtime_root

  for runtime_root in "${EXISTING_RUNTIMES[@]}"; do
    atomic_copy "$source_runtime/lib/amd64/server/libjvm.so" \
      "$runtime_root/lib/amd64/server/libjvm.so"
    atomic_copy "$source_runtime/lib/amd64/libjsig.so" \
      "$runtime_root/lib/amd64/libjsig.so"
    atomic_copy "$source_runtime/lib/amd64/server/Xusage.txt" \
      "$runtime_root/lib/amd64/server/Xusage.txt"
    printf 'Updated HotSpot runtime in %s\n' "$runtime_root"
  done
}

LIBRARY_PATH_ORIGINAL=${LIBRARY_PATH:-}
find_gcc6_pair
require_gcc6 "$CC_BIN"
require_gcc6 "$CXX_BIN"
configure_linker_search_path
find_libffi
MAKE_BIN=$(command -v make 2>/dev/null || true)
[[ -n "$MAKE_BIN" ]] || die "GNU make was not found on PATH."

[[ -x "$BOOT_JDK/bin/java" ]] ||
  die "Boot JDK is missing at $BOOT_JDK (expected executable $BOOT_JDK/bin/java). Set BOOT_JDK to a JDK 7 or 8 installation."

cd "$JDK_ROOT"

if [[ ! -f "$SPEC_FILE" ]]; then
  if ! bash ./configure \
    --with-conf-name="$CONF" \
    "CC=$CC_BIN" \
    "CXX=$CXX_BIN" \
    "BUILD_CC=$CC_BIN" \
    "BUILD_CXX=$CXX_BIN" \
    "LIBFFI_CFLAGS=$FFI_CFLAGS" \
    "LIBFFI_LIBS=$FFI_LIBS" \
    --with-boot-jdk="$BOOT_JDK" \
    --with-jvm-variants=zero \
    --with-debug-level=release \
    --with-native-debug-symbols=none \
    --with-extra-cflags="-DENABLE_CONCOLIC" \
    --with-extra-cxxflags="-DENABLE_CONCOLIC"; then
    die "OpenJDK configure failed. A fresh full image needs all native JDK build dependencies (including freetype and CUPS headers); provide them via an existing toolchain/container and rerun. No system packages were installed."
  fi
fi

# Command-line variables take precedence over paths frozen into an old spec.gmk.
# HOSTCC/HOSTCXX and LD are included because hotspot-spec.gmk also snapshots
# those derived compiler variables at configure time.
MAKE_ARGS=(
  "SPEC=$SPEC_FILE"
  "JOBS=$JOBS"
  "LOG=$LOG"
  "CC=$CC_BIN"
  "CXX=$CXX_BIN"
  "CPP=$CC_BIN -E"
  "AS=$CC_BIN -c"
  "LD=$CC_BIN"
  "LDEXE=$CC_BIN"
  "LDCXX=$CC_BIN"
  "BUILD_CC=$CC_BIN"
  "BUILD_CXX=$CXX_BIN"
  "BUILD_LD=$CC_BIN"
  "HOSTCC=$CC_BIN"
  "HOSTCXX=$CXX_BIN"
  "HOTSPOT_LD=$CC_BIN"
  "LIBFFI_CFLAGS=$FFI_CFLAGS"
  "LIBFFI_LIBS=$FFI_LIBS"
  "MAKE=$MAKE_BIN -R -I $JDK_ROOT/make/common"
  # Do not pass TOPDIR on the make command line.  The legacy HotSpot build
  # assigns TOPDIR to each generated product directory; a command-line value
  # is inherited by recursive make and would redirect its generated files to
  # $JDK_ROOT/../generated instead.
  "SRC_ROOT=$JDK_ROOT"
  "OUTPUT_ROOT=$BUILD_DIR"
  "BUILD_OUTPUT=$BUILD_DIR"
  "JDK_TOPDIR=$JDK_ROOT/jdk"
  "LANGTOOLS_TOPDIR=$JDK_ROOT/langtools"
  "CORBA_TOPDIR=$JDK_ROOT/corba"
  "JAXP_TOPDIR=$JDK_ROOT/jaxp"
  "JAXWS_TOPDIR=$JDK_ROOT/jaxws"
  "HOTSPOT_TOPDIR=$JDK_ROOT/hotspot"
  "NASHORN_TOPDIR=$JDK_ROOT/nashorn"
  "HOTSPOT_OUTPUTDIR=$BUILD_DIR/hotspot"
  "HOTSPOT_DIST=$BUILD_DIR/hotspot/dist"
  "JDK_OUTPUTDIR=$BUILD_DIR/jdk"
  "IMAGES_OUTPUTDIR=$BUILD_DIR/images"
  "BOOT_JDK=$BOOT_JDK"
  "BOOT_RTJAR=$BOOT_JDK/jre/lib/rt.jar"
  "BOOT_TOOLSJAR=$BOOT_JDK/lib/tools.jar"
)

EXISTING_RUNTIMES=()
if [[ -x "$BUILD_DIR/jdk/bin/java" ]]; then
  EXISTING_RUNTIMES+=("$BUILD_DIR/jdk")
fi
if [[ -x "$BUILD_DIR/images/j2sdk-image/bin/java" ]]; then
  EXISTING_RUNTIMES+=("$BUILD_DIR/images/j2sdk-image/jre")
fi
if [[ -x "$BUILD_DIR/images/j2re-image/bin/java" ]]; then
  EXISTING_RUNTIMES+=("$BUILD_DIR/images/j2re-image")
fi

if (( ${#EXISTING_RUNTIMES[@]} > 0 )) && [[ "$FULL_JDK" != true ]]; then
  make hotspot "${MAKE_ARGS[@]}"
  sync_hotspot_runtime
else
  if make hotspot jdk images "${MAKE_ARGS[@]}"; then
    printf 'Built full OpenJDK image in %s/images/j2sdk-image\n' "$BUILD_DIR"
  else
    status=$?
    printf '%s\n' \
      "causynth_build_openjdk.sh: Full JDK/image build failed. No reusable build JDK or image was found, so native JDK components had to be built as well." \
      "Provide the configured native dependencies (notably freetype and CUPS headers), or seed this configuration with a previously built JDK/image. GCC was not changed or silently replaced." >&2
    exit "$status"
  fi
fi

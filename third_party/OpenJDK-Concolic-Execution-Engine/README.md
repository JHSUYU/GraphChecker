# Causynth OpenJDK concolic execution engine

This tree derives from the WeBridge OpenJDK 8 concolic engine and contains the
customized Zero VM used by GraphChecker's narrow replay stage. GraphChecker
itself and broad discovery tracing must run on a stock JDK 8; do not make this
VM the workflow's global `JAVA_HOME`.

## Canonical build

From the GraphChecker repository root, build the `linux/amd64` image and VM:

```bash
JOBS=4 \
  third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_build_in_docker.sh
```

The JDK image is written to:

```text
third_party/OpenJDK-Concolic-Execution-Engine/build/linux-x86_64-normal-zero-release/images/j2sdk-image
```

The Docker build supplies the supported GCC 6, boot JDK 8, and libffi
environment. Build products are intentionally ignored by Git.

## Smoke test

```bash
JDK_HOME="$PWD/third_party/OpenJDK-Concolic-Execution-Engine/build/linux-x86_64-normal-zero-release/images/j2sdk-image" \
  third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_smoke_test.sh
```

Use the resulting image in GraphChecker with:

```bash
export CAUSYNTH_CUSTOM_JDK_HOME=/absolute/path/to/j2sdk-image
```

For the complete workflow and the separation between stock-JDK discovery and
custom-VM replay, see the [GraphChecker README](../../README.md).

The helper `scripts/causynth_build_openjdk.sh` also supports a native build,
but then the caller must provide the exact GCC 6, boot JDK, libffi, and native
library prerequisites. The Docker entrypoint is the documented portable path.

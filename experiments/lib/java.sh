#!/usr/bin/env bash
# The engine JVM, for every case: the heap its campaign states
# (engine_memory_mb), else 8 GB.
exec /usr/lib/jvm/java-8-openjdk-amd64/bin/java \
  -Xmx"${GRAPH_CHECKER_ENGINE_MEMORY_MB:-8192}"m "$@"

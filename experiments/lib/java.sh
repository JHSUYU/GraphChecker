#!/usr/bin/env bash
# The engine JVM, for every case: the heap its campaign states
# (engine_memory_mb), else 8 GB; and a stack as deep as the expression
# chains its walks recurse along (a container a run rebuilt entry by entry
# is one reference per put: IMPORT's DAG check overflowed 1 MB).
exec /usr/lib/jvm/java-8-openjdk-amd64/bin/java \
  -Xmx"${GRAPH_CHECKER_ENGINE_MEMORY_MB:-8192}"m -Xss512m "$@"

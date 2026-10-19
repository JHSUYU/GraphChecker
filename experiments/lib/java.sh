#!/usr/bin/env bash
exec /usr/lib/jvm/java-8-openjdk-amd64/bin/java \
  -Xmx"${GRAPH_CHECKER_ENGINE_MEMORY_MB:-8192}"m -Xss512m "$@"

#!/usr/bin/env bash
# The engine JVM, for every case.
exec /usr/lib/jvm/java-8-openjdk-amd64/bin/java -Xmx8g "$@"

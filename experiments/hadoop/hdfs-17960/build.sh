#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
export CAUSYNTH_HADOOP_JAVAC=/usr/lib/jvm/java-8-openjdk-amd64/bin/javac
exec bash "${here}/../lib/build.sh" /u/vnr3ne/hadoop-hdfs-17960 \
  org.apache.hadoop.hdfs.server.namenode.snapshot.TestOrderedSnapshotDeletion \
  testOrderedDeletionWithRestart

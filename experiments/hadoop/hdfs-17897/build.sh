#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
exec bash "${here}/../lib/build.sh" /u/vnr3ne/hadoop-hdfs-17897 \
  org.apache.hadoop.hdfs.TestCausynthStripedChecksum \
  testStaleEncryptionKeyFailsStripedChecksum

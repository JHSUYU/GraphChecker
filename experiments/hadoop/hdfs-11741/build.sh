#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
exec bash "${here}/../lib/build.sh" /opt/hadoop-hdfs-11741 \
  org.apache.hadoop.hdfs.server.balancer.TestCausynthExpiredBalancerKey \
  testEncryptedBalancerAfterKeyRotations

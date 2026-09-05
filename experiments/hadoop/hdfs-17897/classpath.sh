#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
repo=/opt/hadoop-hdfs-17897
report=${repo}/hadoop-hdfs-project/hadoop-hdfs/target/surefire-reports/TEST-org.apache.hadoop.hdfs.TestCausynthStripedChecksum.xml
[[ -f "${report}" ]] || {
  echo "missing test report: ${report}; run build first" >&2
  exit 2
}
exec python3 "${here}/../lib/classpath.py" "${repo}" "${report}"

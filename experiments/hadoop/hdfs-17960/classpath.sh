#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
repo=/u/vnr3ne/hadoop-hdfs-17960
report=${repo}/hadoop-hdfs-project/hadoop-hdfs/target/surefire-reports/TEST-org.apache.hadoop.hdfs.server.namenode.snapshot.TestOrderedSnapshotDeletion.xml
[[ -f "${report}" ]] || {
  echo "missing test report: ${report}; run build first" >&2
  exit 2
}
exec python3 "${here}/../lib/classpath.py" "${repo}" "${report}"

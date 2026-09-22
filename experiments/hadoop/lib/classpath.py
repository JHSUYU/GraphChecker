#!/usr/bin/env python3
"""Read the workload dependencies while keeping Hadoop classes in one checkout."""
import os
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

repo, report = map(Path, sys.argv[1:])
root = ET.parse(report).getroot()
value = next((p.get("value", "") for p in root.findall("./properties/property")
              if p.get("name") == "java.class.path"), "")
if not value:
    raise SystemExit(f"test report has no java.class.path: {report}")

# Maven installs every experiment under the same SNAPSHOT coordinates. Never
# load another experiment's common/client classes from that shared repository.
modules = ("hadoop-hdfs-project/hadoop-hdfs",
           "hadoop-hdfs-project/hadoop-hdfs-client",
           "hadoop-common-project/hadoop-common")
entries = [str(repo / modules[0] / "target/test-classes")]
entries += [str(repo / module / "target/classes") for module in modules]
for entry in entries:
    if not Path(entry).is_dir():
        raise SystemExit(f"missing compiled classes: {entry}; run build first")
for entry in value.split(os.pathsep):
    # The launcher supplies the current frozen GraphChecker jar explicitly.
    if "/org/example/GraphChecker/" in entry:
        continue
    # The report was written on the host that built the tree, and each host
    # keeps its own local Maven repository: an entry this host does not have
    # contributes nothing here, and handed on it is a path Soot refuses.
    if entry and not os.path.exists(entry):
        continue
    if entry and entry not in entries:
        entries.append(entry)
print(os.pathsep.join(entries))

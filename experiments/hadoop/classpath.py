#!/usr/bin/env python3
"""classpath.py <tree> <surefire report>: the workload's classpath, read off
the report of a run of its test, every Hadoop class from the case's own tree."""
import os
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

repo, report = map(Path, sys.argv[1:])
root = ET.parse(report).getroot()
properties = {p.get("name"): p.get("value", "")
              for p in root.findall("./properties/property")}
value = properties.get("java.class.path", "")
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
# The checkout whose run wrote the report (surefire's basedir is its module).
# A tree made from another's build keeps that one's reports: every entry
# under that checkout is this tree's, at the same place.
basedir = properties.get("basedir", "")
if not basedir.endswith("/" + modules[0]):
    raise SystemExit(f"test report's basedir is not {modules[0]}: {report}")
ran = basedir[:-len(modules[0]) - 1]
for entry in value.split(os.pathsep):
    if entry.startswith(ran + "/"):
        entry = str(repo) + entry[len(ran):]
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

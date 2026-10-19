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

modules = ("hadoop-hdfs-project/hadoop-hdfs",
           "hadoop-hdfs-project/hadoop-hdfs-client",
           "hadoop-common-project/hadoop-common")
entries = [str(repo / modules[0] / "target/test-classes")]
entries += [str(repo / module / "target/classes") for module in modules]
for entry in entries:
    if not Path(entry).is_dir():
        raise SystemExit(f"missing compiled classes: {entry}; run build first")
basedir = properties.get("basedir", "")
if not basedir.endswith("/" + modules[0]):
    raise SystemExit(f"test report's basedir is not {modules[0]}: {report}")
ran = basedir[:-len(modules[0]) - 1]
for entry in value.split(os.pathsep):
    if entry.startswith(ran + "/"):
        entry = str(repo) + entry[len(ran):]
    if "/org/example/GraphChecker/" in entry:
        continue
    if entry and not os.path.exists(entry):
        continue
    if entry and entry not in entries:
        entries.append(entry)
print(os.pathsep.join(entries))

#!/usr/bin/env python3
"""classpath.py <junit4 report>: the workload's classpath, read off the
report of the tree's own test run.

The report states the test JVM's java.class.path.  GraphChecker's jar is not
the tree's: the launcher supplies the frozen one explicitly, so the entry the
tree's build appended is dropped.  An entry this host does not have
contributes nothing and, handed on, is a path Soot refuses."""
import os
import sys
import xml.etree.ElementTree as ET

report = sys.argv[1]
root = ET.parse(report).getroot()
value = next((p.get("value", "") for p in root.findall("./properties/property")
              if p.get("name") == "java.class.path"), "")
if not value:
    raise SystemExit(f"test report has no java.class.path: {report}")
entries = []
for entry in value.split(os.pathsep):
    if not entry or "GraphChecker-" in os.path.basename(entry):
        continue
    if os.path.exists(entry) and entry not in entries:
        entries.append(entry)
print(os.pathsep.join(entries))

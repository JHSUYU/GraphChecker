#!/usr/bin/env python3
"""classpath.py <tree> <surefire report> <test module> <module>...: the
workload's classpath, as the tree's own test run stated it, with the tree's
modules loaded from the tree.

The report states the test JVM's java.class.path.  A module the build
resolved from its repository (every one but the module under test) is that
repository's jar of this tree; it is replaced by the module's compiled
classes (and a test jar by its test classes), so a workload loads one
checkout's classes, and a class rebuilt in the tree is the one it runs.
GraphChecker's jar is not the tree's: the launcher supplies the frozen one,
so the entries the build added are dropped, and so is the tree's Gson (2.9,
Hadoop's): GraphChecker's jar follows the tree's classpath, and the runtime's
publication calls Gson 2.10's JsonObject#asMap, so the workload JVM loads the
jar's Gson.  An entry this host does not
have contributes nothing and, handed on, is a path Soot refuses."""
import os
import re
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

repo, report, test_module = Path(os.path.realpath(sys.argv[1])), sys.argv[2], sys.argv[3]
modules = set(sys.argv[3:])
root = ET.parse(report).getroot()
value = next((p.get("value", "") for p in root.findall("./properties/property")
              if p.get("name") == "java.class.path"), "")
if not value:
    raise SystemExit(f"test report has no java.class.path: {report}")

GSON = re.compile(r"/com/google/code/gson/gson/[^/]+/gson-[^/]+\.jar$")
JAR = re.compile(r"/org/apache/hbase/(hbase-[a-z-]+)/[^/]+/\1-[^/]+?(-tests)?\.jar$")


def tree_entry(entry):
    match = JAR.search(entry)
    if not match or match.group(1) not in modules:
        return None
    kind = "test-classes" if match.group(2) else "classes"
    return str(repo / match.group(1) / "target" / kind)


entries = []
for entry in value.split(os.pathsep):
    if not entry or os.path.basename(entry).startswith("GraphChecker-") or GSON.search(entry):
        continue
    entry = tree_entry(entry) or entry
    if os.path.exists(entry) and entry not in entries:
        entries.append(entry)
classes = str(repo / test_module / "target" / "classes")
if classes not in entries:
    raise SystemExit(f"missing compiled classes on the classpath: {classes}; run build first")
print(os.pathsep.join(entries))

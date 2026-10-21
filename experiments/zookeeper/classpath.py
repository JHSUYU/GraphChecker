#!/usr/bin/env python3
"""classpath.py <tree> <module> <surefire report>: the workload's classpath,
read off the report of the tree's own test run.

The tree's compiled classes come first -- the workload module's, then the
server's and jute's -- so no class of the tree is loaded from a jar of its
Maven repository (the server's test jar a recipe's tests use, say).
GraphChecker's jar is not the tree's: the launcher supplies the frozen one
explicitly, so the entry the build added is dropped, and so is the tree's Gson
(2.8): GraphChecker's jar follows the tree's classpath, and the runtime's
publication calls Gson 2.10's JsonObject#asMap, so the workload JVM loads the
jar's Gson (as HBase's classpath.py).  An entry this host
does not have contributes nothing and, handed on, is a path Soot refuses."""
import os
import re
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

repo, module, report = Path(sys.argv[1]), sys.argv[2], sys.argv[3]
root = ET.parse(report).getroot()
value = next((p.get("value", "") for p in root.findall("./properties/property")
              if p.get("name") == "java.class.path"), "")
if not value:
    raise SystemExit(f"test report has no java.class.path: {report}")

modules = [module] + [m for m in ("zookeeper-server", "zookeeper-jute")
                      if m != module]
entries = []
for each in modules:
    for kind in ("test-classes", "classes"):
        entry = repo / each / "target" / kind
        if entry.is_dir():
            entries.append(str(entry))
for required in (repo / module / "target/test-classes",
                 repo / "zookeeper-server/target/classes"):
    if str(required) not in entries:
        raise SystemExit(f"missing compiled classes: {required}; run build first")
GSON = re.compile(r"/com/google/code/gson/gson/[^/]+/gson-[^/]+\.jar$")
for entry in value.split(os.pathsep):
    name = os.path.basename(entry)
    if not entry or name.startswith("GraphChecker-") or GSON.search(entry):
        continue
    if "/org/apache/zookeeper/zookeeper" in entry:
        continue
    if os.path.exists(entry) and entry not in entries:
        entries.append(entry)
print(os.pathsep.join(entries))

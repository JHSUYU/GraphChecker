#!/usr/bin/env python3
"""sites.py <system-dir> <repo> : every `throw new X(...)` in the system's own
sources (system.sh's system_sources) that stands under an `if` -- a check --
as one JSON row: its class root, class, tree-relative file, throw line, the
if's line and text, the exception and its operand text.  A throw under no
`if` checks nothing and is not a row."""
import json
import os
import re
import subprocess
import sys

system_dir, repo = sys.argv[1], sys.argv[2]
sources = subprocess.run(
    ["bash", "-c", 'source "$1/system.sh"; printf "%s\\n" "${system_sources[@]}"',
     "_", system_dir], check=True, capture_output=True, text=True).stdout.split()
THROW = re.compile(r'throw\s+new\s+(?:@[\w.]+(?:\("[^"]*"\))?\s+)?([\w.]+)\s*\(')
IF = re.compile(r'^\s*(?:}\s*else\s+)?if\s*\((.*)$')
for entry in sources:
    root, rel = entry.split(":", 1)
    base = os.path.join(repo, rel)
    for directory, _, files in os.walk(base):
        for name in sorted(files):
            if not name.endswith(".java"):
                continue
            path = os.path.join(directory, name)
            lines = open(path, errors="ignore").read().split("\n")
            cls = os.path.relpath(path, base)[:-5].replace("/", ".")
            for i, line in enumerate(lines):
                m = THROW.search(line)
                if not m:
                    continue
                j, text = i, line[m.end():]
                while ");" not in text and j + 1 < len(lines) and j - i < 8:
                    j += 1
                    text += " " + lines[j].strip()
                cond, cond_line = "", -1
                for k in range(i - 1, max(-1, i - 8), -1):
                    mm = IF.match(lines[k])
                    if mm:
                        c, kk = lines[k].strip(), k
                        while "{" not in c and kk + 1 < i:
                            kk += 1
                            c += " " + lines[kk].strip()
                        cond, cond_line = c, k + 1
                        break
                    stripped = lines[k].strip()
                    if stripped.endswith(";") or (stripped.startswith(("catch", "}"))
                                                   and "else" not in stripped):
                        break
                if cond_line < 0:
                    continue
                print(json.dumps({"root": root, "cls": cls,
                                  "file": os.path.relpath(path, repo),
                                  "throwLine": i + 1, "condLine": cond_line,
                                  "cond": cond[:300], "exception": m.group(1),
                                  "operand": text.split(");")[0][:300]}))

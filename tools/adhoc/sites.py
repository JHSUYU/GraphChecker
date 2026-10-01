#!/usr/bin/env python3
"""sites.py <system-dir> <repo> : every `throw new X(...)` in the system's own
sources (system.sh's system_sources) that stands under an `if` -- a check --
as one JSON row: its class root, class, tree-relative file, throw line, the
if's line and text, the exception and its operand text.  A throw under no
`if` checks nothing and is not a row.  A throw is read as tools/lib/annotated.py
reads it: its line is the one its `throw new` starts on, and its type (after
a known-bug marker, when the tree marks it) may follow on the next lines."""
import json
import os
import re
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "lib"))
import annotated  # noqa: E402

system_dir, repo = sys.argv[1], sys.argv[2]
IF = re.compile(r'^\s*(?:}\s*else\s+)?if\s*\((.*)$')
for root, rel in annotated.sources(system_dir):
    base = os.path.join(repo, rel)
    for directory, _, files in os.walk(base):
        for name in sorted(files):
            if not name.endswith(".java"):
                continue
            path = os.path.join(directory, name)
            lines = open(path, errors="ignore").read().split("\n")
            cls = os.path.relpath(path, base)[:-5].replace("/", ".")
            for i in range(len(lines)):
                found = annotated.throw_matches(lines, i)
                if not found:
                    continue
                m = found[0]
                first, *rest = (m.string[m.end():].split("\n")
                                + lines[i + 1 + annotated.CONTINUATION:i + 9])
                text = first + "".join(" " + part.strip() for part in rest)
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

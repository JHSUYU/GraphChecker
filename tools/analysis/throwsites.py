#!/usr/bin/env python3
"""throwsites.py TREE > sites.jsonl : every `throw new X(...)` in the tree's hadoop-hdfs and
hadoop-hdfs-client main sources, with the `if` it stands under (the ad-hoc check), the
exception type and its operand text.  One JSON row per site."""
import os, re, sys, json
tree = sys.argv[1]
roots = [("hdfs", "hadoop-hdfs-project/hadoop-hdfs/src/main/java"),
         ("client", "hadoop-hdfs-project/hadoop-hdfs-client/src/main/java")]
THROW = re.compile(r'throw\s+new\s+(?:@[\w.]+(?:\("[^"]*"\))?\s+)?([\w.]+)\s*\(')
IF = re.compile(r'^\s*(?:}\s*else\s+)?if\s*\((.*)$')
for module, rel in roots:
    base = os.path.join(tree, rel)
    for dp, _, fs in os.walk(base):
        for f in fs:
            if not f.endswith(".java"): continue
            path = os.path.join(dp, f)
            lines = open(path, errors="ignore").read().split("\n")
            cls = os.path.relpath(path, base)[:-5]
            for i, line in enumerate(lines):
                m = THROW.search(line)
                if not m: continue
                # operand: from the throw to the closing ');'
                j, text = i, line[m.end():]
                while ');' not in text and j + 1 < len(lines) and j - i < 8:
                    j += 1; text += " " + lines[j].strip()
                operand = text.split(');')[0]
                # the if it stands under: scan up for the nearest `if (`, stop at a statement end
                cond, cl = "", -1
                for k in range(i - 1, max(-1, i - 8), -1):
                    mm = IF.match(lines[k])
                    if mm:
                        c, kk = lines[k].strip(), k
                        while '{' not in c and kk + 1 < i: kk += 1; c += " " + lines[kk].strip()
                        cond, cl = c, k + 1
                        break
                    if lines[k].strip().endswith(";") or lines[k].strip().startswith(("catch", "}")) and "else" not in lines[k]:
                        break
                print(json.dumps({"module": module, "cls": cls.replace("/", "."), "file": os.path.relpath(path, tree),
                                  "throwLine": i + 1, "condLine": cl, "cond": cond[:300],
                                  "exception": m.group(1), "operand": operand[:300]}))

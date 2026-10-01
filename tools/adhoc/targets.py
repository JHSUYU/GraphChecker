#!/usr/bin/env python3
"""targets.py <adhoc-experiment-dir> <tree> : writes targets/<check>.yaml for
every check the experiment's checks.tsv declares, one line each:

    exception_target: adhoc-<check> <binary class name> <throw line> [<type>]

The class is the check's source file under its system's source roots
(system.sh's system_sources); the engine finds the throw in that class or a
class nested in it by the line (causynth.ExceptionTargetLineResolver), so
nothing in <tree> is edited and nothing is rebuilt.  The thrown type is stated
only when <tree>'s line holds more than one `throw new`, and then it is the
first one's, the one sites.py named the check by.  A line that holds no
`throw new` (the tree moved since the check was chosen) is refused."""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "lib"))
import annotated  # noqa: E402

experiment, tree = sys.argv[1], sys.argv[2]
system_dir = os.path.dirname(os.path.abspath(experiment))
roots = [rel.rstrip("/") + "/" for _, rel in annotated.sources(system_dir)]
os.makedirs(os.path.join(experiment, "targets"), exist_ok=True)
for row in open(os.path.join(experiment, "checks.tsv")):
    if row.startswith("#") or not row.strip():
        continue
    check, source, line = row.rstrip("\n").split("\t")[:3]
    root = next((r for r in roots if source.startswith(r)), None)
    if root is None or not source.endswith(".java"):
        sys.exit("%s: %s is under none of %s" % (check, source, roots))
    cls = source[len(root):-len(".java")].replace("/", ".")
    text = open(os.path.join(tree, source)).read().split("\n")
    throws = annotated.throws_at(text, int(line) - 1)
    if not throws:
        sys.exit("%s: %s:%s holds no `throw new`: %s"
                 % (check, source, line, text[int(line) - 1].strip()))
    spec = "exception_target: adhoc-%s %s %s" % (check, cls, line)
    if len(throws) > 1:
        spec += " " + throws[0]
    with open(os.path.join(experiment, "targets", check + ".yaml"), "w") as out:
        out.write(spec + "\n")
    print(check, "->", "%s:%s" % (cls, line))

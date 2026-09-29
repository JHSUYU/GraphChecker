#!/usr/bin/env python3
"""annotate.py <adhoc-experiment-dir> <tree> : annotates every check the
experiment's checks.tsv declares in <tree> --
@CausynthExceptionTarget("adhoc-<check>") on its throw, fully qualified and
on the throw's own line so no line number moves -- and writes the check's
targets/<check>.yaml.  A line already annotated with its own target is left
as it is; one annotated with another is refused."""
import os
import sys

ANNOTATION = "@edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget"
experiment, tree = sys.argv[1], sys.argv[2]
os.makedirs(os.path.join(experiment, "targets"), exist_ok=True)
for row in open(os.path.join(experiment, "checks.tsv")):
    if row.startswith("#") or not row.strip():
        continue
    check, source, line = row.rstrip("\n").split("\t")[:3]
    target = "adhoc-" + check
    path = os.path.join(tree, source)
    lines = open(path).read().split("\n")
    text = lines[int(line) - 1]
    if ANNOTATION not in text:
        if text.count("throw new ") != 1:
            sys.exit("%s:%s is not one `throw new`: %s" % (source, line, text.strip()))
        lines[int(line) - 1] = text.replace(
            "throw new ", 'throw new %s("%s") ' % (ANNOTATION, target))
        open(path, "w").write("\n".join(lines))
    elif '("%s")' % target not in text:
        sys.exit("%s:%s carries another target: %s" % (source, line, text.strip()))
    with open(os.path.join(experiment, "targets", check + ".yaml"), "w") as spec:
        spec.write("exception_target_id: %s\n" % target)
    print(check, "->", "%s:%s" % (os.path.basename(source), line))

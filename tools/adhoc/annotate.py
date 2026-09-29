#!/usr/bin/env python3
"""annotate.py <adhoc-experiment-dir> <tree> : annotates every check the
experiment's checks.tsv declares in <tree> --
@CausynthExceptionTarget("adhoc-<check>") on its throw, fully qualified and
on the throw's own line so no line number moves -- and writes the check's
targets/<check>.yaml.  A line already annotated with its own target is left
as it is; one annotated with another is refused.  A check whose annotation
moved (a merge added lines above it) is found by its annotation, and
checks.tsv follows it."""
import os
import sys

ANNOTATION = "@edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget"
experiment, tree = sys.argv[1], sys.argv[2]
os.makedirs(os.path.join(experiment, "targets"), exist_ok=True)
checks_tsv = os.path.join(experiment, "checks.tsv")
rows = open(checks_tsv).read().split("\n")
for index, row in enumerate(rows):
    if row.startswith("#") or not row.strip():
        continue
    fields = row.split("\t")
    check, source, line = fields[:3]
    target = "adhoc-" + check
    path = os.path.join(tree, source)
    lines = open(path).read().split("\n")
    tagged = [number + 1 for number, text in enumerate(lines)
              if '("%s")' % target in text]
    if len(tagged) == 1 and str(tagged[0]) != line:
        line = fields[2] = str(tagged[0])
        rows[index] = "\t".join(fields)
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
with open(checks_tsv, "w") as out:
    out.write("\n".join(rows))

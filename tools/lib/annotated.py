#!/usr/bin/env python3
"""annotated.py <system-dir> <tree> [<case>] : the throws a tree marks as a
known bug's target.

A tree marks the throw a known bug's case declares with GraphChecker's
annotation, its value the ids of the cases (comma-separated) whose target it
is:

    throw new @CausynthExceptionTarget("hdfs-17899-bug1,hdfs-17899-bug2")
        InvalidEncryptionKeyException(...);

With no <case>: one TSV row per (case, site), sorted:

    <case> <binary class name> <throw line> <tree-relative file> <thrown type>

With <case>: that case's target spec line, the one a case directory without
a target.yaml runs on (experiments/lib/run.sh):

    exception_target: <case> <binary class name> <throw line> [<thrown type>]

A case marked at no site, or at more than one, is refused.  The sources
scanned are the system's own (system.sh's system_sources).  The line is the
one the `throw new` starts on, which is where javac puts the `new` that
causynth.ExceptionTargetLineResolver finds in the compiled class; the class is
the file's top-level one, and the resolver also finds a throw nested in it.
The thrown type is stated only when another `throw new` starts on that line.
A marker on anything but a `throw new` is refused: nothing then says where its
case fails.

Also a module: sites() is what tools/adhoc/findings.py marks known bugs by."""
import os
import re
import subprocess
import sys

MARKER_NAME = "CausynthExceptionTarget"
# A string literal, and a constant made of literals joined by `+`.
_LITERAL = r'"(?:[^"\\]|\\.)*"'
_CONSTANT = r'%s(?:\s*\+\s*%s)*' % (_LITERAL, _LITERAL)
# `throw new [@Marker("...")] Type(`: the marker and the type may continue on
# the lines after the one the throw starts on.
THROW = re.compile(r'throw\s+new\s+(?:@[\w.$]+\s*(?:\(\s*%s\s*\))?\s*)?'
                   r'([\w.$]+)\s*[(<]' % _CONSTANT)
MARKER = re.compile(r'@(?:[\w$]+\.)*%s\s*\(\s*(%s)\s*\)' % (MARKER_NAME, _CONSTANT))
# How many lines after its first a throw's marker and type may take.
CONTINUATION = 3


def throw_matches(lines, index):
    """THROW's matches for the `throw new`s that start on lines[index], read
    on that line and the CONTINUATION lines after it (match.string)."""
    text = "\n".join(lines[index:index + 1 + CONTINUATION])
    found = (THROW.match(text, start.start())
             for start in re.finditer(r'throw\s+new\b', lines[index]))
    return [match for match in found if match]


def throws_at(lines, index):
    """The thrown types of the `throw new`s that start on lines[index]."""
    return [match.group(1) for match in throw_matches(lines, index)]


def sources(system_dir):
    """system.sh's system_sources: [(root name, tree-relative source dir)]."""
    entries = subprocess.run(
        ["bash", "-c",
         'source "$1/system.sh"; printf "%s\\n" "${system_sources[@]}"',
         "_", system_dir], check=True, capture_output=True,
        text=True).stdout.split()
    return [tuple(entry.split(":", 1)) for entry in entries]


def _marked_files(directory):
    found = subprocess.run(
        ["grep", "-rl", "--include=*.java", MARKER_NAME, directory],
        capture_output=True, text=True)
    if found.returncode > 1:
        raise SystemExit("grep %s failed: %s" % (directory, found.stderr))
    return sorted(found.stdout.split())


def sites(system_dir, tree):
    """Every marked throw of the tree's own sources, one dict per case it
    names: case, cls, line, file, type."""
    rows = []
    for _, relative in sources(system_dir):
        base = os.path.join(tree, relative)
        for path in _marked_files(base):
            text = open(path, errors="ignore").read()
            lines = text.split("\n")
            cls = os.path.relpath(path, base)[:-len(".java")].replace("/", ".")
            for marker in MARKER.finditer(text):
                where = "%s:%d" % (os.path.relpath(path, tree),
                                   text.count("\n", 0, marker.start()) + 1)
                throw = re.search(r'throw\s+(new)\s*$', text[:marker.start()])
                match = throw and THROW.match(text, throw.start())
                if not match:
                    raise SystemExit("%s: @%s marks no `throw new`"
                                     % (where, MARKER_NAME))
                names = "".join(re.findall(r'"((?:[^"\\]|\\.)*)"',
                                           marker.group(1)))
                cases = [name.strip() for name in names.split(",")
                         if name.strip()]
                if not cases:
                    raise SystemExit("%s: @%s names no case"
                                     % (where, MARKER_NAME))
                # The `new`'s line, the one javac numbers the throw by.
                line = text.count("\n", 0, throw.start(1))
                for case in cases:
                    rows.append({"case": case, "cls": cls, "line": line + 1,
                                 "file": os.path.relpath(path, tree),
                                 "type": match.group(1),
                                 "several": len(throws_at(lines, line)) > 1})
    return sorted(rows, key=lambda row: (row["case"], row["cls"], row["line"]))


def spec(system_dir, tree, case):
    """The case's `exception_target:` line, from its one marked site."""
    found = [row for row in sites(system_dir, tree) if row["case"] == case]
    if len(found) != 1:
        raise SystemExit("%s: %s marked site(s) in %s%s" % (
            case, len(found) or "no", tree,
            "".join("\n  %s:%d" % (row["file"], row["line"]) for row in found)))
    row = found[0]
    return "exception_target: %s %s %d%s" % (
        case, row["cls"], row["line"], " " + row["type"] if row["several"] else "")


def main():
    if len(sys.argv) not in (3, 4):
        raise SystemExit("usage: annotated.py <system-dir> <tree> [<case>]")
    system_dir, tree = sys.argv[1], sys.argv[2]
    if len(sys.argv) == 4:
        print(spec(system_dir, tree, sys.argv[3]))
        return
    for row in sites(system_dir, tree):
        print("\t".join(str(row[key])
                        for key in ("case", "cls", "line", "file", "type")))


if __name__ == "__main__":
    main()

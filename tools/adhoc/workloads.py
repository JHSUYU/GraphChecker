#!/usr/bin/env python3
"""workloads.py <system-dir> <repo> : the system's cluster tests, one
"<test class><TAB><method>" row each (workloads.tsv, what coverage.sh runs
and select.py reads), read off the compiled test classes (system.sh's
system_paths: test_classes) with a class-file reader.

A row is a JUnit 4 or Jupiter @Test method, declared or inherited from a
superclass among the test classes, that the engine's runner can call
(runtime.JUnitLifecycle: a concrete top-level class with a no-argument
constructor, a method whose one argument, if any, is Jupiter's TestInfo), of
a class that -- itself or a superclass among the test classes -- names the
system's cluster class (system.sh's system_cluster_class) in its constant
pool.  A method or class marked @Ignore or @Disabled is left out."""
import os
import struct
import subprocess
import sys

TEST = {"Lorg/junit/Test;", "Lorg/junit/jupiter/api/Test;"}
IGNORED = {"Lorg/junit/Ignore;", "Lorg/junit/jupiter/api/Disabled;"}
# The test method descriptors JUnitLifecycle calls.
CALLABLE = {"()V", "(Lorg/junit/jupiter/api/TestInfo;)V"}
ABSTRACT, INTERFACE = 0x0400, 0x0200


class ClassFile:
    """What the listing needs of one class file: its name, superclass,
    flags, every UTF-8 constant, its annotations, and its methods'."""

    def __init__(self, data):
        self.data, self.at = data, 10
        count = self.u2(8)
        self.utf8 = {}
        self.classes = {}
        index = 1
        while index < count:
            tag = data[self.at]
            self.at += 1
            if tag == 1:
                length = self.u2()
                self.utf8[index] = data[self.at:self.at + length].decode(
                    "utf-8", "replace")
                self.at += length
            elif tag == 7:
                self.classes[index] = self.u2()
            elif tag in (8, 16, 19, 20):
                self.at += 2
            elif tag == 15:
                self.at += 3
            elif tag in (3, 4, 9, 10, 11, 12, 17, 18):
                self.at += 4
            elif tag in (5, 6):
                self.at += 8
                index += 1
            else:
                raise ValueError("constant pool tag %d" % tag)
            index += 1
        self.flags = self.u2()
        self.name = self.class_name(self.u2())
        self.super = self.class_name(self.u2())
        interfaces = self.u2()
        self.at += 2 * interfaces
        for _ in range(self.u2()):  # fields
            self.at += 6
            self.attributes()
        self.methods = {}
        for _ in range(self.u2()):
            self.at += 2
            name, descriptor = self.utf8[self.u2()], self.utf8[self.u2()]
            self.methods[(name, descriptor)] = self.attributes()
        self.annotations = self.attributes()

    def u2(self, at=None):
        if at is not None:
            self.at = at
        value = struct.unpack_from(">H", self.data, self.at)[0]
        self.at += 2
        return value

    def class_name(self, index):
        return self.utf8[self.classes[index]] if index else ""

    def attributes(self):
        """The type descriptors of the runtime-visible annotations among
        the attributes read here."""
        found = set()
        for _ in range(self.u2()):
            name = self.utf8[self.u2()]
            length = struct.unpack_from(">I", self.data, self.at)[0]
            self.at += 4
            end = self.at + length
            if name == "RuntimeVisibleAnnotations":
                for _ in range(self.u2()):
                    found.add(self.utf8[self.u2()])
                    for _ in range(self.u2()):
                        self.at += 2
                        self.element_value()
            self.at = end
        return found

    def element_value(self):
        tag = chr(self.data[self.at])
        self.at += 1
        if tag == "e":
            self.at += 4
        elif tag == "@":
            self.at += 2
            for _ in range(self.u2()):
                self.at += 2
                self.element_value()
        elif tag == "[":
            for _ in range(self.u2()):
                self.element_value()
        else:
            self.at += 2


def main():
    system_dir, repo = sys.argv[1], sys.argv[2]
    declared = subprocess.run(
        ["bash", "-c", 'repo=$2; source "$1/system.sh"; system_paths; '
         'printf "%s\\n%s\\n" "${test_classes}" "${system_cluster_class}"',
         "_", system_dir, repo], check=True, capture_output=True,
        text=True).stdout.split("\n")
    root, cluster = declared[0], declared[1]
    classes = {}
    for directory, _, files in os.walk(root):
        for name in files:
            if name.endswith(".class"):
                with open(os.path.join(directory, name), "rb") as source:
                    parsed = ClassFile(source.read())
                classes[parsed.name] = parsed

    def lineage(parsed):
        while parsed is not None:
            yield parsed
            parsed = classes.get(parsed.super)

    rows = []
    for name, parsed in sorted(classes.items()):
        if "$" in name or parsed.flags & (ABSTRACT | INTERFACE) \
                or ("<init>", "()V") not in parsed.methods:
            continue
        chain = list(lineage(parsed))
        if not any(cluster in utf8 for c in chain for utf8 in c.utf8.values()) \
                or any(c.annotations & IGNORED for c in chain):
            continue
        seen = set()
        for c in chain:  # a subclass's own declaration wins
            for (method, descriptor), annotations in c.methods.items():
                if descriptor not in CALLABLE or method in seen:
                    continue
                seen.add(method)
                if annotations & TEST and not annotations & IGNORED:
                    rows.append("%s\t%s" % (name.replace("/", "."), method))
    for row in sorted(rows):
        print(row)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Keep all HBase classes in the Java 8 worktree, never in another checkout."""

import argparse
import os
import struct
import sys
import xml.etree.ElementTree as ET
from pathlib import Path
from zipfile import ZipFile


def check_class(path):
    data = Path(path).read_bytes()[:8]
    if len(data) != 8 or data[:4] != b"\xca\xfe\xba\xbe":
        raise ValueError("not a Java class: {}".format(path))
    major = struct.unpack(">H", data[6:8])[0]
    if major > 52:
        raise ValueError("Java {} bytecode is not usable on Java 8: {}".format(
            major, path))


def check_jar(path):
    with ZipFile(str(path)) as jar:
        for name in jar.namelist():
            if not name.endswith(".class") or name == "module-info.class" \
                    or name.startswith("META-INF/versions/"):
                continue
            with jar.open(name) as class_file:
                data = class_file.read(8)
            if len(data) == 8 and data[:4] == b"\xca\xfe\xba\xbe":
                major = struct.unpack(">H", data[6:8])[0]
                if major > 52:
                    raise ValueError("Java {} dependency in Java 8 classpath: {} ({})".format(
                        major, path, name))


def modules(root):
    by_artifact = {}
    for pom in root.rglob("pom.xml"):
        if "target" in pom.parts:
            continue
        tree = ET.parse(str(pom)).getroot()
        namespace = "{http://maven.apache.org/POM/4.0.0}"
        artifact = tree.findtext(namespace + "artifactId")
        if artifact:
            by_artifact[artifact] = pom.parent
    return by_artifact


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check-class")
    parser.add_argument("--worktree")
    parser.add_argument("--input")
    parser.add_argument("--output")
    args = parser.parse_args()
    if args.check_class:
        check_class(args.check_class)
        return
    if not all((args.worktree, args.input, args.output)):
        parser.error("--worktree, --input and --output are required")

    root = Path(args.worktree).resolve(strict=True)
    sibling = root.parent / "hbase"
    source = Path(args.input).read_text().strip()
    if not source:
        raise ValueError("Maven classpath is empty: {}".format(args.input))
    by_artifact = modules(root)
    server = root / "hbase-server" / "target"
    entries = [server / "test-classes", server / "classes"]
    for raw in source.split(os.pathsep):
        if not raw:
            continue
        path = Path(raw).resolve(strict=True)
        if path == sibling or sibling in path.parents:
            raise ValueError("Java 17 checkout path in classpath: {}".format(path))
        parts = path.parts
        # Maven may resolve locally installed HBase jars from another branch.
        # Use this worktree's compiled outputs instead. thirdparty jars are
        # distinct published dependencies and remain as Maven resolved them.
        try:
            index = next(i for i in range(len(parts) - 3)
                         if parts[i:i + 3] == ("org", "apache", "hbase"))
        except StopIteration:
            index = -1
        if index >= 0 and index + 3 < len(parts) and parts[index + 3] != "thirdparty":
            artifact = parts[index + 3]
            if artifact in by_artifact and path.suffix == ".jar":
                kind = "test-classes" if path.name.endswith("-tests.jar") else "classes"
                path = by_artifact[artifact] / "target" / kind
        if "target" in path.parts and path.name in ("classes", "test-classes") \
                and path != root and root not in path.parents:
            raise ValueError("foreign compiled classes in classpath: {}".format(path))
        if not path.exists():
            raise ValueError("classpath entry missing in Java 8 worktree: {}".format(path))
        if path.suffix == ".jar":
            check_jar(path)
        entries.append(path)
    unique = list(dict.fromkeys(str(path) for path in entries))
    Path(args.output).write_text(os.pathsep.join(unique) + "\n")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, ET.ParseError) as error:
        print("jdk8-pressure classpath: {}".format(error), file=sys.stderr)
        sys.exit(2)

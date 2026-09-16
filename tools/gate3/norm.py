#!/usr/bin/env python3
"""Canonicalise a GraphChecker artifact so two runs of the same corpus hash
alike.  Two, and only two, classes of difference are removed:

  * run-local absolute paths -- every mask given with --mask OLD=NEW is
    substituted textually in the serialised row;
  * fields named by --strip -- removed at every depth, by key name.

Everything else is preserved: keys are re-emitted in sorted order with no
whitespace, so a genuine change of value, of key set or of row count changes
the hash.  .jsonl rows are emitted one per line for the caller to `sort`;
nothing but one row is ever held in memory.
"""
import argparse
import json
import sys


def strip(node, names):
    if isinstance(node, dict):
        return {k: strip(v, names) for k, v in node.items() if k not in names}
    if isinstance(node, list):
        return [strip(v, names) for v in node]
    return node


def emit(node, names, masks, out):
    text = json.dumps(strip(node, names), sort_keys=True,
                      separators=(",", ":"), ensure_ascii=True)
    for old, new in masks:
        text = text.replace(old, new)
    out.write(text)
    out.write("\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("file")
    ap.add_argument("--jsonl", action="store_true")
    ap.add_argument("--strip", default="")
    ap.add_argument("--mask", action="append", default=[])
    args = ap.parse_args()
    names = {n for n in args.strip.split(",") if n}
    masks = []
    for spec in args.mask:
        old, _, new = spec.partition("=")
        if old:
            masks.append((old, new))
    masks.sort(key=lambda p: -len(p[0]))
    out = sys.stdout
    with open(args.file, "r", encoding="utf-8", errors="strict") as handle:
        if args.jsonl:
            for line in handle:
                line = line.strip()
                if line:
                    emit(json.loads(line), names, masks, out)
        else:
            emit(json.load(handle), names, masks, out)


if __name__ == "__main__":
    main()

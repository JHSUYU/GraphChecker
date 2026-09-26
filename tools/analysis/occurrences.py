#!/usr/bin/env python3
"""occurrences.py LOG [NODE] : the selector node/region/REGION.<id>#k of the first
observed target occurrence a discovery run's PLAN listed (DECLARED_TARGET_OCCURRENCE_MISSING),
on NODE when given; k counts that node and region's occurrences in listed order."""
import re, sys

log = open(sys.argv[1], errors="replace").read()
wanted = sys.argv[2] if len(sys.argv) > 2 else ""
listing = re.search(r"observed target occurrences: \[(.*?)\]\s*$", log, re.M)
if not listing:
    sys.exit("no observed target occurrences in " + sys.argv[1])
seen = {}
for address in re.findall(r"([^\s,\[]+#epoch\d+/region/REGION\.[0-9a-f-]+)", listing.group(1)):
    node = address.split("#epoch")[0]
    seen[address] = seen.get(address, 0) + 1
    if not wanted or node == wanted:
        print("%s#%d" % (address, seen[address]))
        break
else:
    sys.exit("no observed occurrence on " + wanted)

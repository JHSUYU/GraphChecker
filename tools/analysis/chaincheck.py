#!/usr/bin/env python3
"""chaincheck.py ROUND [BASELINE.json]: per case, the causal-chain signature of
candidate.smt2 (container ops, ite, arms, root groups, query) + the claim's moved
roots; with a baseline, prints what changed."""
import sys, os, re, json, glob, collections
CASES = ["11741","17897","17899-bug1","17899-bug2","17899-bug3","17960",
         "17967-pathA","17967-pathB","17967-pathC"]
def sig(rnd, case):
    base = os.path.expanduser(f"~/gc-out/accept-{rnd}-{case}/out/hdfs-{case}/schedule/final")
    f = os.path.join(base, "candidate.smt2")
    if not os.path.exists(f): return None
    t = open(f).read()
    s = collections.OrderedDict()
    for op in ["assoc_put","assoc_remove","assoc_has","assoc_read","assoc_size","store","select"]:
        s[op] = len(re.findall(r"\(" + op + r"[ )]", t))
    s["ite"] = t.count("(ite ")
    s["path_selectors"] = len(set(re.findall(r"path_selector__\d+__[0-9a-f]+", t)))
    s["message_arms"] = len(set(re.findall(r"message_arm__[A-Za-z0-9_]+", t)))
    s["writer_arms"] = len(set(re.findall(r"writer_arm__[A-Za-z0-9_]+", t)))
    decl = re.findall(r"\(declare-const (\S+) ", t)
    g = collections.Counter()
    for d in decl:
        if d.startswith(("identity","message_arm","path_selector","writer_arm")): continue
        m = re.match(r"([A-Z]_[A-Za-z]+_field_)?(REGION\.[0-9a-f]{8}|HOFF|SRC|[A-Za-z]+)", d)
        g[(m.group(1) or "") + (m.group(2) if m else d[:20])] += 1
    s["roots"] = dict(sorted(g.items()))
    s["fatal_target"] = ":named fatal_target" in t
    s["partition"] = ":named target_path_partition" in t
    s["check_sat"] = "(check-sat)" in t
    try:
        c = json.load(open(os.path.join(base, "claim.json")))["claim"] or {}
        s["moved"] = sorted(re.sub(r"(REGION\.[0-9a-f]{8})\S*", r"\1", k) for k in (c.get("movedRoots") or {}))
        s["finding"] = (json.load(open(os.path.join(base, "result.json"))).get("finding") or {}).get("kind", "")
    except Exception as e:
        s["moved"] = f"? {e}"
    return s
rnd = sys.argv[1]
cur = {c: sig(rnd, c) for c in CASES}
if len(sys.argv) > 2 and os.path.exists(sys.argv[2]):
    base = json.load(open(sys.argv[2]))
    for c in CASES:
        a, b = base.get(c), cur.get(c)
        if b is None: print(f"{c:12} NO SMT"); continue
        diff = {k: (a.get(k), b[k]) for k in b if a and a.get(k) != b[k]}
        print(f"{c:12} {'same' if not diff else ''}")
        for k, (x, y) in diff.items(): print(f"   {k}: {x} -> {y}")
else:
    print(json.dumps(cur, indent=1))

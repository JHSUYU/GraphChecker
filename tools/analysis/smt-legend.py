#!/usr/bin/env python3
"""smt-legend.py <case out dir> [--repo <system tree>] [--all]

Decodes the leaf symbols a campaign's final/candidate.smt2 declares, for checking its causal chain by hand
against the system's code: each root (its kind and category, the door or configuration it stands for, where it
was minted, the value the recording ran it at), each read (the node and region that read it, the site's class,
method and source line, the field the instruction reads, the value the run read), each handoff (the wire port,
the producer's node). Selectors and arms (`path_selector__`, `writer_arm__`, ...) are the formula's own and are
counted, not decoded. `--all` prints every symbol; by default the ones the asserted text names.

<case out dir> is `.../out/<case>` (it holds schedule/); the tree defaults to the `repo=` of the case's
case.sh as frozen in the run (`schedule/frozen-inputs`), else give --repo.
"""
import argparse
import glob
import json
import os
import re
import subprocess
import sys
from collections import defaultdict

JAVAP = '/usr/lib/jvm/java-8-openjdk-amd64/bin/javap'


def declared(smt):
    names = []
    for m in re.finditer(r'\(declare-(?:const|fun) (\|[^|]*\||\S+)', smt):
        names.append(m.group(1).strip('|'))
    return names


def asserted_names(smt):
    body = smt[smt.find('(assert'):] if '(assert' in smt else ''
    return set(n.strip('|') for n in re.findall(r'\|[^|]*\||[A-Za-z_][\w./$#@:\-]*', body))


class ClassIndex:
    """Class files of the tree's modules, javap'd once each: method -> {bci: (line, instruction)}."""

    def __init__(self, repo):
        self.dirs = []
        if repo:
            for depth in ('*', '*/*', '*/*/*', '*/*/*/*'):
                self.dirs += glob.glob(os.path.join(repo, depth, 'target', 'classes'))
                self.dirs += glob.glob(os.path.join(repo, depth, 'target', 'test-classes'))
        self.cache = {}

    def _file(self, cls):
        rel = cls.replace('.', '/') + '.class'
        for d in self.dirs:
            p = os.path.join(d, rel)
            if os.path.exists(p):
                return d
        return None

    def methods(self, cls):
        if cls in self.cache:
            return self.cache[cls]
        out = {}
        d = self._file(cls)
        if d:
            try:
                text = subprocess.run([JAVAP, '-c', '-l', '-p', '-s', '-cp', d, cls], capture_output=True,
                                      text=True, timeout=60).stdout
            except Exception:
                text = ''
            name = desc = None
            code = {}
            lines = []
            for ln in text.splitlines():
                m = re.match(r'^  (?:[\w<>\[\]$.,? ]+ )?([\w<>$]+)\((.*)\)[^;]*;$', ln)
                if m and not ln.startswith('    '):
                    name, desc, code, lines = m.group(1), None, {}, []
                    continue
                m = re.match(r'^    descriptor: (\S+)', ln)
                if m and name:
                    desc = m.group(1)
                    out[(name, desc)] = (code, lines)
                    continue
                m = re.match(r'^\s+(\d+): (.*)$', ln)
                if m and name and desc:
                    code[int(m.group(1))] = m.group(2)
                    continue
                m = re.match(r'^\s+line (\d+): (\d+)$', ln)
                if m and name and desc:
                    lines.append((int(m.group(2)), int(m.group(1))))
        self.cache[cls] = out
        return out

    def where(self, site, jtype=None):
        """'pkg.C#m(desc)R#unit:KIND' -> 'C.m{fields}': the site's unit index is Soot's, not a bytecode offset, so the
        field is named by the method's own field instructions of the read's type (one name, or the candidates)."""
        m = re.match(r'^([\w.$]+)#([\w<>$]+)(\([^)]*\)\S*?)#(\d+)(?::(\w+))?$', site or '')
        if not m:
            return site or '?'
        cls, meth, desc = m.group(1), m.group(2), m.group(3)
        short = cls.rsplit('.', 1)[-1]
        found = self.methods(cls).get((meth, desc))
        if not found:
            return f'{short}.{meth}'
        code, lines = found
        fields = set()
        for ins in code.values():
            f = re.search(r'(?:get|put)(?:field|static).*// Field (\S+):(\S+)', ins)
            if f and (not jtype or f.group(2) == jtype or (jtype.startswith('L') and f.group(2).startswith('L'))):
                fields.add(f.group(1))
        span = f':{min(l for _, l in lines)}-{max(l for _, l in lines)}' if lines else ''
        return f'{short}.{meth}{span}' + ('{' + ','.join(sorted(fields)) + '}' if fields else '')


def occ(o):
    if not o:
        return '?'
    idx = o.get('index') or []
    entry = idx[0].get('callSite', '') if idx else ''
    m = re.search(r': [^ ]+ ([\w<>$]+)\(', entry)
    cls = re.search(r'<([\w.$]+):', entry)
    where = (cls.group(1).rsplit('.', 1)[-1] + '.' + m.group(1)) if (m and cls) else entry[:60]
    ctx = o.get('context', {})
    form = ctx.get('form', '?')
    return f"{o.get('node', '?').split('/')[-1]} {where} [{form}{'/' + ctx.get('role', '') if form == 'ROOT' else ''}]"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('out')
    ap.add_argument('--repo')
    ap.add_argument('--all', action='store_true')
    a = ap.parse_args()
    sched = os.path.join(a.out, 'schedule')
    smt = open(os.path.join(sched, 'final', 'candidate.smt2')).read()
    names = declared(smt)
    used = asserted_names(smt)
    leaves = [n for n in names if not re.match(r'^(path_selector|writer_arm|message_arm|state_arm|decided|wchoice|'
                                                 r'observed_arm|nullRef|valuation)', n)]
    if not a.all:
        leaves = [n for n in leaves if n in used]
    want = set(leaves)
    repo = a.repo
    if not repo:
        for f in glob.glob(os.path.join(sched, 'frozen-inputs', '*')):
            try:
                t = open(f, errors='ignore').read(200000)
            except Exception:
                continue
            m = re.search(r'project_repo=(\S+)', t)
            if m:
                repo = m.group(1)
                break
    ci = ClassIndex(repo)
    sess = os.path.join(sched, 'iteration-0000', 'sessions')
    rows = {}
    for sd in sorted(glob.glob(os.path.join(sess, '*'))):
        for kind in ('roots', 'reads', 'attaches'):
            p = os.path.join(sd, kind + '.jsonl')
            if not os.path.exists(p):
                continue
            with open(p) as fh:
                for line in fh:
                    m = re.search(r'"symbol":"([^"]*)"', line)
                    if m and m.group(1) in want and m.group(1) not in rows:
                        rows[m.group(1)] = (kind, json.loads(line))
    plan = {}
    tp = os.path.join(sched, 'iteration-0000', 'execution_task_plan.jsonl')
    if os.path.exists(tp):
        with open(tp) as fh:
            for line in fh:
                if '"inputActions"' not in line:
                    continue
                for ia in json.loads(line).get('inputActions', []):
                    plan.setdefault(ia.get('portId'), ia)
    moved = {}
    try:
        moved = json.load(open(os.path.join(sched, 'final', 'claim.json'))).get('claim', {}).get('movedRoots', {}) or {}
    except Exception:
        pass
    anchored = {}
    try:
        for root in json.load(open(os.path.join(sched, 'final', 'candidate_composition_manifest.json'))).get('roots', []):
            anchored.setdefault(root.get('rootId'), root.get('recordedValue'))
    except Exception:
        pass
    print(f'# {a.out}\n# tree {repo}\n# {len(names)} declared, {len(leaves)} leaves shown, moved roots: {len(moved)}')
    groups = defaultdict(list)
    for n in leaves:
        kind, r = rows.get(n, (None, None))
        if kind == 'roots':
            ia = plan.get(r.get('rootId'), {})
            door = ia.get('marker') or ia.get('declaredCallee', '')
            site = ia.get('siteId', '')
            key = n if n in moved else r.get('rootId')
            mv = ' MOVED=' + str(moved[key]) if key in moved else ''
            recorded = anchored.get(r.get('rootId'), r.get('recordedValue'))
            ran = '' if recorded == r.get('recordedValue') else f" (this session ran {r.get('recordedValue')})"
            groups['ROOT'].append(f"{r.get('category', '?')}/{r.get('kind', '?')} {door} at {site} | {occ(r.get('occurrence'))} | "
                                  f"recorded={recorded}{ran}{mv} | {n[:90]}")
        elif kind == 'reads':
            e = r.get('endpoint', {})
            loc = r.get('location', {})
            groups['READ'].append(f"{ci.where(e.get('site'), r.get('javaType'))} | {occ(e.get('occurrence'))} | {loc.get('kind')} "
                                  f"{loc.get('owner', '')}#{loc.get('slot', '')} {r.get('javaType', '')} v{r.get('observedVersion')}"
                                  f" = {r.get('concreteValue')} | {n[:70]}")
        elif kind == 'attaches':
            e = r.get('endpoint', {})
            p = r.get('producer') or {}
            groups['HANDOFF'].append(f"{e.get('site', '?')} | {occ(e.get('occurrence'))} <- {occ(p.get('occurrence'))} | "
                                     f"arrival={r.get('arrival')} answered={r.get('answered')} | {n[:70]}")
        else:
            m = re.match(r'^M_J_field_(REGION\.[^.]+\.in\.[^.]+)', n)
            if m and m.group(1) in plan:
                ia = plan[m.group(1)]
                groups['CLOCK'].append(f"{ia.get('marker') or ia.get('declaredCallee', '')} at {ia.get('siteId', '')} | "
                                       f"{ia.get('sourceKey', '')} | {n[:90]}")
            else:
                groups['OTHER'].append(n)
    for g in ('ROOT', 'CLOCK', 'HANDOFF', 'READ', 'OTHER'):
        if groups[g]:
            print(f'\n## {g} ({len(groups[g])})')
            for line in groups[g]:
                print('  ' + line)
    sel = defaultdict(int)
    for n in names:
        m = re.match(r'^(path_selector|writer_arm|message_arm|state_arm|decided|wchoice|observed_arm)', n)
        if m:
            sel[m.group(1)] += 1
    print('\n## formula selectors: ' + ', '.join(f'{k} {v}' for k, v in sorted(sel.items())))


if __name__ == '__main__':
    sys.exit(main())

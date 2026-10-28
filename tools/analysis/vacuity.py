#!/usr/bin/env python3
"""Whether a finished run's UNSAT is substantive or vacuous (read-only, offline).

An UNSAT is vacuous when nothing in the formula could have reached the fatal
arm whatever the exploration did: the fatal arm is literal false, the guard was
decided with no term, or the guard's slice holds no root and no read some other
writer could have answered.  Per check (<round>/out/<case>/) it reads

  schedule/final/candidate_composition_manifest.json   the composed paths
  schedule/final/candidate.smt2       each path_fatal__N, folded over literals
  schedule/final/claim.json, result.json, gaps.json
  static_scope_map.jsonl              the TARGET_SITE's guards
  schedule/iteration-*/sessions/<path session>/  targets, decisions,
                                      expressions, reads, writes, roots

and prints, per check: the paths and their phi (folded: false, true, unstated,
symbolic), the guard decisions' terms per ordinal (how many empty), every read
location in the slice of the guard terms and the phi (the observed version's
written value included) with its writer family -- the distinct non-initial
writer occurrences of that location in the path's session, plus INITIAL -- and
whether any writer is non-INITIAL, the roots in that slice, the claim's moved
roots, the BLOCKING gap codes and the named gap kinds, and a verdict.  A read
is free when the composer could offer it another writer than the observed one
(smt.Arms#stateArms and #eligible): not a constructor's write, not LOST, not
the reader's occurrence or thread, nor any write between it and the observed
version; the ancestry and event-order tests are not repeated, so "free"
over-approximates.  A path is free when its slice holds a root or a free read,
or its phi is true.

Usage: vacuity.py [--latest] [--detail] DIR|GLOB ...
  DIR is a round (contains out/) or a check (contains schedule/).  --latest
  keeps, per case, the newest round whose summary.tsv has a row.
"""
import argparse
import collections
import glob
import gzip
import json
import os
import re
import sys

NAMED_GAPS = ('UNSTATED_VALUE', 'LINEAGE_LOST', 'OCCURRENCE_ANCHOR_UNMATCHED',
              'ENUM_OPERAND_PINNED', 'REF_OPERAND_UNSTATED',
              'ORDERED_MAP_UNMODELED')
MARKS = {'ORDERED_MAP_UNMODELED': 'ordered-map-unmodeled'}
EXPR = re.compile(r'EXPR\.[0-9a-f]+')
UNSAT = ('UNSAT_CLOSED', 'RUN_DEFECT')
THREAD_ENTRY = re.compile(r'#u\d+$|: void run\(\)>$')


def rows(path):
    if not os.path.exists(path):
        return
    with (gzip.open(path, 'rt') if path.endswith('.gz') else open(path)) as f:
        try:
            for line in f:
                if line.strip():
                    try:
                        yield json.loads(line)
                    except ValueError:
                        continue
        except EOFError:
            return


def load(path):
    if not os.path.exists(path):
        return {}
    with open(path) as f:
        return json.load(f)


def tokens(text):
    for m in re.finditer(r'\|[^|]*\||"(?:[^"]|"")*"|;[^\n]*|[()]|[^\s()|";]+',
                         text):
        t = m.group(0)
        if not t.startswith(';'):
            yield t


def parse(text):
    stack = [[]]
    for t in tokens(text):
        if t == '(':
            stack.append([])
        elif t == ')':
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(t)
    return stack[0]


def fold(term, defs):
    """A boolean term with its literal parts folded: 'true', 'false' or the
    term."""
    if isinstance(term, str):
        body = defs.get(term)
        return fold(body, defs) if body in ('true', 'false') else term
    if not term:
        return term
    op, args = term[0], term[1:]
    if op == '!':
        return fold(args[0], defs)
    if op in ('and', 'or'):
        unit, zero = ('true', 'false') if op == 'and' else ('false', 'true')
        kept = []
        for a in args:
            f = fold(a, defs)
            if f == zero:
                return zero
            if f != unit:
                kept.append(f)
        return unit if not kept else kept[0] if len(kept) == 1 else [op] + kept
    if op == 'not':
        f = fold(args[0], defs)
        return {'true': 'false', 'false': 'true'}.get(f, ['not', f]) \
            if isinstance(f, str) else ['not', f]
    if op == '=>':
        a, b = fold(args[0], defs), fold(args[1], defs)
        if a == 'false' or b == 'true':
            return 'true'
        return b if a == 'true' else ['=>', a, b]
    if op == 'ite':
        c = fold(args[0], defs)
        if c in ('true', 'false'):
            return fold(args[1] if c == 'true' else args[2], defs)
    return term


def atoms(term, out):
    if isinstance(term, str):
        out.add(term)
    else:
        for t in term:
            atoms(t, out)
    return out


def symbol_class(name):
    if name.startswith('path_selector__'):
        return None
    if 'REGION.' in name and '.in.' in name:
        return 'ROOT'
    if name.startswith('identity__'):
        return 'IDENTITY'
    if '@v' in name:
        return 'READ'
    return re.split(r'__|[_/]', name.strip('|'))[0] or 'OTHER'


def smt_paths(path):
    """path_fatal__N -> (literal false?, symbol class counts)."""
    if not os.path.exists(path):
        return None
    with open(path) as f:
        commands = parse(f.read())
    defs, declared, found = {}, set(), {}
    for c in commands:
        if not isinstance(c, list) or not c:
            continue
        if c[0] in ('declare-fun', 'declare-const'):
            declared.add(c[1])
        elif c[0] == 'define-fun':
            defs[c[1]] = c[4]
    memo = {}

    def free(name, seen):
        if name in memo:
            return memo[name]
        if name in declared:
            memo[name] = {name}
        elif name in defs and name not in seen:
            seen.add(name)
            memo[name] = set().union(*[free(a, seen) for a in atoms(
                defs[name], set())])
        else:
            memo[name] = set()
        return memo[name]

    for c in commands:
        if (isinstance(c, list) and c and c[0] == 'assert'
                and isinstance(c[1], list) and c[1][0] == '!'
                and str(c[1][-1]).startswith('path_fatal__')):
            body = c[1][1]
            body = body[2] if isinstance(body, list) and body[0] == '=>' else body
            folded = fold(body, defs)
            names = set()
            for a in atoms(folded, set()):
                names |= free(a, set())
            found[c[1][-1]] = (folded == 'false', collections.Counter(
                filter(None, map(symbol_class, names))))
    return found


class Session(object):
    @staticmethod
    def find(camp, sid):
        hits = glob.glob(os.path.join(camp, 'schedule', 'iteration-*',
                                      'sessions', sid, ''))
        return hits[0] if hits else None

    @staticmethod
    def path(camp, sid, name):
        """A session file, gzipped or (an older run) plain; '' without the
        session."""
        found = Session.find(camp, sid)
        if not found:
            return ''
        path = os.path.join(found, name)
        return path if os.path.exists(path) else path[:-len('.gz')]

    def __init__(self, camp, sid):
        self.dir = Session.find(camp, sid)
        self.nodes, self.refs = {}, {}
        self.roots, self.reads, self.writes = {}, {}, collections.defaultdict(list)
        if not self.dir:
            return
        for r in rows(self.file('expressions.jsonl.gz')):
            if 'expression' in r:
                self.nodes[r['node']] = r['expression']
            elif 'ref' in r:
                self.refs[r['ref']] = r['node']
        for r in rows(self.file('roots.jsonl.gz')):
            self.roots[r.get('symbol', '')] = r.get('category', '?')
        for r in rows(self.file('reads.jsonl.gz')):
            if 'seq' in r:
                self.reads[r['seq']] = r
        for r in rows(self.file('writes.jsonl.gz')):
            if 'location' in r:
                self.writes[loc_key(r['location'])].append(r)
        self.threads = {json.dumps(r['occurrence'], sort_keys=True): r.get('threadKey') or ''
                        for r in rows(self.file('activations.jsonl.gz')) if 'occurrence' in r}

    def file(self, name):
        path = os.path.join(self.dir or '', name)
        return path if os.path.exists(path) else path[:-len('.gz')]

    def slice(self, term):
        """(root symbols, read nodes, leaf type counts) under a term."""
        roots, reads, leaves = {}, {}, collections.Counter()
        stack = [self.refs[r] for r in EXPR.findall(term) if r in self.refs]
        seen = set()
        while stack:
            n = stack.pop()
            if n in seen or n not in self.nodes:
                continue
            seen.add(n)
            e = self.nodes[n]
            kind = e.get('_type')
            if kind == 'SymbolExpression':
                name = e.get('_exp', '')
                if name in self.roots or ('REGION.' in name and '.in.' in name):
                    roots[name] = self.roots.get(name, 'PORT')
                else:
                    leaves['OBJECT' if name.startswith('M_L') else
                           'NULL' if name == 'N' else 'SYMBOL'] += 1
            elif kind == 'ReadFromExpression':
                reads[e.get('readEventId')] = e
            elif kind in ('ConstExpr', 'ConStringSymbolExp'):
                leaves['CONST'] += 1
            stack.extend(children(e))
        return roots, reads, leaves

    def family(self, read):
        """(label, family size, any non-initial writer?, another writer
        offered?, observed version kind)."""
        row = self.reads.get(read.get('readEventId'))
        site = read.get('site') or {}
        label = '%s.%s@%s' % (site.get('className', '?').split('/')[-1],
                              site.get('methodName', '?'), site.get('bci', '?'))
        observed = (read.get('observedVersion') or {}).get('versionKind', '?')
        if row is None:
            location = read.get('location') or {}
            return ('%s %s#%s' % (label, location.get('locationKind', '?'),
                                  location.get('slot', '?')),
                    '?', False, False, observed)
        location = row['location']
        writes = self.writes.get(loc_key(location), [])
        writers = {occurrence_id(w) for w in writes if not w.get('initial')}
        initial = observed == 'INITIAL' or any(w.get('initial') for w in writes)
        offered = any(eligible(w, writes, row, self.threads)
                      for w in arms(writes, row))
        return ('%s %s#%s' % (label, location.get('kind'), location.get('slot')),
                len(writers) + (1 if initial else 0), bool(writers), offered,
                observed)


def arms(writes, read):
    """The writes smt.Arms#stateArms considers: every INITIAL one, and per
    writer occurrence its observed write, else its latest."""
    observed = read.get('observedVersion')
    held = {}
    for w in writes:
        if w.get('initial'):
            yield w
            continue
        key = occurrence_id(w)
        h = held.get(key)
        if h is None or h.get('version') != observed and (
                w.get('version') == observed or order(h) < order(w)):
            held[key] = w
    for w in held.values():
        yield w


def order(write):
    return (write.get('seq', 0), write.get('tie', 0))


def eligible(state, writes, read, threads):
    """smt.Arms#eligible for another writer than the observed one, with
    concurrency approximated as another occurrence on another thread, neither
    LOST (the ancestry and order tests are not repeated: over-approximate)."""
    observed = read.get('observedVersion')
    if state.get('version') == observed:
        return False
    reader = occurrence_id(read)
    thread = threads.get(reader, '')

    def blocks(w):
        writer = occurrence_id(w)
        return (constructs(w) or lost(w) or writer == reader
                or thread != '' and threads.get(writer) == thread)

    if not state.get('initial') and blocks(state):
        return False
    low, high = sorted((state.get('version', 0), observed))
    return not any(blocks(w) for w in writes if not w.get('initial')
                   and low < w.get('version', 0) <= high)


def lost(write):
    context = ((write.get('endpoint') or {}).get('occurrence') or {}).get('context') or {}
    return context.get('form') == 'LOST'


def constructs(write):
    endpoint = write.get('endpoint') or {}
    if '<init>(' in endpoint.get('site', '') or '<clinit>(' in endpoint.get('site', ''):
        return True
    for frame in reversed(endpoint.get('siteIndex') or []):
        site = frame.get('callSite', '')
        if '<init>(' in site or '<clinit>(' in site:
            return True
        if THREAD_ENTRY.search(site):
            return False
    return False


def children(e):
    if isinstance(e, dict):
        if e.get('_type') == 'SessionExpressionNode':
            yield e['node']
            return
        for v in e.values():
            for c in children(v):
                yield c
    elif isinstance(e, list):
        for v in e:
            for c in children(v):
                yield c


def loc_key(location):
    return (location.get('kind'), location.get('owner'), location.get('slot'))


def occurrence_id(row):
    return json.dumps((row.get('endpoint') or {}).get('occurrence'),
                      sort_keys=True)


def target_guards(camp):
    guards = set()
    for r in rows(os.path.join(camp, 'static_scope_map.jsonl')):
        if r.get('role') == 'TARGET_SITE':
            guards.update(r.get('guards') or ())
    return guards


def analyze(camp, summary):
    final = os.path.join(camp, 'schedule', 'final')
    manifest = load(os.path.join(final, 'candidate_composition_manifest.json'))
    result = load(os.path.join(final, 'result.json'))
    claim = load(os.path.join(final, 'claim.json')).get('claim') or {}
    gaps = load(os.path.join(final, 'gaps.json'))
    out = {'case': os.path.basename(camp), 'round': summary.get('round', '-'),
           'claim': summary.get('claim') or result.get('claim') or 'MISSING',
           'solver': result.get('solverState') or summary.get('plain') or '-',
           'paths': [], 'reads': {}, 'roots': collections.Counter(),
           'leaves': collections.Counter()}
    out['moved'] = sorted(claim.get('movedRoots') or {})
    out['blocking'] = collections.Counter(
        g.get('code') for g in gaps.get('gaps') or [])
    out['named'] = named((gaps.get('gaps') or []) + (gaps.get('telemetryGaps') or []))
    smt = smt_paths(os.path.join(final, 'candidate.smt2')) or {}
    guards = target_guards(camp)
    for ordinal, p in enumerate(manifest.get('paths') or []):
        s = Session(camp, p['sessionId'])
        target = next((r for r in rows(s.file('targets.jsonl.gz'))
                       if r.get('seq') == p.get('cutoff')), None) if s.dir else None
        phi = (target or {}).get('phiTerm', '').strip()
        reached = bool((target or {}).get('reachedAnchor'))
        occurrence = json.dumps((target or {}).get('occurrence'), sort_keys=True)
        decisions = [r for r in rows(s.file('decisions.jsonl.gz'))
                     if r.get('siteId') in guards and r.get('seq', 0) <= p.get('cutoff', 0)
                     and json.dumps(r.get('occurrence'), sort_keys=True) == occurrence] \
            if s.dir and target else []
        terms = ' '.join([phi] + [d.get('term', '') for d in decisions])
        roots, reads, leaves = s.slice(terms)
        free = bool(roots) or phi_kind(phi, target) == 'true'
        for read in reads.values():
            label, size, non_initial, offered, observed = s.family(read)
            free |= offered
            entry = out['reads'].setdefault(label, {
                'sizes': set(), 'nonInitial': False, 'offered': 0,
                'observed': set(), 'paths': 0})
            entry['sizes'].add(size)
            entry['nonInitial'] |= non_initial
            entry['offered'] += offered
            entry['observed'].add(observed)
            entry['paths'] += 1
        out['roots'].update(roots.values())
        out['leaves'].update(leaves)
        literal, symbols = smt.get('path_fatal__%d' % ordinal, (None, {}))
        out['paths'].append({
            'session': p['sessionId'], 'reached': reached,
            'phi': phi_kind(phi, target),
            'literalFalse': literal, 'smtSymbols': symbols,
            'decisions': [(d.get('siteId', '').rsplit('#', 1)[-1], d.get('ordinal'),
                           d.get('outcome'), bool(d.get('term'))) for d in decisions],
            'roots': sorted(roots), 'reads': len(reads), 'free': free})
    sessions = {p['sessionId'] for p in manifest.get('paths') or []}
    sessions.add(manifest.get('seedSessionId', ''))
    out['namedOnPaths'] = named(g for sid in sorted(filter(None, sessions))
                                for g in rows(Session.path(camp, sid, 'gaps.jsonl.gz')))
    out['verdict'] = verdict(out)
    return out


def phi_kind(phi, target):
    """missing (no target row at the cutoff), unstated, true, false, symbolic
    (names an expression) or constant."""
    if target is None:
        return 'missing'
    if not phi:
        return 'unstated'
    terms = parse(phi)
    folded = fold(terms[0], {}) if len(terms) == 1 else phi
    if folded in ('true', 'false'):
        return folded
    return 'symbolic' if EXPR.search(phi) else 'constant'


def named(gaps):
    """The named kinds among gap rows: a row's code, or its subject or detail
    naming the kind (a VM marker, a task's unanswered address)."""
    found = collections.Counter()
    for g in gaps:
        code = g.get('code') or g.get('kind')
        text = '%s %s' % (g.get('subject', ''), g.get('detail', ''))
        for kind in NAMED_GAPS:
            if code == kind or kind in text or MARKS.get(kind, kind) in text:
                found[kind] += 1
    return found


def verdict(c):
    if c['claim'] not in UNSAT and c['solver'] != 'unsat':
        return 'no UNSAT (claim=%s)' % c['claim']
    rest = ' (rests on BLOCKING %s)' % ','.join(sorted(c['blocking'])) if c['blocking'] else ''
    paths = c['paths']
    if not paths:
        return 'UNSAT is vacuous because no composed path reached the anchor' + rest
    n = len(paths)
    literal = sum(1 for p in paths if p['literalFalse'])
    if literal == n:
        phis = collections.Counter(p['phi'] for p in paths)
        return ('UNSAT is vacuous because every path\'s fatal arm is literal false '
                '(target phi %s)' % pairs(phis)) + rest
    open_paths = [p for p in paths if not p['literalFalse']]
    if all(not any(t for _, _, _, t in p['decisions']) and p['phi'] != 'symbolic'
           for p in open_paths):
        return ('UNSAT is vacuous because the guard decision has no term on any '
                'path not literal false (%d of %d literal false)' % (literal, n)) + rest
    free = [p for p in open_paths if p['free']]
    if not free:
        sizes = collections.Counter(max(r['sizes'], key=str) for r in c['reads'].values())
        why = ('no read in the guard\'s slice' if not c['reads'] else
               'no read in the guard\'s slice offered another writer (family sizes %s, '
               'non-INITIAL writers at %d of %d)' % (
                   pairs(sizes), sum(1 for r in c['reads'].values() if r['nonInitial']),
                   len(c['reads'])))
        return ('UNSAT is vacuous because no root and %s on any path (NO_ROOT; '
                '%d of %d literal false)' % (why, literal, n)) + rest
    return ('UNSAT is substantive: %d of %d paths free (roots %s; reads offered '
            'another writer %d)' % (len(free), n, pairs(c['roots']) or '0',
                                    sum(1 for r in c['reads'].values() if r['offered']))) + rest


def pairs(counter):
    return ','.join('%s=%s' % (k, v) for k, v in sorted(counter.items(), key=str))


def summary_row(round_dir, case):
    path = os.path.join(round_dir, 'summary.tsv')
    found = list(rows_tsv(path))
    for r in found:
        if r.get('case') == case:
            r['round'] = os.path.basename(round_dir)
            return r
    return {'round': os.path.basename(round_dir)}


def rows_tsv(path):
    if not os.path.exists(path):
        return
    with open(path) as f:
        header = f.readline().rstrip('\n').split('\t')
        for line in f:
            if line.strip():
                yield dict(zip(header, line.rstrip('\n').split('\t')))


def checks(args, latest):
    found = []
    for arg in args:
        for path in sorted(glob.glob(arg)) or [arg]:
            if os.path.isdir(os.path.join(path, 'out')):
                for camp in sorted(glob.glob(os.path.join(path, 'out', '*', ''))):
                    found.append((path.rstrip('/'), camp.rstrip('/')))
            elif os.path.isdir(os.path.join(path, 'schedule')):
                camp = path.rstrip('/')
                found.append((os.path.dirname(os.path.dirname(camp)), camp))
    if not latest:
        return found
    best = {}
    for round_dir, camp in found:
        case = os.path.basename(camp)
        summary = os.path.join(round_dir, 'summary.tsv')
        if not any(r.get('case') == case for r in rows_tsv(summary)):
            continue
        when = os.path.getmtime(summary)
        if case not in best or when > best[case][0]:
            best[case] = (when, round_dir, camp)
    return [(r, c) for _, r, c in sorted(best.values(), key=lambda b: b[2])]


def main():
    sys.setrecursionlimit(100000)
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    parser.add_argument('dirs', nargs='+')
    parser.add_argument('--latest', action='store_true')
    parser.add_argument('--detail', action='store_true')
    args = parser.parse_args()
    print('\t'.join(('round', 'case', 'claim', 'solver', 'paths', 'literalFalse',
                     'phi', 'guard terms/decisions', 'roots', 'reads offered/all', 'moved',
                     'BLOCKING', 'named gaps', 'named on paths', 'verdict')))
    for round_dir, camp in checks(args.dirs, args.latest):
        c = analyze(camp, summary_row(round_dir, os.path.basename(camp)))
        paths = c['paths']
        decisions = [d for p in paths for d in p['decisions']]
        free_reads = sum(1 for r in c['reads'].values() if r['offered'])
        print('\t'.join((
            c['round'], c['case'], c['claim'], c['solver'], str(len(paths)),
            str(sum(1 for p in paths if p['literalFalse'])),
            pairs(collections.Counter(p['phi'] for p in paths)) or '-',
            '%d/%d' % (sum(1 for d in decisions if d[3]), len(decisions))
            if decisions else 'phi only' if paths else '-',
            pairs(c['roots']) or '0', '%d/%d' % (free_reads, len(c['reads'])),
            str(len(c['moved'])), pairs(c['blocking']) or '0',
            pairs(c['named']) or '0', pairs(c['namedOnPaths']) or '0', c['verdict'])))
        if args.detail:
            for label, r in sorted(c['reads'].items()):
                print('    read %s family=%s nonInitial=%s offered=%d/%d observed=%s' % (
                    label, '/'.join(map(str, sorted(r['sizes'], key=str))),
                    r['nonInitial'], r['offered'], r['paths'],
                    ','.join(sorted(r['observed']))))
            for ordinal, p in enumerate(paths):
                print('    path %d %s reached=%s phi=%s literalFalse=%s free=%s '
                      'guard=%s roots=%d reads=%d smt=%s' % (
                          ordinal, p['session'], p['reached'], p['phi'],
                          p['literalFalse'], p['free'],
                          ' '.join('%s/o%s=%s%s' % (s, o, 'T' if v else 'F',
                                                    '' if t else '(no term)')
                                   for s, o, v, t in p['decisions']) or '-',
                          len(p['roots']), p['reads'], pairs(p['smtSymbols']) or '0'))
            if c['moved']:
                print('    moved ' + ' '.join(c['moved']))
            if c['leaves']:
                print('    leaves ' + pairs(c['leaves']))


if __name__ == '__main__':
    sys.exit(main())

#!/usr/bin/env python3
"""Root coverage of recorded campaigns: why a check stays concrete (R1-ROOTS WP0).

Offline, over what a round retained: no replay, no Java.  A check is one
campaign directory <round>/out/<case>/.  Per check it reads

  schedule/iteration-*/sessions/*/        manifest.json, targets.jsonl.gz,
                                          roots.jsonl.gz, reads.jsonl.gz (mint rows)
  schedule/iteration-*/obligation_results.jsonl       which sessions ADMITTED
  schedule/iteration-*/{,seed-replay/,obligations-*/*/}execution_task_plan.jsonl
                                          a root's port -> the input it declares
  schedule/iteration-*/obligations-NNNN/obligations.jsonl
  schedule/iteration-0000/ (else runtime/) concolic_region_plan.jsonl
  schedule/final/result.json, gaps.json
  static_scope_map.jsonl, candidate_dataflow_edges.jsonl.gz
  <round>/logs/<case>.log                 stage reached, maxJobs; the fallback
                                          for M-b and M-d when files are gone

and prints the metrics of R1-ROOTS-proposal.md section 8:

  M-a  anchor TargetRows (reachedAnchor) with a phiTerm / observedFatal, in the
       SEED session and in every admitted session (seed + ADMITTED
       obligations); "disk" counts every session on disk.  The check is
       CONCRETE when every admitted anchor row has an empty phiTerm and
       !observedFatal (Composer's "decided concretely" refusal), SYMBOLIC when
       one has a phiTerm, FATAL when one observed the fatal arm, UNREACHED when
       none reached the anchor.
  M-b  obligations wave 0 asked; waves that asked any.
  M-c  roots (distinct rootId) / mints (rows) per category over admitted
       sessions: each root row's own category (CLOCK, FAULT, CONFIG, READ,
       HOOK; a round recorded before the category contract states none and is
       refused by name), and READ also for a placeholder read, mintVersion,
       with no root row (an unattributed region input).
  M-d  PLAN admissions by admissionBasis (none = TARGET_REACHABLE, as
       ConcolicScheduler counts) and closure size / schedule_max_jobs; when PLAN
       refused the closure over the cap, both come from the log's refusal.
       "moved": the basis the plan admitted each occurrence under that minted a
       root the final claim moved (claim.json movedRoots, matched by rootId or
       symbol to roots.jsonl rows), "-" for one the seed plan does not hold (an
       occurrence GROW exposed).
  M-e  "decided concretely" refusals in final/gaps.json; final findingKind.
  M-f  the boundary walk of proposal 2.1, statically: backward BFS over the
       candidate edges (toCell <- fromCell) from the fromCells of the
       exception_guard edges at the TARGET_SITE's deciding guards, nearest
       first, every path stopped at its first boundary, at most 16 edges.
       Classes: mintable CLOCK, FAULT, CONFIG_CALL, CONFIG_FIELD, READ, TRACK;
       named-only TRACK_IDENTITY, TRACK_CONTAINER, PRE_WINDOW, WIRE, SCOPE, IO,
       and LIBRARY (an unmodeled library result no other class covers).
       "Blocked by" is the named-only classes found, nearest first
       (MINTABLE_ONLY when only mintable ones were, NO_BOUNDARY when none); the
       aggregate splits it by anchor verdict, and its CONCRETE row is the
       proposal's metric.
       "demand": the same histogram from the engine's own classification,
       root_demand.jsonl beside the scope map (proposal 2.1: one row per
       boundary with its `class` and `distance`), for a campaign that has one.
  static roots: DECLARED_SITE rows by inputKind, and how many sit in the fatal
       cone (backward from the throw) and the predicate cone (backward from the
       guard operands), both unbounded over every edge.

Static approximations (M-f):
- Every edge kind is walked, guard (control) edges too as ScopeFrontier#walk
  does, except a receiver edge (accessor/method/constructor/dispatch): it
  names which object is read, not the value, so it is followed only when the
  receiver is the value itself (a box, a String, an enum).  container_receiver
  and library_receiver are followed.
- A `<callee>.return` is CLOCK when a CLOCK DECLARED_SITE names the callee or
  it is System.currentTimeMillis/nanoTime; CONFIG_CALL for a JVM property
  getter or a CONFIG_SOURCE row of the engine's library catalog, matched by
  subsignature on the catalog owner or on a subclass in CONFIG_ALIASES; FAULT
  when an explicit_symbolic_fault edge names it.  Else it is walked through
  when it has incoming edges (an expanded body) or the call's operand edges
  carry it (an accessor's field, a value-like call's arguments, a container's
  receiver); else READ (a JDK atomic), IO (a JDK *InputStream, Reader, File(s),
  Channel, Socket, URLConnection), TRACK_CONTAINER (a JDK or Guava collection),
  SCOPE (a package the graph analyses) or LIBRARY.
- A field is READ (a JDK atomic, or a READ DECLARED_SITE cell); no boundary
  when it is a box's own state or a class constant (written only in <clinit>,
  or of its own type with no writer: an enum constant); CONFIG_FIELD when every
  field_write edge into it stores, within 4 same-method edges, a CONFIG_CALL
  return (the graph holds only the writers the slice kept; config wrappers are
  not recognized); PRE_WINDOW without a WRITE_SITE row (no region holds a
  writer); else TRACK_CONTAINER, TRACK (integral or boxed) or TRACK_IDENTITY by
  the field's type (the writer's region is not compared with the reader's).
- A formal with no incoming edge is WIRE: there is no attach/port test, so a
  callback that library code invokes (a lambda, a watcher) counts too.

Usage: rootcov.py [--json] [--jobs N] DIR|GLOB ...
  DIR is a round (contains out/) or a campaign (contains static_scope_map.jsonl).
  Prints one TSV row per check, then the aggregate; --json prints one JSON
  object per check instead.  A missing artifact prints "-" and is counted.
"""
import argparse
import collections
import glob
import gzip
import json
import os
import re
import statistics
import sys
from concurrent.futures import ProcessPoolExecutor

CATALOG = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..',
                       'src', 'main', 'resources', 'edu', 'uva', 'liftlab',
                       'graphchecker', 'library-catalog.jsonl')
MAX_DISTANCE = 16
MINTABLE = ('CLOCK', 'FAULT', 'CONFIG_CALL', 'CONFIG_FIELD', 'READ', 'TRACK')
NAMED = ('TRACK_IDENTITY', 'TRACK_CONTAINER', 'PRE_WINDOW', 'WIRE', 'SCOPE',
         'IO', 'LIBRARY')
CATEGORIES = ('CLOCK', 'FAULT', 'CONFIG', 'READ', 'HOOK')
JVM_CLOCKS = {'<java.lang.System: long currentTimeMillis()>',
              '<java.lang.System: long nanoTime()>'}
JVM_CONFIG = (
    '<java.lang.System: java.lang.String getProperty(java.lang.String)>',
    '<java.lang.System: java.lang.String getProperty(java.lang.String,java.lang.String)>',
    '<java.lang.System: java.lang.String getenv(java.lang.String)>',
    '<java.lang.Boolean: boolean getBoolean(java.lang.String)>',
    '<java.lang.Integer: java.lang.Integer getInteger(java.lang.String)>',
    '<java.lang.Integer: java.lang.Integer getInteger(java.lang.String,int)>',
    '<java.lang.Integer: java.lang.Integer getInteger(java.lang.String,java.lang.Integer)>',
    '<java.lang.Long: java.lang.Long getLong(java.lang.String)>',
    '<java.lang.Long: java.lang.Long getLong(java.lang.String,long)>',
    '<java.lang.Long: java.lang.Long getLong(java.lang.String,java.lang.Long)>')
# A subclass a config getter is invoked through: matched as its catalog owner.
CONFIG_ALIASES = {
    'org.apache.hadoop.hdfs.HdfsConfiguration': 'org.apache.hadoop.conf.Configuration',
    'org.apache.hadoop.mapred.JobConf': 'org.apache.hadoop.conf.Configuration'}
# Edges that state WHICH object a value is read from, not the value: the
# boundary walk does not follow them unless the receiver IS the value (a box,
# a String, an enum: VALUE_LIKE).  A container's receiver is its contents, so
# container_receiver is always followed.
IDENTITY_EDGES = {'accessor_receiver', 'method_receiver', 'constructor_receiver',
                  'dispatch_receiver', 'dispatch_caller_receiver'}
VALUE_LIKE = re.compile(r'^(?:java\.lang\.(?:Boolean|Byte|Character|Short|Integer|Long|Float'
                        r'|Double|Number|String|CharSequence|StringBuilder|StringBuffer|Enum)'
                        r'|java\.math\.Big(?:Integer|Decimal))$')
# Edges from a call's operands into its result: a library return they carry is
# no boundary (an accessor's field, a value-like call's arguments, a container's
# receiver and key, a shared receiver's state).
OPERAND_EDGES = {'accessor_field_return', 'local_def_use', 'container_receiver',
                 'container_argument', 'library_receiver'}
ATOMIC = 'java.util.concurrent.atomic.'
INTEGRAL = {'boolean', 'byte', 'char', 'short', 'int', 'long', 'float',
            'double'} | {'java.lang.' + box for box in (
                'Boolean', 'Byte', 'Character', 'Short', 'Integer', 'Long',
                'Float', 'Double')}

METHOD = re.compile(r'^<([^:]+): (\S+ [^\s(]+\(.*\))>$')
FIELD = re.compile(r'^<([^:]+): (\S+) [^\s(>]+>$')
RETURN = re.compile(r'^(<.+>)\.return$')
FORMAL = re.compile(r'>\.param\d+:')
PORT = re.compile(r'REGION\.[0-9a-f-]+\.in\.[0-9a-f-]+')
CONTAINER = re.compile(r'^(?:java\.util\.(?:concurrent\.)?|com\.google\.common\.collect\.)'
                       r'\w*(?:Map|Set|List|Queue|Deque|Collection|Iterator|Vector'
                       r'|Stack|Hashtable|Properties|Enumeration)$')
IO = re.compile(r'^(?:java|javax|sun|jdk)\.\S*'
                r'(?:InputStream|Reader|File|Files|Channel|Socket|URLConnection)$')
ROLE = re.compile(r'"role":"(\w+)"')
LOG_STAGE = re.compile(r'^\[campaign\] stage (\w+)')
LOG_MAX_JOBS = re.compile(r'^\[campaign\] workers=\d+ maxJobs=(\d+)')
LOG_PLANNED = re.compile(r'^\[campaign\] planned tasks: (\d+)')
LOG_WAVE = re.compile(r'^\[campaign\] wave (\d+): (?:(\d+) obligation|no obligation)')
LOG_OVER_CAP = re.compile(r'selected exact closure exceeds max jobs: (\d+) > (\d+);'
                          r' admissionBasis=\{([^}]*)\}')


def config_sources():
    """owner -> config getter subsignatures: the JVM set plus the catalog's."""
    sources = collections.defaultdict(set)
    rows = [{'method': m} for m in JVM_CONFIG]
    if os.path.exists(CATALOG):
        with open(CATALOG) as catalog:
            rows += [r for r in map(json.loads, filter(str.strip, catalog))
                     if r.get('kind') == 'CONFIG_SOURCE']
    else:
        print('rootcov: no library catalog at %s; CONFIG_CALL is the JVM getters only'
              % os.path.normpath(CATALOG), file=sys.stderr)
    for row in rows:
        owner, subsignature = METHOD.match(row['method']).groups()
        sources[owner].add(subsignature)
    return sources


CONFIG = config_sources()
MALFORMED = collections.Counter()


def is_config(callee):
    m = METHOD.match(callee)
    return bool(m) and m.group(2) in CONFIG.get(
        CONFIG_ALIASES.get(m.group(1), m.group(1)), ())


def package(signature):
    """The first three package segments of a method or field's owner."""
    return '.'.join(signature[1:signature.find(':')].split('.')[:3])


def lines(path, mode='rt'):
    """A file's lines as the engine reads them (smt.ArtifactIO#input): a .gz
    file's decoded, as far as its stream was written (a replay killed before
    its close leaves it ending at its last flush)."""
    with (gzip.open(path, mode) if path.endswith('.gz') else open(path, mode)) as f:
        try:
            for line in f:
                yield line
        except EOFError:
            return


def rows(path):
    """A JSONL file's rows, streamed; a torn line (a killed round) is counted."""
    for line in lines(path):
        if not line.strip():
            continue
        try:
            yield json.loads(line)
        except ValueError:
            MALFORMED[os.path.basename(path)] += 1


def load(path):
    with open(path) as f:
        return json.load(f)


def scope_map(path):
    """The TARGET_SITE guards, DECLARED_SITE rows and region-held written cells."""
    smap = {'guards': set(), 'declared': [], 'written': set(), 'reads': set(),
            'clocks': set(JVM_CLOCKS)}
    with open(path) as f:
        for line in f:
            role = ROLE.search(line)
            if not role or role.group(1) not in (
                    'TARGET_SITE', 'DECLARED_SITE', 'WRITE_SITE'):
                continue
            r = json.loads(line)
            if r['role'] == 'TARGET_SITE':
                smap['guards'].update(r.get('guards') or ())
            elif r['role'] == 'WRITE_SITE':
                smap['written'].update(c for c in (r.get('cell'), r.get('carrier')) if c)
            elif r.get('inputKind'):
                smap['declared'].append((r['inputKind'], r.get('dependencyCell', '')))
                if r['inputKind'] == 'CLOCK':
                    smap['clocks'].add(r.get('declaredCallee', ''))
                elif r['inputKind'] == 'READ':
                    smap['reads'].add(r.get('cell', ''))
    return smap


def static_walk(edges_path, smap):
    """M-f boundaries and the declared roots' cones."""
    into = collections.defaultdict(list)
    operands, throws, markers, analysed, carried = set(), set(), set(), set(), set()
    for e in rows(edges_path):
        kind, to, invoke = e.get('kind'), e.get('toCell', ''), e.get('invoke', '')
        value = kind not in IDENTITY_EDGES or bool(VALUE_LIKE.match(invoke[1:invoke.find(':')]))
        into[to].append((e.get('fromCell', ''), kind, e.get('method', ''), value))
        analysed.add(package(e.get('method', '')))
        if kind in OPERAND_EDGES:
            carried.update((invoke, e.get('accessorImplementationMethod', '')))
        if kind == 'exception_throw':
            throws.add(to)
        elif kind == 'exception_guard' and e.get('siteId') in smap['guards']:
            operands.add(e.get('fromCell', ''))
        elif kind == 'explicit_symbolic_fault':
            markers.add(invoke)

    def stores_config(cell, method):
        """Whether a field store's value is a config getter's return, within
        four edges of the storing method (locals, casts)."""
        frontier, seen = [cell], {cell}
        for _ in range(5):
            nxt = []
            for c in frontier:
                m = RETURN.match(c)
                if m and is_config(m.group(1)):
                    return True
                for f, kind, owner, _ in into.get(c, ()):
                    if owner == method and kind != 'guard_dependency' and f not in seen:
                        seen.add(f)
                        nxt.append(f)
            frontier = nxt
        return False

    def field_class(cell, owner, ftype):
        if ATOMIC in (owner[:len(ATOMIC)], ftype[:len(ATOMIC)]) or cell in smap['reads']:
            return 'READ'
        if VALUE_LIKE.match(owner):
            return None  # a box's or String's own state: its receiver carries it
        writers = [(f, m) for f, kind, m, _ in into.get(cell, ()) if kind == 'field_write']
        if (all(m.endswith(' <clinit>()>') for _, m in writers)
                if writers else ftype == owner):
            return None  # a class constant: $assertionsDisabled, an enum constant
        if writers and all(stores_config(f, m) for f, m in writers):
            return 'CONFIG_FIELD'
        if cell not in smap['written']:
            return 'PRE_WINDOW'
        if CONTAINER.match(ftype):
            return 'TRACK_CONTAINER'
        return 'TRACK' if ftype in INTEGRAL else 'TRACK_IDENTITY'

    def classify(cell):
        m = RETURN.match(cell)
        if m:
            callee = m.group(1)
            if callee in smap['clocks']:
                return 'CLOCK'
            if is_config(callee):
                return 'CONFIG_CALL'
            if callee in markers:
                return 'FAULT'
            if cell in into or callee in carried:
                return None  # an expanded body, or the call's operand edges, carry it
            owner = callee[1:callee.find(':')]
            if owner.startswith(ATOMIC):
                return 'READ'
            if IO.match(owner):
                return 'IO'
            if CONTAINER.match(owner):
                return 'TRACK_CONTAINER'
            return 'SCOPE' if package(callee) in analysed else 'LIBRARY'
        m = FIELD.match(cell)
        if m:
            return field_class(cell, m.group(1), m.group(2))
        if FORMAL.search(cell) and cell not in into:
            return 'WIRE'
        return None

    distance = dict.fromkeys(operands, 0)
    queue = collections.deque(operands)
    boundaries = {}
    while queue:
        cell = queue.popleft()
        cls = classify(cell)
        if cls:  # nearest first: the first cell of a class is its nearest
            b = boundaries.setdefault(cls, {'count': 0, 'min': distance[cell], 'nearest': cell})
            b['count'] += 1
            continue
        if distance[cell] < MAX_DISTANCE:
            for f, _, _, value in into.get(cell, ()):
                if value and f not in distance:
                    distance[f] = distance[cell] + 1
                    queue.append(f)

    fatal, predicate = reach(into, throws), reach(into, operands)
    declared = collections.defaultdict(lambda: {'all': 0, 'fatalCone': 0, 'predCone': 0})
    for kind, cell in smap['declared']:
        declared[kind]['all'] += 1
        declared[kind]['fatalCone'] += cell in fatal
        declared[kind]['predCone'] += cell in predicate
    return boundaries, dict(declared), len(operands)


def reach(into, starts):
    seen, stack = set(starts), list(starts)
    while stack:
        for f, _, _, _ in into.get(stack.pop(), ()):
            if f not in seen:
                seen.add(f)
                stack.append(f)
    return seen


def sessions(camp):
    """(dir, seed?, admitted?) for every session on disk."""
    admitted = set()
    for path in glob.glob(os.path.join(camp, 'schedule', 'iteration-*',
                                       'obligation_results.jsonl')):
        admitted.update(r.get('sessionId') for r in rows(path)
                        if r.get('verdict') == 'ADMITTED')
    found = []
    for d in sorted(glob.glob(os.path.join(camp, 'schedule', 'iteration-*', 'sessions', '*', ''))):
        manifest = os.path.join(d, 'manifest.json')
        seed = os.path.exists(manifest) and load(manifest).get('role') == 'SEED'
        found.append((d, seed, seed or os.path.basename(d.rstrip('/')) in admitted))
    return found


def anchor_rows(found):
    """M-a: reached / phi / fatal anchor rows per scope (seed, admitted, disk)."""
    scopes = {s: collections.Counter() for s in ('seed', 'admitted', 'disk')}
    for d, seed, admitted in found:
        path = os.path.join(d, 'targets.jsonl.gz')
        if not os.path.exists(path):
            continue
        for r in rows(path):
            if not r.get('reachedAnchor'):
                continue
            row = collections.Counter(reached=1, phi=bool(r.get('phiTerm')),
                                      fatal=bool(r.get('observedFatal')))
            for scope, member in (('seed', seed), ('admitted', admitted), ('disk', True)):
                if member:
                    scopes[scope].update(row)
    return {s: {k: c[k] for k in ('reached', 'phi', 'fatal')} for s, c in scopes.items()}


def address(occurrence):
    """A roots.jsonl occurrence object as OccurrenceAddress#render spells it,
    the plan rows' occurrenceId."""
    c = occurrence['context']
    if c.get('form') == 'ROOT':
        ctx = 'Root:%s%s#%d' % (c['role'], '/' + c['api'] if c.get('api') else '',
                                c['windowIndex'])
    elif c.get('form') == 'ANCHOR':
        ctx = 'Anchor:%s@%s' % (c['producerEndpointId'], c['rpcSite'])
    else:
        ctx = 'Lost:%s' % c.get('role')
    return '%s/region/%s/ctx:%s/idx:%s' % (
        occurrence['node'], occurrence['regionId'], ctx,
        '/'.join('%s@%d' % (f['callSite'], f['iteration']) for f in occurrence.get('index') or ()))


def moved_admissions(camp, found, bases):
    """M-d: the plan basis of each occurrence that minted a root the claim moved."""
    path = os.path.join(camp, 'schedule', 'final', 'claim.json')
    if not os.path.exists(path):
        return None
    moved = set(((load(path).get('claim') or {}).get('movedRoots') or {}))
    minted = set()
    for d, _, _ in found if moved else ():
        roots = os.path.join(d, 'roots.jsonl.gz')
        for r in rows(roots) if os.path.exists(roots) else ():
            if r.get('rootId') in moved or r.get('symbol') in moved:
                minted.add(address(r['occurrence']))
    return dict(collections.Counter(bases.get(o, '-') for o in minted))


def root_demand(camp):
    """M-f from the engine: root_demand.jsonl's boundaries, class -> count and
    nearest distance."""
    path = os.path.join(camp, 'root_demand.jsonl')
    if not os.path.exists(path):
        return None
    found = {}
    for r in rows(path):
        b = found.setdefault(r['class'], {'count': 0, 'min': r.get('distance', 0)})
        b['count'] += 1
        b['min'] = min(b['min'], r.get('distance', 0))
    return found


def verdict(anchor):
    if anchor['reached'] == 0:
        return 'UNREACHED'
    if anchor['phi']:
        return 'SYMBOLIC'
    return 'FATAL' if anchor['fatal'] else 'CONCRETE'


def root_categories(found):
    """M-c over admitted sessions: category -> [distinct roots, mints]."""
    roots = collections.defaultdict(set)
    mints = collections.Counter()
    for d, _, admitted in found:
        if not admitted:
            continue
        symbols = set()
        path = os.path.join(d, 'roots.jsonl.gz')
        for r in rows(path) if os.path.exists(path) else ():
            symbols.add(r.get('symbol'))
            if 'category' not in r:
                sys.exit('%s: a root row states no category: recorded before '
                         'the root-category contract' % path)
            roots[r['category']].add(r.get('rootId', ''))
            mints[r['category']] += 1
        path = os.path.join(d, 'reads.jsonl.gz')
        if not os.path.exists(path):
            continue
        for line in lines(path, 'rb'):  # only mint rows are parsed
            if b'"mintVersion"' not in line:
                continue
            symbol = json.loads(line).get('symbol', '')
            if symbol not in symbols:
                port = PORT.search(symbol)
                roots['READ'].add(port.group(0) if port else symbol)
                mints['READ'] += 1
    return {c: [len(roots[c]), mints[c]] for c in CATEGORIES if mints[c]}


def campaign_log(path):
    """The stage reached, the cap, the plan and wave sizes the log states."""
    log = {'stage': None, 'error': False, 'maxJobs': None, 'planned': None,
           'waves': {}, 'overCap': None}
    if not os.path.exists(path):
        return log
    with open(path, errors='replace') as f:
        for line in f:
            if line.startswith('[campaign:error]'):
                log['error'] = True
            elif line.startswith('[campaign]'):
                for pattern, key in ((LOG_STAGE, 'stage'), (LOG_MAX_JOBS, 'maxJobs'),
                                     (LOG_PLANNED, 'planned')):
                    m = pattern.match(line)
                    if m:
                        log[key] = m.group(1)
                m = LOG_WAVE.match(line)
                if m:
                    log['waves'][int(m.group(1))] = int(m.group(2) or 0)
            elif 'exceeds max jobs' in line:
                m = LOG_OVER_CAP.search(line)
                if m:
                    log['overCap'] = (int(m.group(1)), int(m.group(2)), {
                        k: int(v) for k, v in (p.split('=') for p in m.group(3).split(', ') if p)})
    return log


def analyze(camp):
    MALFORMED.clear()
    camp = camp.rstrip('/')
    parent = os.path.dirname(camp)
    case = os.path.basename(camp)
    round_dir = os.path.dirname(parent) if os.path.basename(parent) == 'out' else parent
    out = {'round': os.path.basename(round_dir), 'case': case, 'dir': camp, 'missing': [],
           'boundaries': None, 'declared': None, 'operands': None}

    def present(name, path):
        if not os.path.exists(path):
            out['missing'].append(name)
        return os.path.exists(path)

    log_path = os.path.join(round_dir, 'logs', case + '.log')
    present('log', log_path)
    log = campaign_log(log_path)
    out['stage'] = (log['stage'] or '-') + ('!' if log['error'] else '')

    smap_path = os.path.join(camp, 'static_scope_map.jsonl')
    edges_path = os.path.join(camp, 'candidate_dataflow_edges.jsonl.gz')
    smap = scope_map(smap_path) if present('scope_map', smap_path) else None
    if present('edges', edges_path) and smap:
        out['boundaries'], out['declared'], out['operands'] = static_walk(edges_path, smap)
    elif smap:
        out['declared'] = {k: {'all': n} for k, n in collections.Counter(
            kind for kind, _ in smap['declared']).items()}

    found = sessions(camp)
    out['sessions'] = {'disk': len(found), 'admitted': sum(a for _, _, a in found)}
    out['anchor'] = out['concrete'] = out['roots'] = None
    if found:
        out['anchor'] = anchor_rows(found)
        out['concrete'] = verdict(out['anchor']['admitted'])
        out['roots'] = root_categories(found)
    else:
        out['missing'].append('sessions')

    waves = sorted(glob.glob(os.path.join(camp, 'schedule', 'iteration-*',
                                          'obligations-[0-9][0-9][0-9][0-9]', 'obligations.jsonl')))
    asked = [sum(1 for _ in rows(p)) for p in waves]
    if not asked:
        out['missing'].append('obligations')
        asked = [log['waves'][w] for w in sorted(log['waves'])]
    out['wave0'] = asked[0] if asked else None
    out['waves'] = sum(1 for n in asked if n) if asked else None

    plans = [p for p in (os.path.join(camp, 'schedule', 'iteration-0000', 'concolic_region_plan.jsonl'),
                         os.path.join(camp, 'runtime', 'concolic_region_plan.jsonl'))
             if os.path.exists(p)]
    out['maxJobs'] = int(log['maxJobs'] or 1024)
    out['admissions'] = out['closure'] = None
    bases = {}
    if plans:
        bases = {r['occurrenceId']: r.get('admissionBasis') or 'TARGET_REACHABLE'
                 for r in rows(plans[0]) if r.get('kind') == 'CONCOLIC_REGION_PLAN'}
        out['admissions'] = dict(collections.Counter(bases.values()))
        out['closure'] = len(bases)
    else:
        out['missing'].append('plan')
        if log['overCap']:
            out['closure'], out['maxJobs'], out['admissions'] = log['overCap']
        elif log['planned']:
            out['closure'] = int(log['planned'])

    out['moved'] = moved_admissions(camp, found, bases)
    out['demand'] = root_demand(camp)

    final = os.path.join(camp, 'schedule', 'final')
    result, gaps = os.path.join(final, 'result.json'), os.path.join(final, 'gaps.json')
    out['finding'] = load(result).get('findingKind') if present('final', result) else None
    out['decidedConcretely'] = None
    if os.path.exists(gaps):
        g = load(gaps)
        out['decidedConcretely'] = sum(
            1 for row in (g.get('gaps') or []) + (g.get('telemetryGaps') or [])
            if row.get('detail', '').startswith('the anchor decided concretely'))

    if out['boundaries'] is not None:
        named = sorted((b['min'], c) for c, b in out['boundaries'].items() if c in NAMED)
        out['blockedBy'] = ([c for _, c in named] or
                            ['MINTABLE_ONLY' if out['boundaries'] else 'NO_BOUNDARY'])
    else:
        out['blockedBy'] = None
    out['malformedRows'] = dict(MALFORMED)
    return out


def campaigns(args):
    """Every campaign dir the arguments name, in order, once."""
    found = []
    for arg in args:
        for path in sorted(glob.glob(arg)) or [arg]:
            if os.path.isdir(os.path.join(path, 'out')):
                found += sorted(d for d in glob.glob(os.path.join(path, 'out', '*'))
                                if os.path.isdir(d))
            elif os.path.isfile(os.path.join(path, 'static_scope_map.jsonl')):
                found.append(path.rstrip('/'))
            else:
                print('rootcov: neither a round nor a campaign: ' + path, file=sys.stderr)
    return list(dict.fromkeys(found))


def dash(value, render=str):
    return '-' if value is None else render(value)


def triple(a):
    return '%d/%d/%d' % (a['reached'], a['phi'], a['fatal'])


def pairs(d, render=str):
    return ','.join('%s=%s' % (k, render(v)) for k, v in sorted(d.items())) or '0'


def row(c):
    return '\t'.join([
        c['round'], c['case'], c['stage'], dash(c['finding']), dash(c['concrete']),
        dash(c['anchor'], lambda a: triple(a['seed'])),
        dash(c['anchor'], lambda a: triple(a['admitted'])),
        '%d/%d' % (c['sessions']['admitted'], c['sessions']['disk']),
        dash(c['wave0']), dash(c['waves']),
        dash(c['roots'], lambda r: pairs(r, lambda v: '%d/%d' % tuple(v))),
        dash(c['admissions'], pairs),
        '%s/%d' % (dash(c['closure']), c['maxJobs']),
        dash(c['moved'], pairs),
        dash(c['decidedConcretely']),
        dash(c['blockedBy'], '>'.join),
        dash(c['boundaries'], histogram),
        dash(c['demand'], histogram),
        dash(c['declared'], lambda d: ','.join(
            '%s:%s' % (k, '/'.join(str(v[x]) for x in ('all', 'fatalCone', 'predCone') if x in v))
            for k, v in sorted(d.items())) or '0')])


def histogram(boundaries):
    return ','.join('%s:%d@%d' % (k, v['count'], v['min']) for k, v in sorted(
        boundaries.items(), key=lambda kv: (kv[1]['min'], kv[0]))) or '0'


HEADER = ('round', 'case', 'stage', 'finding', 'anchor verdict', 'seed r/phi/fatal',
          'admitted r/phi/fatal', 'sessions adm/disk', 'wave0', 'waves',
          'roots/mints', 'admissions', 'closure/max', 'moved', 'decidedConcretely',
          'blockedBy', 'boundaries class:n@min', 'demand class:n@min',
          'declared all/fatal/pred')


def aggregate(checks):
    n = len(checks)

    def have(key):
        return [c for c in checks if c[key] is not None]

    lines = ['# aggregate over %d check(s)' % n,
             'missing artifacts: ' + pairs(collections.Counter(m for c in checks for m in c['missing']))]
    lines.append('M-a anchor verdict: ' + pairs(collections.Counter(c['concrete'] or '-' for c in checks)))
    for scope in ('seed', 'admitted', 'disk'):
        total = collections.Counter()
        for c in have('anchor'):
            total.update(c['anchor'][scope])
        lines.append('M-a %s rows reached/phi/fatal: %d/%d/%d' % (
            scope, total['reached'], total['phi'], total['fatal']))
    w = have('wave0')
    lines.append('M-b wave0>0: %d of %d checks with a wave 0 (%d obligations); waves asked: %s' % (
        sum(1 for c in w if c['wave0']), len(w), sum(c['wave0'] for c in w),
        pairs(collections.Counter(sorted(c['waves'] for c in w)))))
    roots = collections.defaultdict(lambda: [0, 0, 0])
    for c in have('roots'):
        for cat, (r, m) in c['roots'].items():
            roots[cat][0] += r
            roots[cat][1] += m
            roots[cat][2] += 1
    lines.append('M-c roots/mints (checks): %s; checks minting no root: %d of %d' % (
        ','.join('%s=%d/%d(%d)' % (k, *roots[k]) for k in CATEGORIES if k in roots) or '0',
        sum(1 for c in have('roots') if not c['roots']), len(have('roots'))))
    basis = collections.Counter()
    for c in have('admissions'):
        basis.update(c['admissions'])
    closure = have('closure')
    lines.append('M-d admissions (%d checks): %s; closure > maxJobs: %d of %d' % (
        len(have('admissions')), pairs(basis),
        sum(1 for c in closure if c['closure'] > c['maxJobs']), len(closure)))
    moved = collections.Counter()
    for c in have('moved'):
        moved.update(c['moved'])
    lines.append('M-d moved-root occurrences (%d claims) by plan basis: %s' % (
        len(have('moved')), pairs(moved)))
    dc = have('decidedConcretely')
    lines.append('M-e decided concretely: %d of %d finals (%d refusals); findings: %s' % (
        sum(1 for c in dc if c['decidedConcretely']), len(dc),
        sum(c['decidedConcretely'] for c in dc),
        pairs(collections.Counter(c['finding'] or '-' for c in checks))))
    walked = have('boundaries')
    lines.append('M-f blocked-by over %d walked checks, by anchor verdict (nearest class; classes present):'
                 % len(walked))
    for v in sorted({c['concrete'] or '-' for c in walked}):
        group = [c for c in walked if (c['concrete'] or '-') == v]
        lines.append('    %-10s n=%d nearest %s; present %s' % (
            v, len(group), pairs(collections.Counter(c['blockedBy'][0] for c in group)),
            pairs(collections.Counter(b for c in group for b in c['blockedBy']))))
    lines.append('M-f boundary classes over %d walked checks (checks, cells, min, median of per-check min):'
                 % len(walked))
    for cls in MINTABLE + NAMED:
        mins = [c['boundaries'][cls]['min'] for c in walked if cls in c['boundaries']]
        if mins:
            lines.append('    %-15s %-7s checks=%d cells=%d min=%d median=%g' % (
                cls, 'mint' if cls in MINTABLE else 'named', len(mins),
                sum(c['boundaries'][cls]['count'] for c in walked if cls in c['boundaries']),
                min(mins), statistics.median(mins)))
    demanded = have('demand')
    classes = collections.defaultdict(list)
    for c in demanded:
        for cls, b in c['demand'].items():
            classes[cls].append(b)
    lines.append('M-f root_demand.jsonl classes over %d checks (checks, rows, min): %s' % (
        len(demanded), ','.join('%s=%d/%d@%d' % (cls, len(bs), sum(b['count'] for b in bs),
                                                 min(b['min'] for b in bs))
                                for cls, bs in sorted(classes.items())) or '0'))
    declared, cones = collections.Counter(), collections.defaultdict(collections.Counter)
    for c in have('declared'):
        for kind, v in c['declared'].items():
            declared[kind] += v['all']
            if c['boundaries'] is not None:
                cones[kind].update(v)
    lines.append('static roots: DECLARED_SITE by inputKind over %d scope maps %s; over the %d walked '
                 'checks all/fatalCone/predCone %s' % (
                     len(have('declared')), pairs(declared), len(walked),
                     pairs(cones, lambda v: '%d/%d/%d' % (v['all'], v['fatalCone'], v['predCone']))))
    malformed = collections.Counter()
    for c in checks:
        malformed.update(c['malformedRows'])
    if malformed:
        lines.append('torn rows skipped: ' + pairs(malformed))
    return lines


def main():
    parser = argparse.ArgumentParser(
        description='Root coverage of recorded campaigns (R1-ROOTS WP0).')
    parser.add_argument('dirs', nargs='+', help='round dirs, campaign dirs or globs')
    parser.add_argument('--json', action='store_true', help='one JSON object per check')
    parser.add_argument('--jobs', type=int, default=min(8, os.cpu_count() or 1))
    args = parser.parse_args()
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        checks = list(pool.map(analyze, campaigns(args.dirs)))
    if args.json:
        for c in checks:
            print(json.dumps(c, sort_keys=True))
        return
    print('\t'.join(HEADER))
    for c in checks:
        print(row(c))
    print()
    print('\n'.join(aggregate(checks)))


if __name__ == '__main__':
    main()

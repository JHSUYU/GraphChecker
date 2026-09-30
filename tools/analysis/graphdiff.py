#!/usr/bin/env python3
"""graphdiff: how an injected transport fault changes the cross-node causal graph.

READ-ONLY over /u/vnr3ne/gc-out/accept-<round>-<case>/...; writes only into $GRAPHDIFF_OUT/accept-<round>/.
Usage: graphdiff.py <round>   (e.g. v53; door sites of the v51 hand-written and v53+ woven doors).

For every case, the seed session and every ADMITTED obligation session are loaded into five
layers, each keyed without session-local ids:
  occurrences  node|region|context|index                     (activations.jsonl)
  WIRE edges   producer endpoint -> consumer endpoint        (attaches.jsonl; export-only endpoints kept)
  STATE edges  writer endpoint -> reader endpoint            (writes/reads joined on location+version
                                                              inside one session; MINT / UNWRITTEN)
  decisions    (occurrence, siteId, ordinal) -> [outcomes]   (decisions.jsonl)
  messages     SEND(ctx, site, k) -> RECV node               (schedule.jsonl; a RECV names its SEND by
                                                              the producer endpoint id in its Anchor ctx)
  targets      reachedAnchor / observedFatal                  (targets.jsonl)
An endpoint key is occurrence + site + siteIndex; attempt is kept as an attribute.

Every admitted session is diffed against the seed. Sessions whose world holds a MARKER root
assigned true are FAULT sessions (the door named from the flip site / the root's region); the rest
(clock, serial, config worlds) are the CONTROL set, whose diffs measure replay noise.
"""
import collections
import csv
import glob
import json
import os
import re
import sys

GC = '/u/vnr3ne/gc-out'
ROUND = 'accept-' + (sys.argv[1] if len(sys.argv) > 1 else 'v51')
# Every case the round ran (the nine, or an ad-hoc round's), from its directories.
CASES = sorted(os.path.basename(d)[len(ROUND) + 1:]
               for d in glob.glob(f'{GC}/{ROUND}-*')
               if glob.glob(d + '/out/*/schedule/iteration-0000/obligation_results.jsonl'))
OUT = os.path.join(os.environ.get('GRAPHDIFF_OUT', '/tmp/graphdiff'), ROUND)
os.makedirs(OUT, exist_ok=True)

DOOR_SITES = {  # branch site of each marker: v51 hand-written, v53 woven kinds
    'sendRpcRequest(org.apache.hadoop.ipc.Client$Call)>#u17': 'IPC:REQUEST',
    'sendRpcRequest(org.apache.hadoop.ipc.Client$Call)>#u22': 'IPC:REQUEST:ConnectTimeout',
    'getRpcResponse(org.apache.hadoop.ipc.Client$Call,org.apache.hadoop.ipc.Client$Connection)>#u7': 'IPC:RESPONSE',
    'getRpcResponse(org.apache.hadoop.ipc.Client$Call,org.apache.hadoop.ipc.Client$Connection)>#u6': 'IPC:RESPONSE',
    'getRpcResponse(org.apache.hadoop.ipc.Client$Call,org.apache.hadoop.ipc.Client$Connection)>#u11': 'IPC:RESPONSE:EOF',
    'getRpcResponse(org.apache.hadoop.ipc.Client$Call,org.apache.hadoop.ipc.Client$Connection)>#u16': 'IPC:RESPONSE:SocketTimeout',
    'org.apache.hadoop.security.token.Token)>#u14': 'SASL:REQUEST',
    'org.apache.hadoop.security.token.Token)>#u15': 'SASL:REQUEST',
}
DOOR_REGIONS = {'REGION.763d087e': 'IPC:REQUEST', 'REGION.9ffdee3d': 'IPC:RESPONSE',
                'REGION.074f9e67': 'SASL:REQUEST', 'REGION.2edcf422': 'DATA_TRANSFER:SEND'}


def door_of_site(site):
    for suffix, door in DOOR_SITES.items():
        if site.endswith(suffix) and ('sendRpcRequest' in site or 'getRpcResponse' in site
                                      or 'doSaslHandshake' in site):
            return door
    return None


# ----------------------------------------------------------------------------- rendering
METH = re.compile(r'<([\w.$]+): [^ ]+ ([\w$<>]+)\(')


def short(cs):
    """'<pkg.Cls: ret m(args)>#u5' -> 'Cls.m#u5'."""
    m = METH.search(cs)
    if not m:
        return cs
    cls = m.group(1).rsplit('.', 1)[-1]
    rest = cs[cs.index('>') + 1:] if '>' in cs[m.end():] or cs.endswith('>') else ''
    # keep a '#uN' unit suffix if present after the signature
    tail = ''
    mm = re.search(r'>(#u\d+.*)$', cs)
    if mm:
        tail = mm.group(1)
    return f'{cls}.{m.group(2)}{tail}'


def node_short(n):
    return n.split('/', 1)[-1].replace('#epoch0', '')


def ctx_render(c):
    f = c.get('form')
    if f == 'ROOT':
        s = 'Root:' + c.get('role', '?')
        if c.get('api'):
            s += '/' + c['api']
        return s + '#' + str(c.get('windowIndex', ''))
    if f == 'ANCHOR':
        return 'Anchor:%s@%s' % (c.get('producerEndpointId'), c.get('rpcSite'))
    if f == 'LOST':
        return 'Lost:' + c.get('role', '?')
    return json.dumps(c, sort_keys=True)


def ctx_coarse(c):
    """Context without session/attempt-specific ids: ROOT keeps role/api, ANCHOR keeps rpcSite."""
    f = c.get('form')
    if f == 'ROOT':
        return 'Root:' + c.get('role', '?') + ('/' + c['api'] if c.get('api') else '')
    if f == 'ANCHOR':
        return 'Anchor@' + str(c.get('rpcSite'))
    return 'Lost:' + c.get('role', '?')


def idx_render(index):
    return '/'.join('%s@%s' % (short(i['callSite']), i['iteration']) for i in index)


def occ_key(o):
    return '%s|%s|%s|%s' % (node_short(o['node']), o['regionId'][:15], ctx_render(o['context']),
                            idx_render(o['index']))


def occ_group(o):
    c = o['context']
    return (node_short(o['node']), o['regionId'][:15], c.get('form'),
            c.get('role') or c.get('rpcSite') or '')


SITE_NORM = [(re.compile(r'(INSTANCE_FIELD|STATIC_FIELD|ARRAY_ELEMENT|ARRAY)/\d+#'), r'\1/*#'),
             # a reflective call runs through NativeMethodAccessorImpl for its first 15 invocations and
             # through a JVM-generated GeneratedMethodAccessor<N> after (sun.reflect.inflationThreshold):
             # the same logical write gets a different site depending on how warm the JVM is
             (re.compile(r'sun\.reflect\.(GeneratedMethodAccessor\d*|NativeMethodAccessorImpl)#invoke\([^#]*#\d+'),
              'sun.reflect.MethodAccessor#invoke'),
             (re.compile(r'GeneratedMethodAccessor\d+'), 'GeneratedMethodAccessorN')]


def site_norm(s):
    for rx, rep in SITE_NORM:
        s = rx.sub(rep, s)
    return short(s)


def ep_key(ep):
    return '%s::%s::%s' % (occ_key(ep['occurrence']), site_norm(ep['site']), site_norm(idx_render(ep['siteIndex'])))


def ep_occ(ep):
    return occ_key(ep['occurrence'])


def rows(path):
    if not os.path.exists(path):
        return
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if line:
                yield json.loads(line)


# ----------------------------------------------------------------------------- loading
class Session:
    def __init__(self, d):
        self.dir = d
        self.id = os.path.basename(d)
        self.occ = collections.Counter()
        self.occ_obj = {}
        self.lost = 0
        for r in rows(d + '/activations.jsonl'):
            k = occ_key(r['occurrence'])
            self.occ[k] += 1
            self.occ_obj[k] = r['occurrence']
            if r['occurrence']['context'].get('form') == 'LOST':
                self.lost += 1
        # WIRE
        self.wire = collections.Counter()
        self.wire_attempts = collections.Counter()
        self.no_producer = 0
        self.exports = collections.Counter()
        attached_prod = set()
        for r in rows(d + '/attaches.jsonl'):
            cons = ep_key(r['endpoint'])
            if r.get('producer'):
                prod = ep_key(r['producer'])
                attached_prod.add(prod)
                self.wire_attempts[r['producer'].get('attempt', 0)] += 1
            else:
                prod = 'NO_PRODUCER'
                self.no_producer += 1
            self.wire[(prod, cons)] += 1
        for r in rows(d + '/exports.jsonl'):
            self.exports[ep_key(r['endpoint'])] += 1
        self.orphan_exports = sum(v for k, v in self.exports.items() if k not in attached_prod)
        # STATE
        writes = {}
        for r in rows(d + '/writes.jsonl'):
            loc = json.dumps(r['location'], sort_keys=True)
            writes[(loc, r['version'])] = ep_key(r['endpoint'])
        self.state = collections.Counter()
        self.reader_writers = collections.defaultdict(collections.Counter)
        self.reads_mint = self.reads_unwritten = self.reads_written = 0
        for r in rows(d + '/reads.jsonl'):
            loc = json.dumps(r['location'], sort_keys=True)
            reader = ep_key(r['endpoint'])
            w = writes.get((loc, r['observedVersion']))
            if w is None:
                if r.get('mintVersion') is not None and r['mintVersion'] == r['observedVersion']:
                    m = re.search(r'field_(.+?)\.occ\.', r.get('symbol', ''))
                    w = 'MINT:' + (m.group(1) if m else r.get('symbol', '')[:60])
                    self.reads_mint += 1
                else:
                    w = 'UNWRITTEN'
                    self.reads_unwritten += 1
            else:
                self.reads_written += 1
            self.state[(w, reader)] += 1
            self.reader_writers[reader][w] += 1
        # decisions
        self.dec = collections.defaultdict(list)
        self.dec_obj = {}
        for r in sorted(rows(d + '/decisions.jsonl'), key=lambda r: r['seq']):
            k = (occ_key(r['occurrence']), r['siteId'], r['ordinal'])
            self.dec[k].append(r['outcome'])
            self.dec_obj[k] = r['occurrence']
        self.door_false = [(k, door_of_site(k[1])) for k, v in self.dec.items()
                           if door_of_site(k[1]) and False in v]
        # targets
        self.targets = list(rows(d + '/targets.jsonl'))
        self.reached = any(t.get('reachedAnchor') for t in self.targets)
        self.fatal = any(t.get('observedFatal') for t in self.targets)
        # schedule
        self.sched = collections.Counter()
        sends = {}
        recvs = []
        self.send_keys = collections.Counter()
        for r in rows(d + '/schedule.jsonl'):
            if 'kind' not in r:
                continue
            self.sched[r['kind']] += 1
            if r['kind'] == 'SEND':
                ctx = r['context'].split('|', 1)
                sk = (node_short(ctx[0]) + '|' + anchor_norm(ctx[1] if len(ctx) > 1 else ''),
                      r['site'], r['k'])
                sends[r.get('endpoint')] = sk
                self.send_keys[(sk[0], sk[1])] += 1
            elif r['kind'] == 'RECV':
                recvs.append(r)
        self.msg = collections.Counter()
        delivered = set()
        for r in recvs:
            m = re.search(r'Anchor:([0-9a-f]+)@', r['context'])
            if not m:
                continue
            sk = sends.get(m.group(1))
            recv_node = node_short(r['context'].split('|', 1)[0])
            if sk is None:
                self.msg[(('?', r['site'], 0), recv_node)] += 1
                continue
            delivered.add(m.group(1))
            self.msg[(sk, recv_node)] += 1
        self.undelivered = collections.Counter()
        for eid, sk in sends.items():
            if eid not in delivered:
                self.undelivered[sk] += 1
        self.sends = sends


def anchor_norm(ctxtail):
    """A context tail as the schedule writes it; kept verbatim (anchor ids are stable across replays
    as long as the producer endpoint's identity is)."""
    return ctxtail


# ----------------------------------------------------------------------------- obligations
def load_case(case):
    it = glob.glob(f'{GC}/{ROUND}-{case}/out/*/schedule/iteration-0000')[0]
    results = {}
    for r in rows(it + '/obligation_results.jsonl'):
        results[r['obligationId']] = r
    tasks = {}
    for f in glob.glob(it + '/obligations-*/*/focused_task.jsonl'):
        for t in rows(f):
            tasks[t['obligationId']] = t
    region_names = {}
    for r in rows(it + '/concolic_region_plan.jsonl'):
        if r.get('kind') == 'CONCOLIC_REGION_PLAN':
            region_names[r['regionId'][:15]] = short(r.get('targetMethod', ''))
    sess_dirs = sorted(glob.glob(it + '/sessions/*'))
    seed = [d for d in sess_dirs if os.path.basename(d).startswith('seed-')]
    roots = {}
    for r in rows(seed[0] + '/roots.jsonl'):
        roots[r['rootId']] = r
    return it, results, tasks, region_names, seed[0], sess_dirs, roots


def world_of(task, roots):
    """(kind, door list, compound flag, text) for an obligation's world."""
    ra = task.get('rootAssignments', {}) or {}
    faults = []
    others = []
    pinned = []
    for rid, val in ra.items():
        kind = roots.get(rid, {}).get('kind')
        if kind == 'MARKER' or rid.split('.in.')[0][:15] in DOOR_REGIONS:
            if str(val) == 'true':
                faults.append(rid)
            else:
                pinned.append('%s=%s' % (rid[7:15] + '..' + rid.split('.in.')[-1][:8], val))
        else:
            others.append('%s=%s' % (rid, val))
    clocks = task.get('clockDeltas', {}) or {}
    inh = task.get('inheritedFlips', []) or []
    flip = task['flip']
    fdoor = door_of_site(flip['siteId'])
    doors = []
    for rid in faults:
        reg = rid.split('.in.')[0][:15]
        d = None
        if fdoor and len(faults) == 1:
            d = fdoor
        if d is None:
            d = DOOR_REGIONS.get(reg)
        if d is None:
            idx = roots.get(rid, {}).get('occurrence', {}).get('index', [])
            last = idx[-1]['callSite'] if idx else ''
            d = ('IPC:REQUEST' if 'sendRpcRequest' in last else 'IPC:RESPONSE' if 'getRpcResponse' in last
                 else 'SASL:REQUEST' if 'Sasl' in last else '?(%s)' % reg)
        doors.append(d)
    kind = 'FAULT' if faults else ('CLOCK' if clocks else ('ROOT' if ra else 'OTHER'))
    compound = bool(clocks or others or inh or len(faults) > 1)
    others = others + ['pinned ' + p for p in pinned]
    text = 'flip %s#%s->%s; faults=%s; others=%s; clocks=%d; inherited=%d' % (
        short(flip['siteId']), flip['ordinal'], flip['outcome'],
        ['%s[%s..%s]' % (d, r[7:15], r.split('.in.')[-1][:8]) for d, r in zip(doors, faults)],
        others, len(clocks), len(inh))
    return kind, doors, faults, compound, text


def carrier_of(fctx, doors):
    """What the faulted exchange carried, from the faulting context."""
    c = ' '.join(sorted(fctx))
    if any(d.startswith('SASL') for d in doors):
        return 'SASL data-transfer handshake'
    if 'CLIENT/heartbeat' in c:
        return 'workload heartbeat (KeyUpdateCommand carrier)'
    if 'BP_SERVICE_ACTOR' in c:
        return 'daemon BPServiceActor heartbeat'
    return 'client/service RPC (' + ','.join(sorted(set(re.sub(r'.*CLIENT/([\w-]+)#.*', r'\1', x) for x in fctx))) + ')'


def replay_stats(it, oid):
    """(idle stalls, given-up slots, events run free) from the obligation's replay.log."""
    logs = glob.glob('%s/obligations-*/%s/replay.log' % (it, oid))
    if not logs:
        return ('', '', '')
    idle = 0
    summary = ('', '')
    with open(logs[0], errors='replace') as fh:
        for line in fh:
            if 'did not happen for' in line:
                idle += 1
            m = re.search(r'of an order of (\d+) slot.*?(\d+) given up in (\d+) stall.*?(\d+) event\(s\) ran free', line)
            if m:
                summary = (m.group(2), m.group(4))
    return (idle, summary[0], summary[1])


# ----------------------------------------------------------------------------- diff
def counter_diff(a, b):
    """(new, gone) multisets: in b not a / in a not b (by multiplicity)."""
    return b - a, a - b


def coarse_occ(o):
    return (node_short(o['node']), o['regionId'][:15], ctx_coarse(o['context']))


def short_occ(k, n=3):
    return '|'.join(k.split('::')[0].split('|')[:n])


def fault_contexts(s):
    """node|ctx of every occurrence whose door decision took the throw arm."""
    return set('%s|%s' % tuple(ok.split('|')[0:3:2]) for (ok, site, ordn), door in s.door_false)


def exchange_contexts(seed, s, fctx):
    """The cut exchange(s): the faulting contexts, plus -- for each message a faulting context sent
    in the seed that is gone in the replay -- the receiving handler's context and, transitively, the
    handler of its answer. Items touching these contexts are the DIRECT cut; all else is downstream."""
    ex = set(fctx)
    seed_by_eid = dict(seed.sends)
    frontier = [eid for eid, sk in seed.sends.items() if sk[0] in fctx]
    seen = set()
    while frontier:
        eid = frontier.pop()
        if eid in seen:
            continue
        seen.add(eid)
        for eid2, sk2 in seed_by_eid.items():
            if ('Anchor:%s@' % eid) in sk2[0]:
                ex.add(sk2[0])
                frontier.append(eid2)
    # a receiving handler's ctx is named Anchor:<eid>@...; add the RECV-side contexts too
    for (sk, rn) in seed.msg:
        pass
    anchors = set()
    for eid in seen:
        anchors.add('Anchor:%s@' % eid)
    return ex, anchors


def touches(key_ctx, ex, anchors):
    """key_ctx = 'node|ctx...'"""
    if key_ctx in ex:
        return True
    return any(a in key_ctx for a in anchors)


def diff(seed, s):
    """All changes of s against the seed, as hashable items per layer."""
    I = collections.defaultdict(set)
    D = {}
    D['occ_new'], D['occ_gone'] = counter_diff(seed.occ, s.occ)
    for k in D['occ_new']:
        I['occ+'].add(k)
    for k in D['occ_gone']:
        I['occ-'].add(k)
    seed_coarse = set(coarse_occ(o) for o in seed.occ_obj.values())
    seed_nr = set(c[:2] for c in seed_coarse)
    for k in D['occ_new']:
        c = coarse_occ(s.occ_obj[k])
        if c in seed_coarse:
            I['occ+same_kind'].add(k)          # the same logical occurrence re-appears (retry/rewindow)
            if any(d in c[2] for d in DAEMON_ROLES):
                I['occ+daemon_turn'].add(k)    # one more daemon turn (actor heartbeat, tick)
        elif c[:2] not in seed_nr:
            I['occ+new_region'].add(k)         # a region never active on that node in the seed
        else:
            I['occ+new_ctx'].add(k)            # a known region under a new context kind
    gone_c = collections.Counter(coarse_occ(seed.occ_obj[k]) + (idx_render(seed.occ_obj[k]['index']),)
                                 for k in D['occ_gone'].elements())
    new_c = collections.Counter(coarse_occ(s.occ_obj[k]) + (idx_render(s.occ_obj[k]['index']),)
                                for k in D['occ_new'].elements())
    D['occ_rekeyed'] = sum((gone_c & new_c).values())
    D['wire_new'], D['wire_gone'] = counter_diff(seed.wire, s.wire)
    for e in D['wire_new']:
        I['wire+'].add(e)
    for e in D['wire_gone']:
        I['wire-'].add(e)
    D['state_new'], D['state_gone'] = counter_diff(seed.state, s.state)
    for e in D['state_new']:
        I['state+'].add(e)
    for e in D['state_gone']:
        I['state-'].add(e)
    rep = []
    for reader, ws in s.reader_writers.items():
        if reader in seed.reader_writers:
            a = tuple(sorted(seed.reader_writers[reader]))
            b = tuple(sorted(ws))
            if a != b:
                rep.append((reader, a, b))
                I['repoint'].add((reader, a, b))
    D['repointed'] = rep
    changed = []
    dnew = dgone = 0
    for k, v in s.dec.items():
        if k in seed.dec:
            sv = seed.dec[k]
            n = min(len(sv), len(v))
            if sv[:n] != v[:n]:
                changed.append((k, sv, v))
                I['dec~'].add((k, tuple(sv), tuple(v)))
            dnew += max(0, len(v) - len(sv))
            dgone += max(0, len(sv) - len(v))
        else:
            dnew += len(v)
    for k, sv in seed.dec.items():
        if k not in s.dec:
            dgone += len(sv)
    D['dec_changed'], D['dec_new'], D['dec_gone'] = changed, dnew, dgone
    D['msg_new'], D['msg_gone'] = counter_diff(seed.msg, s.msg)
    for m in D['msg_new']:
        I['msg+'].add(m)
    for m in D['msg_gone']:
        I['msg-'].add(m)
    D['undeliv_new'], _ = counter_diff(seed.undelivered, s.undelivered)
    for u in D['undeliv_new']:
        I['undelivered+'].add(u)
    D['sched_delta'] = {k: s.sched.get(k, 0) - seed.sched.get(k, 0) for k in set(seed.sched) | set(s.sched)}
    D['more_sends'] = {k: (seed.send_keys.get(k, 0), v) for k, v in s.send_keys.items()
                       if v > seed.send_keys.get(k, 0) and seed.send_keys.get(k, 0) > 0}
    for k in D['more_sends']:
        I['resend'].add(k)
    seed_pairs = collections.defaultdict(set)
    for (sk, rn) in seed.msg:
        seed_pairs[(sk[0], sk[1])].add(rn)
    new_pairs = collections.defaultdict(set)
    for (sk, rn) in s.msg:
        new_pairs[(sk[0], sk[1])].add(rn)
    for key, rns in new_pairs.items():
        if key in seed_pairs:
            for rn in rns - seed_pairs[key]:
                I['fallback_peer'].add((key[0], key[1], rn, tuple(sorted(seed_pairs[key]))))
    (D['target']) = ((seed.reached, seed.fatal), (s.reached, s.fatal), len(seed.targets), len(s.targets))
    tgt_seed = set((occ_key(t['occurrence']), t['anchorSiteId']) for t in seed.targets)
    tgt_s = set((occ_key(t['occurrence']), t['anchorSiteId']) for t in s.targets)
    for t in tgt_s - tgt_seed:
        I['target+'].add(t)
    for t in tgt_seed - tgt_s:
        I['target-'].add(t)
    D['items'] = I
    return D


DAEMON_ROLES = ('BP_SERVICE_ACTOR', 'HEARTBEAT_TICK', 'KEY_MANAGER_TICK')
NET_LAYERS = ['occ+', 'occ-', 'occ+same_kind', 'occ+daemon_turn', 'occ+new_region', 'occ+new_ctx', 'msg+', 'msg-', 'undelivered+',
              'resend', 'fallback_peer', 'wire+', 'wire-', 'state+', 'state-', 'repoint', 'dec~', 'target+',
              'target-']


def net_items(D, envelope):
    return {L: D['items'].get(L, set()) - envelope.get(L, set()) for L in NET_LAYERS}


def node_ctx_of_occ(k):
    parts = k.split('::')[0].split('|')
    return parts[0] + '|' + parts[2] if len(parts) > 2 else k


def split_direct(N, ex, anchors):
    """Partition the net items into DIRECT (the cut exchange itself) and DOWNSTREAM."""
    T = lambda nc: touches(nc, ex, anchors)
    direct = collections.defaultdict(set)
    down = collections.defaultdict(set)
    for L, items in N.items():
        for it in items:
            if L.startswith('occ'):
                hit = T(node_ctx_of_occ(it))
            elif L in ('msg+', 'msg-'):
                hit = T(it[0][0])
            elif L in ('undelivered+', 'resend'):
                hit = T(it[0])
            elif L == 'fallback_peer':
                hit = False
            elif L in ('wire+', 'wire-', 'state+', 'state-'):
                hit = (it[0] not in ('NO_PRODUCER', 'UNWRITTEN') and not it[0].startswith('MINT:')
                       and T(node_ctx_of_occ(it[0]))) or T(node_ctx_of_occ(it[1]))
            elif L == 'repoint':
                hit = T(node_ctx_of_occ(it[0]))
            elif L == 'dec~':
                hit = T(node_ctx_of_occ(it[0][0])) and door_of_site(it[0][1]) is not None
            else:
                hit = False
            (direct if hit else down)[L].add(it)
    return direct, down


def classify(D, N, ex, anchors, fnodes):
    """Patterns on the NET (fault-specific) change items."""
    P = set()
    direct, down = split_direct(N, ex, anchors)
    if N['msg-'] or N['undelivered+'] or N['wire-']:
        P.add('EDGE_CUT')
    # the same logical call again: a context re-sends on a site, or a non-daemon occurrence of a
    # known kind re-appears, or the faulting node's own daemon takes another turn (actor re-heartbeat)
    daemon_nodes = set(k.split('|')[0] for k in N['occ+daemon_turn'])
    logical = [k for k in N['occ+same_kind'] if k not in N['occ+daemon_turn']]
    own_daemon = [k for k in N['occ+daemon_turn'] if k.split('|')[0] in fnodes]
    resend = [r for r in N['resend'] if not any(d in r[0] for d in DAEMON_ROLES) or r[0].split('|')[0] in fnodes]
    if resend or logical or (own_daemon and len(daemon_nodes) <= 1):
        P.add('RETRY')
    # more daemon turns on several nodes: the run lasted longer (enforcer stall / slower workload)
    if len(daemon_nodes) >= 2:
        P.add('DAEMON_INFLATION')
    if N['fallback_peer'] or N['occ+new_region']:
        P.add('FALLBACK')
    # the same work re-done under another context on the same node (a payload that rode the cut
    # exchange is produced again for another carrier)
    gone_nr = set(tuple(k.split('|')[:2]) for k in D['items'].get('occ-', ())
                  if touches(node_ctx_of_occ(k), ex, anchors))
    rec = [k for k in N['occ+new_ctx'] if tuple(k.split('|')[:2]) in gone_nr]
    if rec:
        P.add('RECOVERY')
    if N['repoint']:
        P.add('STATE_DIVERGENCE')
    (sr, sf), (rr, rf), nst, nrt = D['target']
    if rf and not sf:
        P.add('ESCALATION')
    if sr and not rr:
        P.add('ABORT')
    elif N['target-']:
        P.add('ANCHOR_DROPPED')
    dn = sum(len(v) for L, v in down.items() if L not in ('state+', 'state-', 'dec~'))
    if not dn and not (rf and not sf) and not (sr and not rr) and not N['repoint']:
        P.add('TOLERATE')
    return P, direct, down


def msg_render(m):
    (sender, site, k), rn = m
    return '%s %s#k%s -> %s' % (sender, site, k, rn)


# ----------------------------------------------------------------------------- main
def main():
    os.makedirs(OUT, exist_ok=True)
    rows_out = []
    detail = {}
    scopes = {}
    for case in CASES:
        it, results, tasks, rnames, seed_dir, sess_dirs, roots = load_case(case)
        seed = Session(seed_dir)
        by_session = {r['sessionId']: oid for oid, r in results.items()
                      if r.get('verdict') == 'ADMITTED' and r.get('sessionId')}
        loaded = []
        for d in sess_dirs:
            sid = os.path.basename(d)
            if sid.startswith('seed-'):
                continue
            oid = by_session.get(sid)
            if oid is None:
                oids = json.load(open(d + '/manifest.json')).get('obligationIds') or []
                oid = oids[0] if oids else None
            t = tasks.get(oid)
            if t is None or results.get(oid, {}).get('verdict') != 'ADMITTED':
                continue
            kind, doors, faults, compound, wtext = world_of(t, roots)
            s = Session(d)
            s.stalls = replay_stats(it, oid)
            loaded.append((sid, oid, t, kind, doors, compound, wtext, s, diff(seed, s)))
        # the case's noise envelope: every change item any CONTROL (non-fault) replay shows
        envelope = collections.defaultdict(set)
        ncontrol = 0
        for (sid, oid, t, kind, doors, compound, wtext, s, D) in loaded:
            if kind != 'FAULT':
                ncontrol += 1
                for L, items in D['items'].items():
                    envelope[L] |= items
        for (sid, oid, t, kind, doors, compound, wtext, s, D) in loaded:
            fctx = fault_contexts(s)
            ex, anchors = exchange_contexts(seed, s, fctx)
            if kind == 'FAULT':
                N = net_items(D, envelope)
            else:  # leave-one-out envelope for a control, so controls are judged like faults
                env2 = collections.defaultdict(set)
                for (sid2, _, _, kind2, _, _, _, _, D2) in loaded:
                    if kind2 != 'FAULT' and sid2 != sid:
                        for L, items in D2['items'].items():
                            env2[L] |= items
                N = net_items(D, env2)
            P, direct, down = classify(D, N, ex, anchors, set(c.split('|')[0] for c in fctx))
            ncut_direct = len(direct['msg-']) + len(direct['undelivered+'])
            ncut_down = len(down['msg-']) + len(down['undelivered+'])
            raw = D['items']
            row = {
                'case': case, 'session': sid, 'obligation': oid, 'kind': kind, 'door': '+'.join(doors),
                'compound': int(compound), 'controls_in_envelope': ncontrol,
                'fault_ctx': ';'.join(sorted(fctx)),
                'carrier': carrier_of(fctx, doors),
                'occ_seed': sum(seed.occ.values()), 'occ_replay': sum(s.occ.values()),
                'occ_new': len(raw.get('occ+', ())), 'occ_gone': len(raw.get('occ-', ())),
                'net_occ_new': len(N['occ+']), 'net_occ_gone': len(N['occ-']),
                'net_occ_same_kind': len(N['occ+same_kind']), 'net_occ_new_region': len(N['occ+new_region']),
                'occ_rekeyed': D['occ_rekeyed'], 'lost_seed': seed.lost, 'lost_replay': s.lost,
                'msg_seed': sum(seed.msg.values()), 'msg_new': len(raw.get('msg+', ())),
                'msg_gone': len(raw.get('msg-', ())), 'net_msg_new': len(N['msg+']), 'net_msg_gone': len(N['msg-']),
                'net_undelivered_new': len(N['undelivered+']), 'net_cut_direct': ncut_direct,
                'net_cut_downstream': ncut_down, 'net_resend': len(N['resend']),
                'net_fallback_peer': len(N['fallback_peer']),
                'wire_seed': sum(seed.wire.values()), 'wire_new': len(raw.get('wire+', ())),
                'wire_gone': len(raw.get('wire-', ())), 'net_wire_new': len(N['wire+']),
                'net_wire_gone': len(N['wire-']), 'no_producer_seed': seed.no_producer,
                'no_producer_replay': s.no_producer, 'orphan_exports_seed': seed.orphan_exports,
                'orphan_exports_replay': s.orphan_exports,
                'state_seed': sum(seed.state.values()), 'state_new': len(raw.get('state+', ())),
                'state_gone': len(raw.get('state-', ())), 'repointed': len(raw.get('repoint', ())),
                'net_state_new': len(N['state+']), 'net_state_gone': len(N['state-']),
                'net_repointed': len(N['repoint']), 'unwritten_reads_seed': seed.reads_unwritten,
                'unwritten_reads_replay': s.reads_unwritten,
                'dec_changed': len(D['dec_changed']), 'net_dec_changed': len(N['dec~']),
                'dec_new': D['dec_new'], 'dec_gone': D['dec_gone'],
                'seed_reached': int(D['target'][0][0]), 'seed_fatal': int(D['target'][0][1]),
                'reached': int(D['target'][1][0]), 'fatal': int(D['target'][1][1]),
                'targets_seed': D['target'][2], 'targets_replay': D['target'][3],
                'sched_delta': ' '.join('%s%+d' % (k, v) for k, v in sorted(D['sched_delta'].items()) if v),
                'direct_items': sum(len(v) for v in direct.values()),
                'downstream_items': sum(len(v) for v in down.values()),
                'downstream_layers': ' '.join('%s=%d' % (L, len(down[L])) for L in NET_LAYERS if down[L]),
                'idle_stalls': s.stalls[0], 'slots_given_up': s.stalls[1], 'ran_free': s.stalls[2],
                'patterns': ' '.join(sorted(P)), 'world': wtext,
            }
            rows_out.append(row)
            detail[(case, sid)] = (D, N, s, seed, rnames, row)
            row['_exchange'] = ' '.join(sorted(ex))
            scopes[(case, sid)] = (direct, down)
    if not rows_out:
        print('no admitted focused replay in these cases: nothing to diff')
        return
    with open(OUT + '/sessions.csv', 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows_out[0].keys()))
        w.writeheader()
        w.writerows(rows_out)
    with open(OUT + '/fault_details.txt', 'w') as fh, open(OUT + '/control_details.txt', 'w') as fc:
        for (case, sid), v in detail.items():
            dump(fh if v[-1]['kind'] == 'FAULT' else fc, case, sid, *v)
    with open(OUT + '/net_items.csv', 'w', newline='') as fh:
        w = csv.writer(fh)
        w.writerow(['case', 'session', 'kind', 'door', 'scope', 'layer', 'item'])
        for (case, sid), (D, N, s, seed, rnames, row) in detail.items():
            direct, down = scopes[(case, sid)]
            for scope, part in (('direct', direct), ('downstream', down)):
                for L in NET_LAYERS:
                    for it in sorted(part[L], key=str):
                        w.writerow([case, sid, row['kind'], row['door'], scope, L, str(it)[:600]])
    with open(OUT + '/occ_groups.csv', 'w', newline='') as fh:
        w = csv.writer(fh)
        w.writerow(['case', 'session', 'kind', 'door', 'change', 'net', 'node', 'region', 'regionName', 'form',
                    'role_or_rpcSite', 'count'])
        for (case, sid), (D, N, s, seed, rnames, row) in detail.items():
            for tag, keys, objs in (('new', D['items'].get('occ+', set()), s.occ_obj),
                                    ('gone', D['items'].get('occ-', set()), seed.occ_obj)):
                netset = N['occ+'] if tag == 'new' else N['occ-']
                g = collections.Counter()
                for k in keys:
                    g[occ_group(objs[k]) + (int(k in netset),)] += 1
                for (n, r, f, role, net), v in sorted(g.items()):
                    w.writerow([case, sid, row['kind'], row['door'], tag, net, n, r, rnames.get(r, ''), f, role, v])
    write_pattern_table(rows_out)
    print_summary(rows_out)
    write_growth()


def write_growth():
    """growth.csv: every occurrence the closure GREW (EXPOSED_REGION, PIPELINE §7.8), the world of
    the replay that exposed it (which door's fault, or a control world), and whether a later replay
    captured it (a planned address no replay ran again is a DIAGNOSTIC 'planned at this address')."""
    out = []
    for case in CASES:
        it, results, tasks, rnames, seed_dir, sess_dirs, roots = load_case(case)
        unreproduced = set()
        for g in glob.glob(it + '/obligations-*/gaps.jsonl'):
            for r in rows(g):
                if r.get('detail', '').startswith('planned at this address'):
                    unreproduced.add(r.get('subject', ''))
        for f in sorted(glob.glob(it + '/obligations-*/growth.jsonl')):
            wave = f.split('/')[-2]
            for r in rows(f):
                t = tasks.get(r.get('obligationId'))
                kind, doors, _, _, _ = world_of(t, roots) if t else ('?', [], [], False, '')
                occ = r['occurrence']
                ctx = occ.split('/ctx:')[1].split('/idx:')[0] if '/ctx:' in occ else ''
                out.append({'case': case, 'wave': wave, 'obligation': r.get('obligationId', ''),
                            'kind': kind, 'door': '+'.join(doors), 'node': node_short(r['node']),
                            'region': r['regionId'][:15], 'regionName': rnames.get(r['regionId'][:15], ''),
                            'context': re.sub(r'Anchor:[0-9a-f]+@', 'Anchor@', ctx),
                            'captured': int(occ not in unreproduced)})
    if not out:
        return
    with open(OUT + '/growth.csv', 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=list(out[0].keys()))
        w.writeheader()
        w.writerows(out)
    print('%-12s %5s %5s %5s  %s' % ('case', 'grown', 'fault', 'capt', 'grown by (door -> node region context)'))
    by = collections.defaultdict(list)
    for r in out:
        by[r['case']].append(r)
    for case, rs in sorted(by.items()):
        top = collections.Counter('%s -> %s %s %s' % (r['door'] or r['kind'], r['node'], r['regionName']
                                                       or r['region'], r['context'][:32]) for r in rs)
        print('%-12s %5d %5d %5d  %s' % (case, len(rs), sum(r['kind'] == 'FAULT' for r in rs),
                                          sum(r['captured'] for r in rs),
                                          '; '.join('%s x%d' % kv for kv in top.most_common(3))))


PATTERNS = ['EDGE_CUT', 'TOLERATE', 'RETRY', 'RECOVERY', 'FALLBACK', 'STATE_DIVERGENCE', 'ESCALATION', 'ABORT',
            'ANCHOR_DROPPED', 'DAEMON_INFLATION']


def write_pattern_table(rows_):
    """patterns.csv: pattern counts per case, per carrier/door, and for the controls."""
    groups = collections.defaultdict(list)
    for r in rows_:
        if r['kind'] == 'FAULT':
            groups[('case', r['case'])].append(r)
            groups[('carrier', r['carrier'] + ' ' + r['door'].split('+')[0])].append(r)
            groups[('all', 'FAULT')].append(r)
            if r['compound'] == 0:
                groups[('all', 'FAULT single-flip')].append(r)
        elif r['case'] != '17960':
            groups[('all', 'CONTROL (non-fault worlds, excl. 17960)')].append(r)
    with open(OUT + '/patterns.csv', 'w', newline='') as fh:
        w = csv.writer(fh)
        w.writerow(['grouping', 'group', 'sessions', 'single_flip'] + PATTERNS)
        for (g, name), rs in sorted(groups.items()):
            pc = collections.Counter(p for r in rs for p in r['patterns'].split())
            w.writerow([g, name, len(rs), sum(1 for r in rs if r['compound'] == 0)] + [pc[p] for p in PATTERNS])


def dump(fh, case, sid, D, N, s, seed, rnames, row):
    p = fh.write
    p('=' * 100 + '\n')
    p('%s %s  kind=%s door=%s compound=%s\n  %s\n' % (case, sid, row['kind'], row['door'], row['compound'],
                                                     row['world']))
    p('  patterns(net): %s\n' % row['patterns'])
    p('  fault contexts: %s\n' % row['fault_ctx'])
    p('  cut exchange contexts: %s\n' % row['_exchange'])
    p('  net items direct=%s downstream=%s [%s]\n' % (row['direct_items'], row['downstream_items'],
                                                     row['downstream_layers']))
    p('  target seed(reached,fatal)=%s replay=%s rows %s->%s\n' % D['target'])
    p('  schedule delta: %s\n' % row['sched_delta'])
    p('  raw: occ +%d -%d (rekeyed %d)  msg +%d -%d  wire +%d -%d  state +%d -%d repoint %d  dec~ %d\n' % (
        row['occ_new'], row['occ_gone'], row['occ_rekeyed'], row['msg_new'], row['msg_gone'], row['wire_new'],
        row['wire_gone'], row['state_new'], row['state_gone'], row['repointed'], row['dec_changed']))
    p('  NET (not in any control replay of this case):\n')
    for tag, L, objs in (('+', 'occ+', s.occ_obj), ('-', 'occ-', seed.occ_obj)):
        g = collections.Counter()
        for k in N[L]:
            sub = ('same_kind' if k in N['occ+same_kind'] else 'new_region' if k in N['occ+new_region']
                   else 'new_ctx' if k in N['occ+new_ctx'] else '') if tag == '+' else ''
            g[occ_group(objs[k]) + (sub,)] += 1
        for (n, r, f, role, sub), v in sorted(g.items()):
            p('    occ%s %3d %-10s %s(%s) %s %s %s\n' % (tag, v, n, r, rnames.get(r, ''), f, role, sub))
    for m in sorted(N['msg-']):
        p('    msg- %s\n' % msg_render(m))
    for m in sorted(N['msg+']):
        p('    msg+ %s\n' % msg_render(m))
    for u in sorted(N['undelivered+']):
        p('    undelivered+ %s %s#k%s\n' % u)
    for r_ in sorted(N['resend']):
        p('    resend %s %s  (seed %s -> replay %s)\n' % (r_[0], r_[1], s.send_keys and seed.send_keys.get(r_),
                                                       s.send_keys.get(r_)))
    for f_ in sorted(N['fallback_peer']):
        p('    fallback_peer %s %s -> %s (seed peers %s)\n' % f_)
    g = collections.Counter()
    for (pk, ck) in N['wire-']:
        g[('-', short_occ(pk), pk.split('::')[1] if '::' in pk else '', short_occ(ck))] += 1
    for (pk, ck) in N['wire+']:
        g[('+', short_occ(pk), pk.split('::')[1] if '::' in pk else '', short_occ(ck))] += 1
    for (t, a, site, b), v in sorted(g.items()):
        p('    wire%s %3d %s --%s--> %s\n' % (t, v, a, site, b))
    g = collections.Counter()
    for (wk, rk) in N['state-']:
        g[('-', short_occ(wk), short_occ(rk))] += 1
    for (wk, rk) in N['state+']:
        g[('+', short_occ(wk), short_occ(rk))] += 1
    for (t, a, b), v in sorted(g.items()):
        p('    state%s %3d %s ==> %s\n' % (t, v, a, b))
    for reader, a, b in sorted(N['repoint'])[:30]:
        p('    repoint reader %s\n        seed %s\n        now  %s\n' % (
            reader[:260], [x[:170] for x in a], [x[:170] for x in b]))
    for k, a, b in sorted(N['dec~'])[:25]:
        p('    dec~ %s %s#%s  %s -> %s\n' % (k[0][:160], short(k[1]), k[2], list(a), list(b)))
    for t in sorted(N['target+']):
        p('    target+ %s %s\n' % (t[0][:160], short(t[1])))
    for t in sorted(N['target-']):
        p('    target- %s %s\n' % (t[0][:160], short(t[1])))


def print_summary(rows_):
    by = collections.defaultdict(list)
    for r in rows_:
        by[(r['case'], 'FAULT' if r['kind'] == 'FAULT' else 'CONTROL')].append(r)
    print('%-12s %-8s %3s %s' % ('case', 'set', 'n', 'patterns (net of control noise)'))
    for (c, k), rs in sorted(by.items()):
        pc = collections.Counter()
        for r in rs:
            for p in r['patterns'].split():
                pc[p] += 1
        print('%-12s %-8s %3d %s' % (c, k, len(rs), dict(sorted(pc.items()))))


if __name__ == '__main__':
    main()

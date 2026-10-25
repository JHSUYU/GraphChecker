#!/usr/bin/env python3
"""final-stats.py: the final table of a system's cases on CloudLab (as results/hbase, results/hdfs): per case its final
run (the first round of --order whose run accept-<round>-<short> has a summary row), its verdict, time in four parts
and the final closure's size.  seeding = PREFLIGHT..IMPORT (+ZKKEYS); exploration = EXPLORE; compose+solver =
COMPOSE + SOLVE + DECIDE; other = CONFIRM + EMIT + REPRODUCE; refuted = the wall of the claims CONFIRM refuted before
the last (stage_metrics.tsv times only the last claim); regions / occurrences = the final closure; rounds = EXPLORE's
obligation generations; replays = the obligation replays EXPLORE ran, and on how many nodes.

With --util <dir> (tools/cloudlab/util-sampler.sh's rows) it adds what the five nodes did over each case's window
(its summary row's time back by its wall): the cluster's mean CPU busy % over the whole case and over its
exploration (the seeding's end to the exploration's), the highest 15-s cluster CPU %, and the most memory any node
had in use.  A round --alone names ran its case alone on the five nodes; any other ran beside other cases.
Usage: final-stats.py --order B1 --cases experiments/hbase/hbase-cases.tsv --out /bulk/gc-out/hbase-final
       [--alone B1] [--util /bulk/gc-out/hbase-final/util]"""
import argparse, collections, glob, json, os, re

SEED = ['PREFLIGHT', 'FREEZE_TOOL', 'SETUP', 'FREEZE', 'SEED', 'PLAN', 'INSTRUMENT', 'REPLAY', 'IMPORT', 'ZKKEYS']
COMPOSE = ['COMPOSE', 'SOLVE', 'DECIDE']
OTHER = ['CONFIRM', 'EMIT', 'REPRODUCE']


def short(case):
    return case.split('-', 1)[1]


def ended(path):
    return os.path.exists(path) and sum(1 for _ in open(path)) >= 2


def samples(util):
    """{epoch // 15: {host: (cpu, mem_mb, total_mb)}} over every host's rows."""
    rows = collections.defaultdict(dict)
    for path in glob.glob(os.path.join(util or '', '*.tsv')):
        host = os.path.basename(path)[:-4]
        for line in open(path):
            f = line.split()
            if len(f) < 5:
                continue
            rows[int(f[0]) // 15][host] = (int(f[1]), int(f[3]), int(f[4]))
    return rows


def window(rows, start, end):
    ticks = [rows[t] for t in sorted(rows) if start // 15 <= t <= end // 15]
    if not ticks:
        return None
    cluster = [sum(c for c, _, _ in t.values()) / len(t) for t in ticks]
    mem = max(m for t in ticks for _, m, _ in t.values())
    return dict(cpu=sum(cluster) / len(cluster), cpuPeak=max(cluster), memPeak=mem / 1024.0)


def replays(it):
    hosts = collections.Counter()
    for path in glob.glob(os.path.join(it, 'obligations-*', '*', 'replay-host.txt')):
        try:
            hosts[open(path).read().strip()] += 1
        except OSError:
            pass
    return sum(hosts.values()), len(hosts)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--out', required=True, help='the GC_OUT the runs wrote')
    p.add_argument('--order', required=True, help='rounds, most final first, comma-separated')
    p.add_argument('--cases', required=True, help='experiments/<system>/<system>-cases.tsv')
    p.add_argument('--alone', default='', help='rounds that ran alone')
    p.add_argument('--util', default='', help="util-sampler.sh's directory")
    a = p.parse_args()
    order = [r for r in a.order.split(',') if r]
    alone = set(r for r in a.alone.split(',') if r)
    util = samples(a.util) if a.util else {}
    rows = []
    for line in open(a.cases):
        if not line.strip() or line.startswith('#'):
            continue
        case = line.split('\t')[0]
        run = None
        for r in order:
            if ended(os.path.join(a.out, 'accept-%s-%s' % (r, short(case)), 'summary.tsv')):
                run = r
                break
        if run is None:
            rows.append(dict(case=case, run='-'))
            continue
        tag = '%s-%s' % (run, short(case))
        d = os.path.join(a.out, 'accept-' + tag)
        summary = os.path.join(d, 'summary.tsv')
        last = open(summary).read().strip().split('\n')[-1].split('\t')
        sched = os.path.join(d, 'out', case, 'schedule')
        m = {}
        try:
            for l in open(os.path.join(sched, 'stage_metrics.tsv')):
                k, v = l.split('\t')
                m[k] = int(v)
        except FileNotFoundError:
            pass
        sec = lambda ks: round(sum(m.get(k, 0) for k in ks) / 1000.0)
        regions, occ = set(), 0
        it = os.path.join(sched, 'iteration-0000')
        plans = sorted(glob.glob(os.path.join(it, 'generations', 'g*', 'execution_task_plan.jsonl')))
        plan = plans[-1] if plans else os.path.join(it, 'execution_task_plan.jsonl')
        if os.path.exists(plan):
            for l in open(plan):
                occ += 1
                regions.add(json.loads(l).get('regionId'))
        rounds = len(glob.glob(os.path.join(it, 'obligations-*')))
        refuted = len(glob.glob(os.path.join(sched, 'final', 'refuted', '*')))
        finding = last[12] if len(last) > 12 else ''
        native = re.search(r'reproduced (\d+/\d+) natively', finding)
        mech = finding.split('|')[0].split(' at ')[0].strip()
        wall = int(last[2])
        n_replays, n_hosts = replays(it)
        row = dict(case=case, run=tag, mode='alone' if run in alone else 'concurrent', claim=last[3],
                   blockers=last[5], wall=wall, seeding=sec(SEED), exploration=sec(['EXPLORE']),
                   compose=sec(COMPOSE), other=sec(OTHER), refutedClaims=refuted,
                   refuted=wall - sec(SEED + ['EXPLORE'] + COMPOSE + OTHER) if refuted else 0,
                   regions=len(regions), occ=occ, rounds=rounds, replays=n_replays, replayHosts=n_hosts,
                   mech=mech, native=native.group(1) if native else '-')
        if util:
            end = int(os.path.getmtime(summary))
            start = end - wall
            whole = window(util, start, end)
            explore = window(util, start + row['seeding'], start + row['seeding'] + row['exploration'])
            if whole:
                row.update(cpu='%.0f' % whole['cpu'], cpuPeak='%.0f' % whole['cpuPeak'],
                           memPeak='%.0f' % whole['memPeak'],
                           cpuExplore='%.0f' % explore['cpu'] if explore else '-')
        rows.append(row)
    keys = ['case', 'run', 'mode', 'claim', 'mech', 'native', 'blockers', 'wall', 'seeding', 'exploration', 'compose',
            'other', 'refutedClaims', 'refuted', 'regions', 'occ', 'rounds', 'replays', 'replayHosts']
    ukeys = ['cpu', 'cpuExplore', 'cpuPeak', 'memPeak'] if util else []
    print('\t'.join(keys + ukeys))
    for r in rows:
        print('\t'.join(str(r.get(k, '-')) for k in keys + ukeys))
    print()
    head = ('| case | run | mode | claim | mechanism | native | wall (s) | seeding (s) | exploration (s) '
            '| compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds | replays (nodes) |')
    rule = '| --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |'
    if util:
        head += ' CPU % case | CPU % explore | CPU % peak | node mem peak (GB) |'
        rule += ' ---: | ---: | ---: | ---: |'
    print(head)
    print(rule)
    for r in rows:
        if r['run'] == '-':
            print('| %s | not run yet |' % r['case'] + '  |' * (head.count('|') - 3))
            continue
        line = ('| %(case)s | %(run)s | %(mode)s | %(claim)s | %(mech)s | %(native)s | %(wall)d | %(seeding)d '
                '| %(exploration)d | %(compose)d | %(other)d | %(ref)s | %(regions)d | %(occ)d | %(rounds)d '
                '| %(replays)d (%(replayHosts)d) |'
                % dict(r, ref='%d (%d)' % (r['refuted'], r['refutedClaims']) if r['refutedClaims'] else '-'))
        if util:
            line += ' %s | %s | %s | %s |' % tuple(r.get(k, '-') for k in ukeys)
        print(line)
    done = [r for r in rows if r['run'] != '-']
    if done:
        tot = {k: sum(r[k] for r in done) for k in ['wall', 'seeding', 'exploration', 'compose', 'other', 'refuted']}
        print('\n%d of %d cases; wall %d s (%.1f h); seeding %d, exploration %d, compose+solver %d, other %d, '
              'refuted claims %d s' % (len(done), len(rows), tot['wall'], tot['wall'] / 3600.0, tot['seeding'],
                                       tot['exploration'], tot['compose'], tot['other'], tot['refuted']))


if __name__ == '__main__':
    main()

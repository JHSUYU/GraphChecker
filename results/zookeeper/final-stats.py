#!/usr/bin/env python3
"""final-stats.py -- the ZooKeeper final table, ported from HBase's analysis/hbase-2026-10-20/lead/final-stats.py: per
case its final run (the first round of ORDER whose run accept-<round>-<short> has a summary row), its verdict, time in
four parts and the final closure's region count. seeding = PREFLIGHT..IMPORT (+ZKKEYS); exploration = EXPLORE;
compose+solver = COMPOSE + SOLVE + DECIDE; other = CONFIRM + EMIT + REPRODUCE; refuted = the compose and CONFIRM of the
claims CONFIRM refuted before the last (final/refuted/<n>): stage_metrics.tsv times only the last claim, so it is the wall
the stages leave uncovered. regions = distinct regionId of the final
closure's execution_task_plan.jsonl, occurrences = its rows; rounds = EXPLORE's obligation generations. A round named
F2* or F3* (HBase's rule), or one --alone names, ran its case alone; any other (F1*) ran concurrently.
Usage: final-stats.py --order F2S,F1B --cases <final snapshot>/experiments/zookeeper/zookeeper-cases.tsv
       [--out /bigtemp/vnr3ne/gc-out/zookeeper-final] [--alone F2S,F2T]. Prints TSV, then the markdown table."""
import argparse, glob, json, os, re

SEED = ['PREFLIGHT', 'FREEZE_TOOL', 'SETUP', 'FREEZE', 'SEED', 'PLAN', 'INSTRUMENT', 'REPLAY', 'IMPORT', 'ZKKEYS']
COMPOSE = ['COMPOSE', 'SOLVE', 'DECIDE']
OTHER = ['CONFIRM', 'EMIT', 'REPRODUCE']
SHORT = {'zk-bugs-quota-init': 'quota', 'zk-bugs-election-offer': 'offer', 'zk-bugs-container-reuse': 'cont',
         'zk-bugs-retry-seq-quota': 'rseq', 'zk-bugs-trunc-sync': 'trunc', 'zk-bugs-observer-master': 'om'}


def short(case):
    if case in SHORT:
        return SHORT[case]
    return case[len('zk-adhoc-'):] if case.startswith('zk-adhoc-') else case[len('zk-'):]


def ended(path):
    return os.path.exists(path) and sum(1 for _ in open(path)) >= 2


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--out', default='/bigtemp/vnr3ne/gc-out/zookeeper-final')
    p.add_argument('--order', required=True, help='rounds, most final first, comma-separated')
    p.add_argument('--cases', required=True, help="the final snapshot's experiments/zookeeper/zookeeper-cases.tsv")
    p.add_argument('--alone', default='', help='rounds that ran alone (default: F2* and F3*)')
    a = p.parse_args()
    order = [r for r in a.order.split(',') if r]
    alone = set(r for r in a.alone.split(',') if r)
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
        last = open(os.path.join(d, 'summary.tsv')).read().strip().split('\n')[-1].split('\t')
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
        rows.append(dict(case=case, run=tag, mode='alone' if (run in alone or (not alone and run[:2] in ('F2', 'F3')))
                         else 'concurrent', claim=last[3], blockers=last[5], wall=int(last[2]), seeding=sec(SEED),
                         exploration=sec(['EXPLORE']), compose=sec(COMPOSE), other=sec(OTHER), refutedClaims=refuted,
                         refuted=int(last[2]) - sec(SEED + ['EXPLORE'] + COMPOSE + OTHER) if refuted else 0,
                         regions=len(regions),
                         occ=occ, rounds=rounds, mech=mech, native=native.group(1) if native else '-'))
    keys = ['case', 'run', 'mode', 'claim', 'mech', 'native', 'blockers', 'wall', 'seeding', 'exploration', 'compose',
            'other', 'refutedClaims', 'refuted', 'regions', 'occ', 'rounds']
    print('\t'.join(keys))
    for r in rows:
        print('\t'.join(str(r.get(k, '-')) for k in keys))
    print()
    print('| case | run | mode | claim | mechanism | native | wall (s) | seeding (s) | exploration (s) '
          '| compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |')
    print('| --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |')
    for r in rows:
        if r['run'] == '-':
            print('| %s | not run yet |  |  |  |  |  |  |  |  |  |  |  |  |  |' % r['case'])
            continue
        print('| %(case)s | %(run)s | %(mode)s | %(claim)s | %(mech)s | %(native)s | %(wall)d | %(seeding)d '
              '| %(exploration)d | %(compose)d | %(other)d | %(ref)s | %(regions)d | %(occ)d | %(rounds)d |'
              % dict(r, ref='%d (%d)' % (r['refuted'], r['refutedClaims']) if r['refutedClaims'] else '-'))
    done = [r for r in rows if r['run'] != '-']
    if done:
        tot = {k: sum(r[k] for r in done) for k in ['wall', 'seeding', 'exploration', 'compose', 'other', 'refuted']}
        print('\n%d of %d cases; wall %d s (%.1f h); seeding %d, exploration %d, compose+solver %d, other %d, '
              'refuted claims %d s' % (len(done), len(rows), tot['wall'], tot['wall'] / 3600.0, tot['seeding'],
                                       tot['exploration'], tot['compose'], tot['other'], tot['refuted']))


if __name__ == '__main__':
    main()

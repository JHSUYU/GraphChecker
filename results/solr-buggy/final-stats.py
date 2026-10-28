#!/usr/bin/env python3
"""final-stats.py: the buggy-detect table on liftlab (results/hdfs's final-stats.py for the old-bug cases): per case of
<sys>-buggy-cases.tsv its run (accept-<round>-<case>, tools/rounds/launch-round.sh's name: hdfs-* loses its hdfs-),
the bug, the ad hoc point, the verdict, CONFIRM, native REPRODUCE (reproduced / runs, by IDENTITY 9 shape where it
answered so, the control's fatal at the anchor / runs), time in four parts and the final closure's size.
seeding = PREFLIGHT..IMPORT (+ZKKEYS); exploration = EXPLORE; compose+solver = COMPOSE + SOLVE + DECIDE;
other = CONFIRM + EMIT + REPRODUCE; refuted claims = the wall of the claims CONFIRM refuted before the last (their
count in brackets); regions / occurrences = the final closure; rounds = EXPLORE's generations.
Usage: final-stats.py --cases experiments/<sys>/<sys>-buggy-cases.tsv [--round B1] [--out /bigtemp/vnr3ne/gc-out/buggy-detect]"""
import argparse, glob, json, os
SEED = ['PREFLIGHT', 'FREEZE_TOOL', 'SETUP', 'FREEZE', 'SEED', 'PLAN', 'INSTRUMENT', 'REPLAY', 'IMPORT', 'ZKKEYS']
COMPOSE = ['COMPOSE', 'SOLVE', 'DECIDE']
OTHER = ['CONFIRM', 'EMIT', 'REPRODUCE']


def suffix(case):
    return case[len('hdfs-'):] if case.startswith('hdfs-') else case


def load(path):
    try:
        return json.load(open(path))
    except (OSError, ValueError):
        return {}


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--out', default='/bigtemp/vnr3ne/gc-out/buggy-detect')
    p.add_argument('--round', default='B1')
    p.add_argument('--cases', required=True)
    a = p.parse_args()
    rows = []
    for line in open(a.cases):
        if not line.strip() or line.startswith('#'):
            continue
        f = line.rstrip('\n').split('\t')
        case, jira, point = f[0], f[3] if len(f) > 3 else '-', f[4] if len(f) > 4 else '-'
        tag = '%s-%s' % (a.round, suffix(case))
        d = os.path.join(a.out, 'accept-' + tag)
        s = os.path.join(d, 'summary.tsv')
        if not (os.path.exists(s) and sum(1 for _ in open(s)) >= 2):
            rows.append(dict(case=case, jira=jira, point=point, run='-'))
            continue
        last = open(s).read().strip().split('\n')[-1].split('\t')
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
        rep = load(os.path.join(sched, 'final', 'reproduce.json'))
        conf = load(os.path.join(sched, 'final', 'confirm.json'))
        native = '-'
        if rep.get('runs'):
            native = '%d/%d' % (rep.get('reproduced', 0), rep['runs'])
            if rep.get('reproducedByShape'):
                native += ', by shape %d/%d' % (rep['reproducedByShape'], rep['runs'])
            c = rep.get('control', {})
            native += '; control %d/%d' % (c.get('atAnchor', 0), c.get('runs', 0))
        finding = last[12] if len(last) > 12 else ''
        refuted = len(glob.glob(os.path.join(sched, 'final', 'refuted', '*')))
        wall = int(last[2])
        parts = sec(SEED + ['EXPLORE'] + COMPOSE + OTHER)
        rows.append(dict(case=case, jira=jira, point=point, run=tag, claim=last[3], verdict=last[10] if len(last) > 10 else '-',
                         mech=finding.split('|')[0].split(' at ')[0].strip() or '-',
                         confirm='yes' if conf.get('confirmed') else 'no', native=native, wall=wall,
                         ref='%d (%d)' % (wall - parts, refuted) if refuted else '-',
                         seeding=sec(SEED), exploration=sec(['EXPLORE']), compose=sec(COMPOSE), other=sec(OTHER),
                         regions=len(regions), occ=occ, rounds=len(glob.glob(os.path.join(it, 'obligations-*')))))
    print('| case | bug | point | run | claim | report.py | mechanism | CONFIRM | native REPRODUCE | wall (s) '
          '| seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |')
    print('| --- | --- | --- | --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |')
    for r in rows:
        if r['run'] == '-':
            print('| %(case)s | %(jira)s | %(point)s | no run |  |  |  |  |  |  |  |  |  |  |  |  |  |  |' % r)
            continue
        print('| %(case)s | %(jira)s | %(point)s | %(run)s | %(claim)s | %(verdict)s | %(mech)s | %(confirm)s | %(native)s '
              '| %(wall)d | %(seeding)d | %(exploration)d | %(compose)d | %(other)d | %(ref)s | %(regions)d | %(occ)d | %(rounds)d |' % r)
    done = [r for r in rows if r['run'] != '-']
    if done:
        tot = {k: sum(r[k] for r in done) for k in ['wall', 'seeding', 'exploration', 'compose', 'other']}
        print('\n%d of %d cases ran (%s, beside each other on liftlab); wall %d s; seeding %d, exploration %d, '
              'compose+solver %d, other %d' % (len(done), len(rows), a.round, tot['wall'], tot['seeding'],
                                               tot['exploration'], tot['compose'], tot['other']))


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""final-stats.py -- the Solr final table, as results/zookeeper/final-stats.py on system/zookeeper: per case of
index.tsv (case, run dir under /bigtemp/vnr3ne/gc-out, claim) its verdict, time in five parts and the final closure's
region count. seeding = PREFLIGHT..IMPORT (+ZKKEYS); exploration = EXPLORE; compose+solver = COMPOSE + SOLVE + DECIDE;
other = CONFIRM + EMIT + REPRODUCE; refuted = the compose and CONFIRM of the claims CONFIRM refuted before the last
(final/refuted/<n>): stage_metrics.tsv times only the last claim, so it is the wall the stages leave uncovered.
regions = distinct regionId of the final closure's execution_task_plan.jsonl, occurrences = its rows; rounds =
EXPLORE's obligation generations. The round is the run dir's name: SGF7, SGF9 and X1 (the owed cases' exclusive series,
2026-10-22/23) ran each case alone, R1-R4 concurrently.

Usage: final-stats.py [--index results/solr/index.tsv] [--out /bigtemp/vnr3ne/gc-out]. Prints TSV, then the markdown
table."""
import argparse, glob, gzip, json, os, re

SEED = ['PREFLIGHT', 'FREEZE_TOOL', 'SETUP', 'FREEZE', 'SEED', 'PLAN', 'INSTRUMENT', 'REPLAY', 'IMPORT', 'ZKKEYS']
COMPOSE = ['COMPOSE', 'SOLVE', 'DECIDE']
OTHER = ['CONFIRM', 'EMIT', 'REPRODUCE']
ALONE = ('SGF7', 'SGF8', 'SGF9', 'X1')


def lines(path):
    for p in (path, path + '.gz'):
        if os.path.exists(p):
            return (gzip.open(p, 'rt') if p.endswith('.gz') else open(p)).read().splitlines()
    return []


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    p = argparse.ArgumentParser()
    p.add_argument('--index', default=os.path.join(here, 'index.tsv'))
    p.add_argument('--out', default='/bigtemp/vnr3ne/gc-out')
    a = p.parse_args()
    rows = []
    for line in open(a.index):
        if not line.strip() or line.startswith('case\t') or line.startswith('#'):
            continue
        case, run = line.rstrip('\n').split('\t')[:2]
        d = os.path.join(a.out, run)
        last = open(os.path.join(d, 'summary.tsv')).read().strip().split('\n')[-1].split('\t')
        sched = os.path.join(d, 'out', case, 'schedule')
        m = {}
        for l in lines(os.path.join(sched, 'stage_metrics.tsv')):
            k, v = l.split('\t')
            m[k] = int(v)
        sec = lambda ks: round(sum(m.get(k, 0) for k in ks) / 1000.0)
        regions, occ = set(), 0
        it = os.path.join(sched, 'iteration-0000')
        plans = sorted(glob.glob(os.path.join(it, 'generations', 'g*', 'execution_task_plan.jsonl*')))
        plan = plans[-1].replace('.gz', '') if plans else os.path.join(it, 'execution_task_plan.jsonl')
        for l in lines(plan):
            occ += 1
            regions.add(json.loads(l).get('regionId'))
        rounds = len(glob.glob(os.path.join(it, 'obligations-*')))
        refuted = len(glob.glob(os.path.join(sched, 'final', 'refuted', '*')))
        finding = last[12] if len(last) > 12 else ''
        native = re.search(r'reproduced (\d+/\d+) natively', finding)
        rj = os.path.join(sched, 'final', 'reproduce.json')
        if os.path.exists(rj):
            j = json.load(open(rj))
            if j.get('runs'):
                native = re.match(r'(.*)', '%d/%d' % (j.get('reproduced', 0), j['runs']))
        mech = finding.split('|')[0].split(' at ')[0].strip()
        rnd = os.path.basename(run)[len('accept-'):].split('-')[0]
        stages = sec(SEED + ['EXPLORE'] + COMPOSE + OTHER)
        rows.append(dict(case=case, run=os.path.basename(run)[len('accept-'):],
                         mode='alone' if rnd.startswith(ALONE) else 'concurrent', claim=last[3], blockers=last[5],
                         wall=int(last[2]), seeding=sec(SEED), exploration=sec(['EXPLORE']), compose=sec(COMPOSE),
                         other=sec(OTHER), refutedClaims=refuted, refuted=int(last[2]) - stages if refuted else 0,
                         regions=len(regions), occ=occ, rounds=rounds, mech=mech,
                         native=native.group(1) if native else '-'))
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
        print('| %(case)s | %(run)s | %(mode)s | %(claim)s | %(mech)s | %(native)s | %(wall)d | %(seeding)d '
              '| %(exploration)d | %(compose)d | %(other)d | %(ref)s | %(regions)d | %(occ)d | %(rounds)d |'
              % dict(r, ref='%d (%d)' % (r['refuted'], r['refutedClaims']) if r['refutedClaims'] else '-'))
    tot = {k: sum(r[k] for r in rows) for k in ['wall', 'seeding', 'exploration', 'compose', 'other', 'refuted']}
    print('\n%d cases; wall %d s (%.1f h); seeding %d, exploration %d, compose+solver %d, other %d, refuted claims %d s'
          % (len(rows), tot['wall'], tot['wall'] / 3600.0, tot['seeding'], tot['exploration'], tot['compose'],
             tot['other'], tot['refuted']))


if __name__ == '__main__':
    main()

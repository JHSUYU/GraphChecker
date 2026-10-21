#!/usr/bin/env python3
"""final-stats.py -- the HBase final table (owner 2026-10-20): per case its final run in gc-out/hbase-final (the exclusive
F2* run if any, else the kept concurrent F1* run, owner: runs under 30 min are not rerun), its verdict, time in four parts
and the final closure's region count. As Solr's analysis/solr-2026-10-14/final-stats.py and HDFS's EX1 stats.py:
seeding = PREFLIGHT..IMPORT (+ZKKEYS); exploration = EXPLORE; compose+solver = COMPOSE + SOLVE + DECIDE;
other = CONFIRM + EMIT + REPRODUCE. regions = distinct regionId of the final closure's execution_task_plan.jsonl,
occurrences = its rows; rounds = EXPLORE's obligation generations. Prints TSV, then the markdown table."""
import json, os, re, sys, glob
O = '/bigtemp/vnr3ne/gc-out/hbase-final'
CASES = '/u/vnr3ne/gc-run/hb-int-16/experiments/hbase/hbase-cases.tsv'
ORDER = ['F3S', 'F2S', 'F2T', 'F2B', 'F1U', 'F1T', 'F1H', 'F1B']
SEED = ['PREFLIGHT', 'FREEZE_TOOL', 'SETUP', 'FREEZE', 'SEED', 'PLAN', 'INSTRUMENT', 'REPLAY', 'IMPORT', 'ZKKEYS']
COMPOSE = ['COMPOSE', 'SOLVE', 'DECIDE']
OTHER = ['CONFIRM', 'EMIT', 'REPRODUCE']
rows = []
for line in open(CASES):
    if not line.strip() or line.startswith('#'): continue
    case = line.split('\t')[0]
    tail = case[len('hbase-'):]
    run = None
    for r in ORDER:
        s = os.path.join(O, 'accept-%s-%s' % (r, tail), 'summary.tsv')
        if os.path.exists(s) and sum(1 for _ in open(s)) >= 2:
            run = '%s-%s' % (r, tail); break
    if run is None:
        rows.append(dict(case=case, run='-')); continue
    d = os.path.join(O, 'accept-' + run)
    last = open(os.path.join(d, 'summary.tsv')).read().strip().split('\n')[-1].split('\t')
    sched = os.path.join(d, 'out', case, 'schedule')
    m = {}
    try:
        for l in open(os.path.join(sched, 'stage_metrics.tsv')):
            k, v = l.split('\t'); m[k] = int(v)
    except FileNotFoundError: pass
    sec = lambda ks: round(sum(m.get(k, 0) for k in ks) / 1000.0)
    regions, occ = set(), 0
    it = os.path.join(sched, 'iteration-0000')
    plans = sorted(glob.glob(os.path.join(it, 'generations', 'g*', 'execution_task_plan.jsonl')))
    plan = plans[-1] if plans else os.path.join(it, 'execution_task_plan.jsonl')
    if os.path.exists(plan):
        for l in open(plan):
            r = json.loads(l); occ += 1; regions.add(r.get('regionId'))
    rounds = len(glob.glob(os.path.join(it, 'obligations-*')))
    native = re.search(r'reproduced (\d+/\d+) natively', last[12] if len(last) > 12 else '')
    mech = (last[12].split('|')[0].split(' at ')[0].strip() if len(last) > 12 else '')
    rows.append(dict(case=case, run=run, mode='alone' if run[:2] in ('F2', 'F3') else 'concurrent', claim=last[3],
                     blockers=last[5], wall=int(last[2]), seeding=sec(SEED), exploration=sec(['EXPLORE']),
                     compose=sec(COMPOSE), other=sec(OTHER), regions=len(regions), occ=occ, rounds=rounds,
                     mech=mech, native=native.group(1) if native else '-'))
keys = ['case', 'run', 'mode', 'claim', 'mech', 'native', 'blockers', 'wall', 'seeding', 'exploration', 'compose',
        'other', 'regions', 'occ', 'rounds']
print('\t'.join(keys))
for r in rows: print('\t'.join(str(r.get(k, '-')) for k in keys))
print()
print('| case | run | mode | claim | mechanism | native | wall (s) | seeding (s) | exploration (s) | compose+solver (s) '
      '| other (s) | regions | occurrences | rounds |')
print('| --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |')
for r in rows:
    if r['run'] == '-':
        print('| %s | not run yet |  |  |  |  |  |  |  |  |  |  |  |  |' % r['case']); continue
    print('| %(case)s | %(run)s | %(mode)s | %(claim)s | %(mech)s | %(native)s | %(wall)d | %(seeding)d | %(exploration)d '
          '| %(compose)d | %(other)d | %(regions)d | %(occ)d | %(rounds)d |' % r)
done = [r for r in rows if r['run'] != '-']
if done:
    tot = {k: sum(r[k] for r in done) for k in ['wall', 'seeding', 'exploration', 'compose', 'other']}
    print('\n%d of %d cases; wall %d s (%.1f h); seeding %d, exploration %d, compose+solver %d, other %d s'
          % (len(done), len(rows), tot['wall'], tot['wall'] / 3600.0, tot['seeding'], tot['exploration'],
             tot['compose'], tot['other']))

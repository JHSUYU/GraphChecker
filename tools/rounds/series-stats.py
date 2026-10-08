#!/usr/bin/env python3
"""series-stats.py <round> -- per finished run accept-<round>-* under GC_OUT (tools/lib/gc-env.sh's default
when unset): its claim, the time breakdown in seconds and the final closure's size, one tab-separated row per
case, as docs/design/PERFORMANCE.md §6 reports series EX1 (tools/rounds/run-series.sh).

  analysis        = PREFLIGHT..IMPORT (FREEZE, SEED: the static passes and the recording, PLAN, INSTRUMENT,
                    the seed REPLAY, IMPORT)
  exploration     = EXPLORE
  compose_solver  = COMPOSE + SOLVE + DECIDE
  other           = CONFIRM + EMIT + REPRODUCE
  regions, tasks  = distinct regionIds and rows of the last execution_task_plan.jsonl
  rounds          = EXPLORE's obligation rounds; answered = obligations answered"""
import glob
import json
import os
import subprocess
import sys

ANALYSIS = ['PREFLIGHT', 'FREEZE_TOOL', 'SETUP', 'FREEZE', 'SEED', 'PLAN', 'INSTRUMENT', 'REPLAY', 'IMPORT']
COMPOSE = ['COMPOSE', 'SOLVE', 'DECIDE']
OTHER = ['CONFIRM', 'EMIT', 'REPRODUCE']

here = os.path.dirname(os.path.abspath(__file__))
gc_out = os.environ.get('GC_OUT') or subprocess.run(
    ['bash', '-c', 'source "$1" && printf %s "$GC_OUT"', '_', os.path.join(here, '..', 'lib', 'gc-env.sh')],
    capture_output=True, text=True, check=True).stdout
round_name = sys.argv[1]
print('case\trun\tclaim\treport\twall_s\tanalysis_s\texploration_s\tcompose_solver_s\tother_s'
      '\tregions\ttasks\trounds\tanswered')
for run in sorted(glob.glob(os.path.join(gc_out, 'accept-%s-*' % round_name))):
    summary = os.path.join(run, 'summary.tsv')
    if not os.path.exists(summary):
        continue
    lines = open(summary).read().strip().split('\n')
    if len(lines) < 2:
        continue
    last = lines[-1].split('\t')
    case = last[0]
    sched = os.path.join(run, 'out', case, 'schedule')
    metrics = {}
    if os.path.exists(os.path.join(sched, 'stage_metrics.tsv')):
        for line in open(os.path.join(sched, 'stage_metrics.tsv')):
            key, value = line.split('\t')
            metrics[key] = int(value)
    seconds = lambda keys: sum(metrics.get(k, 0) for k in keys) / 1000.0
    plan = os.path.join(sched, 'iteration-0000', 'execution_task_plan.jsonl')
    regions, tasks = set(), 0
    if os.path.exists(plan):
        for line in open(plan):
            tasks += 1
            regions.add(json.loads(line).get('regionId'))
    rounds = len(glob.glob(os.path.join(sched, 'iteration-0000', 'obligations-*')))
    exploration = os.path.join(sched, 'iteration-0000', 'exploration.json')
    answered = json.load(open(exploration)).get('answered') if os.path.exists(exploration) else None
    print('%s\t%s\t%s\t%s\t%s\t%.0f\t%.0f\t%.0f\t%.0f\t%d\t%d\t%d\t%s' % (
        case, os.path.basename(run)[len('accept-'):], last[3], last[10], last[2], seconds(ANALYSIS),
        seconds(['EXPLORE']), seconds(COMPOSE), seconds(OTHER), len(regions), tasks, rounds, answered))

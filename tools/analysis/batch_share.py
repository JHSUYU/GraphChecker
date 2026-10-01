#!/usr/bin/env python3
"""batch_share.py <batch-output-dir> : how much of a batch campaign's
per-target seed plans one shared seed replay could run as one plan
(ADHOC-INFRA §3.5, measurement (i)), from each target's
targets/<name>/schedule/iteration-0000/execution_task_plan.jsonl.

Per pair of targets, over the occurrences both plan a task at:
  identical   the same task (one id): a union plan holds it once;
  M1          the same body -- every field but the id, the target branch,
              the observed sites and the replay group -- with another
              target branch: one task would carry both targets' branches
              (a list the runtime does not have);
  conflict    different bodies at one occurrence: separate seed replays.
And, over the regions only one of the pair plans, how often a region of one
is rooted inside a method the other weaves (its root among the other's
branch methods): in one replay the nested region's activation would take
the events the other target's plan files under its own region.

Prints one row per pair and the totals; M1 coverage is (identical + M1) /
shared occurrences."""
import collections
import glob
import itertools
import json
import os
import sys

IGNORED = {"taskId", "targetBranch", "observedSites", "replayGroupId"}


def plans(batch):
    found = {}
    for path in sorted(glob.glob(os.path.join(
            batch, "targets", "*", "schedule", "iteration-0000",
            "execution_task_plan.jsonl"))):
        name = path.split(os.sep)[-4]
        found[name] = [json.loads(line) for line in open(path) if line.strip()]
    return found


def body(task):
    return json.dumps({k: v for k, v in task.items() if k not in IGNORED},
                      sort_keys=True)


def main():
    batch = sys.argv[1]
    targets = plans(batch)
    totals = collections.Counter()
    print("pair\tshared\tidentical\tM1\tconflict\tnested")
    for (a, tasks_a), (b, tasks_b) in itertools.combinations(
            sorted(targets.items()), 2):
        by_a = {t["occurrenceId"]: t for t in tasks_a}
        by_b = {t["occurrenceId"]: t for t in tasks_b}
        counts = collections.Counter()
        for occurrence in set(by_a) & set(by_b):
            counts["shared"] += 1
            left, right = by_a[occurrence], by_b[occurrence]
            if left["taskId"] == right["taskId"]:
                counts["identical"] += 1
            elif body(left) == body(right):
                counts["M1"] += 1
            else:
                counts["conflict"] += 1
        regions_a = {t["regionId"]: t for t in tasks_a}
        regions_b = {t["regionId"]: t for t in tasks_b}
        for outer, inner in ((regions_a, regions_b), (regions_b, regions_a)):
            for region, task in inner.items():
                if region in outer:
                    continue
                root = (task.get("rootSelector") or {}).get("method", "")
                if any(root in (o.get("branchMethods") or [])
                       for o in outer.values()):
                    counts["nested"] += 1
        totals.update(counts)
        print("%s|%s\t%d\t%d\t%d\t%d\t%d" % (
            a, b, counts["shared"], counts["identical"], counts["M1"],
            counts["conflict"], counts["nested"]))
    shared = totals["shared"]
    print("# %d target(s), %s task(s); M1 coverage %s of %d shared occurrence(s)"
          ", %d nested region(s)" % (
              len(targets), sum(map(len, targets.values())),
              "%.0f%%" % (100.0 * (totals["identical"] + totals["M1"]) / shared)
              if shared else "n/a", shared, totals["nested"]))


if __name__ == "__main__":
    main()

---
name: workload-assertions-may-be-adjusted
description: "Owner permission (2026-09-13): workload unit tests (/opt/hadoop-* TestCausynth*) may get SMALL edits when their assertions block a replay path (e.g. a flipped fault path aborting before the fatal read)"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 3230912f-3427-4c18-a306-eb2005a43b37
  modified: 2026-09-13T19:38:53.173Z
---

The owner: "我知道作为workload的unit test有些assertion可能阻碍了，如果有这种情况你可以对unit test做小的修改" (2026-09-13, during the 17960 healthy-recording / bug3 flip work).

**Why:** the experiments' workloads are JUnit tests adapted from upstream Hadoop tests. Their assertions/`Assert.fail`/`waitFor` were written for one outcome; a concolic flip replay (fault=true, config=false, clock skew) legitimately takes another path and must still reach the fatal read site. An assertion that aborts the test before that site hides the mechanism, not a bug.

**How to apply:** when a replay path is cut short by a workload assertion, make the SMALLEST edit that lets the path reach the fatal read (relax/remove the assertion, make a helper return a boolean instead of failing, skip a waitFor on failure) and record the diff under $SP_NEW (never git checkout/stash/reset/commit in /opt/hadoop-*). Do not change production code to dodge an assertion; do not weaken the fatal condition itself. Related: [[graphchecker-core-design-principle]], [[graphchecker-refactor-goal]].

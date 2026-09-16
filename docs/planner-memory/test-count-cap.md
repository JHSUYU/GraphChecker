---
name: test-count-cap
description: "Owner ruling 2026-09-14: the test suite must stay at a few dozen tests, never more than 100 (@Test methods); every new behaviour folds into an existing test or replaces one"
metadata:
  type: feedback
---

Owner (2026-09-14, on seeing 405 test runs / 286 @Test methods / 67 classes): "测试太多了，测试要始终维持在几十个，不许超过100个".

**Why:** the suite had grown with one pinning test per fix (regression pins for mechanisms since deleted, near-duplicate cases per row shape); the owner wants a small suite that states the design's rules, not a history of patches.

**How to apply:**
- Hard cap: ≤ 100 `@Test` methods in src/test; target 60–80. Count with `grep -rc "@Test" src/test | awk -F: '{s+=$2} END {print s}'`.
- Every subagent mandate: "no net new @Test methods" — a new behaviour becomes an assertion inside the existing test for that rule, or replaces the test it supersedes; table-driven cases over one method for shapes that differ only in data.
- Delete tests that pin deleted mechanisms, duplicate a rule, or test a row's spelling rather than a rule.
- Report before/after counts in every test-touching report. Related: [[subagent-rules-of-engagement]], [[graphchecker-refactor-goal]].

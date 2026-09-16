---
name: fix-the-flow-not-the-bug
description: Owner rule (2026-09-15, repeated and strengthened): every fix is planned against the whole pipeline in advance; the planner enumerates downstream effects and sibling instances before dispatching, so one round fixes the class, not the symptom
metadata:
  type: feedback
---

Owner (2026-09-15 morning): "你每次修bug。不要局限于这个bug本身，而要考虑未来可能的连锁影响，这个bug修复是否能让整个流程没问题。这样就不会不停出现bug". Repeated that evening after the identity work took four rounds (G2→G5): "每次修bug。你要提前考虑可能的影响，你作为规划者，要思考整个流程的。不能只聚焦于一个bug本身。你要提前考虑清楚争取一次就解决大部分问题。这要设为你的长期记忆".

**Why:** each round that fixes one symptom costs a recording + gate cycle (1–2 h) and a subagent's context; the owner measures progress in cases passing, not in bugs closed. The identity rounds were the example: G2 unified the address function but not its inputs, so G3 (producer endpoint), G4 (frame sets, site index) and G5 (double-pushed frames) each surfaced the next input that differed between the recording and the replay.

**How to apply (planner, BEFORE dispatching any fix):**
1. Write the defect as a class, not an instance: which notion is wrong (identity input, row contract, closure rule, artifact shape), and every place that notion is computed or consumed (both passes, PLAN/IMPORT/EXPLORE/COMPOSE, run_engine, configs, tests).
2. Enumerate the inputs of the function being fixed and, for each, where it comes from in every pass/stage; any input present in only one of them is part of the same fix.
3. Trace the fix forward through rows → gate → explore → compose → claim and state the expected numbers at each stage (the gate letters of the mandate come from this trace).
4. Check the in-flight mandates for overlap or contradiction (a fix in one branch that another branch deletes or re-routes) and resolve it in the mandates, not at merge time.
5. Put the invariant into the IMPORT gate or a test so the class cannot come back silently.
6. Only then dispatch, with the whole class in one mandate and one gate. If a second symptom appears after the round, stop and redo step 1 — do not patch the symptom.

Related: [[planner-judge-against-reference-design]], [[identity-v3-execution-index]] (the identity input checklist), [[subagent-rules-of-engagement]].

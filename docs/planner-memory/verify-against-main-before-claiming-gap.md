---
name: verify-against-main-before-claiming-gap
description: Never call a GraphChecker mechanism "missing/by design" without first checking original main (3d9355745) and the /opt/hadoop workload hooks; the user built these and knows they exist
metadata:
  type: feedback
---

When a chain looks broken (e.g. wire value unbound, boundary families 0, roots not connected), first diff the path against original main `3d9355745` and grep the workload hooks under `/opt/hadoop-hdfs-*/` before saying anything about design. Concrete instance (2026-09-12): I said cross-RPC attach was a "Java-side seam / shadows can't cross processes"; wrong — the cluster runs in ONE JVM and the propagation header already carries an expression identifier that the receiver attaches (`CausynthMessagePropagation` → `CausynthTraceRecorder.registerSource/beginSourceRequest`). User: "我们的这个attach确实是都实现了的。你怎么能把这个都弄没呢".

**Why:** the user is the designer; these mechanisms were working on main. A "0 realized" count after a refactor is a regression to locate, not a design gap to explain.

**How to apply:** treat every such symptom as a regression first: dispatch a code diff main→branch along the path plus an artifact check of the main baseline; only after both come back empty discuss design. Related: [[graphchecker-refactor-goal]], [[graphchecker-external-callers]].

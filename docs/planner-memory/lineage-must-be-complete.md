---
name: lineage-must-be-complete
description: Owner ruling 2026-09-15 — lineage IS tracing (OpenTelemetry-style context propagation); it must be COMPLETE on the six cases, not measured-and-degraded. Fix every scope loss by adding Soot instrumentation or editing HDFS source; system-specific support is allowed.
metadata:
  type: feedback
---

Owner: "这个lineage其实就是tracing。我允许你改动hdfs的source code,包括soot插桩。如果哪里有遗漏我们要不补充soot instrumentation要不我们就改改hdfs代码。其余都类似标准opentelemetry，所以lineage这里肯定是完备的。我们允许针对特定系统做一些支持."

**Why:** the identity (causal anchor + execution index) is only as good as the context propagation; a Lost context is a hole in the graph, and OpenTelemetry shows every async boundary (thread pools, executors, RPC handler queues, Netty event loops, timers, SASL/handshake lifetimes) can be carried.
**How to apply:** the gate for the runtime milestone is 0 Lost activations and 0 unpaired attaches on all six recordings, per entry point; each remaining loss gets a Soot hook or an HDFS source edit (kept as a diff per tree under d-runtime/workload/); Lost/degraded stays only as a safety net for unknown code. Extends [[hadoop-tracing-edits-allowed]]; see [[identity-v3-execution-index]].

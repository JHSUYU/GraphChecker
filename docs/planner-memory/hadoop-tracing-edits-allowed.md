---
name: hadoop-tracing-edits-allowed
description: Owner permission 2026-09-14 — small edits to Hadoop SOURCE (not just tests) are allowed for tracing/scope propagation (Server.Call carry, SASL scope lifetime, daemon-tick roots); keep them as diffs under d-runtime/workload/; build rules and the no-git rule in /opt/hadoop-* still apply.
metadata:
  type: feedback
---

Owner: "tracing啥的我都允许你小改hadoop代码". Small, tracing-only edits to the Hadoop source trees (/opt/hadoop-hdfs-*) are permitted: request-scope carry across the IPC Server.Call queue, SASL inbound scope lifetime = DataXceiver op, daemon-tick roots, hook points the lineage needs.

**Why:** lineage completeness (the identity the whole design rests on) is lost in Hadoop's thread pools and handshake code; instrumentation alone cannot recover it.
**How to apply:** each edit is a diff file under $SP_NEW/d-runtime/workload/ (one per tree), semantics-preserving, no behaviour change beyond scope bookkeeping; rebuild per the runbook (Java 8, never install, never while a lane runs on that tree); never git checkout/stash/reset/commit/clean in /opt/hadoop-*; do not touch the foreign TestPureJavaCrc32C edit. Extends [[workload-assertions-may-be-adjusted]]; see [[graphchecker-verification-runbook]].

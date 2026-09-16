---
name: graphchecker-external-callers
description: The 21 GraphChecker APIs called from outside this repo (the eight /opt/hadoop-hdfs-* workload trees and /opt/solr); a repo grep cannot see them, so check this table before deleting any public member of runtime/ or annotation/
metadata:
  type: project
---

The workload checkouts and Solr call GraphChecker **by name**, compiled
against an older jar in `~/.m2`. A `git grep` of /opt/GraphChecker therefore
returns empty for every one of these, and the reference resolves only when a
campaign puts the new jar on the classpath — at SEED, as `NoSuchMethodError`.

**Before deleting or changing the signature of ANY public member of
`runtime/` or `annotation/`, check this table.** Refresh it with:
`for t in /opt/hadoop-hdfs-* /opt/solr; do grep -rl edu.uva.liftlab.graphchecker "$t" --include='*.java'; done`
and also `grep -h 'Causynth\|Debug\.' $SP_NEW/d-runtime/workload/*.diff`.

## The table (verified 2026-09-14 against tip `1d02b20a3`, REPORT-MECHANISMS §10)

`ConcolicRegionRuntime`
- `symbolizeConfiguredSourceField(String,Object,String)→boolean` ← `ipc.CausynthSymbolicSource.symbolize:31`. **Every case's configured symbolic roots.** 7 trees (all but 17899-base).
- `materializeSymbolicBoolean(String)→boolean` ← `annotation.Debug.makeSymbolicBoolean` ← `ipc.Client:1247`. bug1/bug2/bug3.
- `pauseObservation()→void`, `resumeObservation()→void` ← Solr `CausynthHttpPropagation$RuntimeApi:237-238`, **reflective**.

`CausynthTraceRecorder` (all ← `ipc.CausynthMessagePropagation`, except where noted)
- `captureScope()→Object`; `endInboundExchange(long)→void`; `registerSourceAlias(Object,Object)→void`
- `outboundExchange(String,String,String,String,Object)→String` — **Solr only** (`RuntimeApi:225`, reflective)
- `outboundExchange(String,String,String,String,Object,Object)→String` — the 8 trees
- `inboundExchange(String,String,String,String,String,Object)→long`
- `registerSource(Object,String,String,String,long)→void`
- `beginSourceRequest(Object,String)→long`; `endSourceRequest(long,String)→void`
- `startRecording()→void` — 7 trees (not 17899-base)
- `restartSource(Object,String,String,String,long)→void` — **17960 and 17960-jdk8 only**
- `captureAsync(Object)→void` — **17899-bug1 only**

`SymbolicMessageEnvelope`
- `takeOutbound()→String`; `installInbound(String)→void`; `clearInbound()→void` — the 8 trees and Solr.

`annotation`
- `Debug.makeSymbolicBoolean(String)→boolean` ← `ipc.Client:1247` (bug1/bug2/bug3)
- `CausynthExceptionTarget` (type) ← `BlockTokenSecretManager:21` / `FSImageFormatPBSnapshot:38`. Solr keeps its own forked copy under `solrj/src/java/edu/uva/...` and does not read ours.

Nothing else in any tree names `edu.uva.liftlab.graphchecker`. The recorded
workload diffs add no API beyond this table.

## Three traps this table exists to name
1. **Two APIs are single-tree** (`captureAsync`, `restartSource`): grepping one tree is not the check.
2. **Four are bound reflectively by Solr and fail SOFT** — `RuntimeApi.load` catches `ReflectiveOperationException | LinkageError` and returns null, so deleting one silently disables Solr propagation instead of crashing. A green campaign is not evidence.
3. **"Woven by nothing" is not "called by nothing."** `ConcolicHookAbiTest` covers only woven hooks; these are called, not woven.
4. **A helper left with zero callers by your own deletion is a signal to re-check, not to delete deeper.** Deleting `symbolizeConfiguredSourceField` stranded seven helpers. "These are dead now, take them too" would have been a second, larger deletion built on the first one's error. A helper that served exactly one caller is evidence the caller was load-bearing. Stop, list the stranded helpers, re-derive the deletion's premise from OUTSIDE the repo.

5. **Grep the string, not only the symbol.** GS §A repeated the loss in a new shape: `CALL_ARGUMENT` recording looked consumer-less because its three real consumers match the row's `kind` STRING through a different constant (`CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT`, value `"CALL_ARGUMENT"`) in another file. Before deleting a mechanism, grep BOTH the identifier AND every string literal it is spelled with, including literals other constants are defined as.

## Incidents
- **2026-09-12** — an audit flagged `symbolizeConfiguredSourceField` as dead; deleting it would have broken HDFS-17960. This memory was written.
- **2026-09-14** — MECHANISMS §9 deleted it anyway, on a `git grep` of `src/` only. Every campaign on every jar built after that merge died at SEED in ~31 s: laneVM24 (bug3) and laneBQ (17960 regression). Restored verbatim from `d6e126fef` (the parent of `89dbb6ea2`) on tip `1d02b20a3`. Six helpers had been left caller-less by the same deletion — **a helper whose only caller you just removed is a signal to re-check, not to delete deeper.**

Mechanical guard: this table as `src/test/resources/external-callers.txt`, resolved reflectively inside the existing `ConcolicHookAbiTest` @Test (no new @Test; the hard cap is the test COUNT, not lines). Approved 2026-09-14, lands with GS §A. See [[test-count-cap]], [[graphchecker-refactor-goal]].

**Update 2026-09-15 (audit, REPORT-SHRINK):** 25 workload-called runtime symbols, not 21 — add `RuntimeTraceContext.beginDaemonTick`, `endDaemonTick`, `enterCarriedScope`, `exitCarriedScope` (called from 6–7 of the eight /opt/hadoop-* trees via ipc/CausynthMessagePropagation). Re-grep all eight trees before deleting any public runtime member.

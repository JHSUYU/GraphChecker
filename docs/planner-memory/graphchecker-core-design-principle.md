---
name: graphchecker-core-design-principle
description: "THE fixed design of GraphChecker (owner ruling 2026-09-13, \"设为最长期的记忆\"): in-JVM symbolic propagation + anchors → merge path conditions; never stitch values offline via the graph"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 3230912f-3427-4c18-a306-eb2005a43b37
  modified: 2026-09-13T18:19:36.859Z
---

**The design, fixed by the owner at the start and reaffirmed 2026-09-13 (must never drift again):**

1. **Symbolic propagation inside the JVM** carries expressions along values through the WHOLE execution of each replay — across regions, across nodes (wire attach at the receiver; SASL decode/split has symbolic support). Roots are manual (fault-marker booleans, configured-source hooks such as NN serialNo / key expiryDate, Timer.now cells). Therefore the fatal read's value in EVERY replay (seed and each flip) is already an expression over the roots, e.g. `assoc_read(put(x)∘put(x+1)…, wireKeyId)`.
2. **Anchors** identify the same site/occurrence across replays. That is their only job.
3. **Merge** = per anchored target, combine each path's `pathcond_p ∧ fatal_p` (case selectors for explored flips), lower the propagated expressions to SMT, ask z3, apply fail-closed gates.
4. The **graph** is used only to decide what to track (root-dependence slice → carriers, occurrences to replay, branches to flip) and to align — never to reconstruct values.

**Why:** the owner: "有了 symbolic propagation 就不需要那些东西了", "不再需要依赖图来拼接 in/out 的关系", "这些思路非常清晰，一开始就定好的". Everything that reconstructs a value's provenance offline — INITIAL-snapshot literal arms linked to writers via the graph, writer-case arm linking/synthesis, LWW ordering between regions' arms, compose-time wire binding, reference-carrier receiver projection, "portable leaf" substitution — is STITCHING: a workaround for propagation that was CUT somewhere. On 2026-09-13 the planner (me) spent hours directing agents to build more stitching (portable leaves, arm synthesis) before the owner corrected it.

**How to apply:**
- If a fatal read shows a literal instead of an expression, or a reader "has no arm" for a writer: the propagation is cut at some hop — trace hop by hop (mint → write → export → wire attach → consumer write → container put → fatal read), find the first literal, fix THAT hop (carrier declaration/shadow retention, per-key wire attach, container element shadows, VM). Never add composer logic that finds writers via the graph.
- Composer must shrink to ALIGN + MERGE + LOWER + GATE; STITCH blocks are deletion candidates (inventory: $SP_NEW/composer-inventory/REPORT.md).
- Heuristics not derivable from this design are deleted, not kept ("明显不合理的东西删掉，不要再用了"). See [[graphchecker-refactor-goal]] for the progress log and [[serial-campaigns-only]] for lane rules.

**Addendum 2026-09-13 19:20 (owner):** shadow retention is BY VALUE, not by declared carrier location. Any symbolic write keeps its expression under the real object identity; reads return it. The "carrier identification" layer (declared carriers, receiver locators, access/entry anchors, map identity disambiguation, MISSING_METADATA) is not part of the design and is deleted once the VM retains shadows by value. The static slice scopes instrumentation and flips only.

**Addendum 2026-09-13 22:20 (from HDFS-17960 evidence):** a fatal predicate φ may be legitimately CONCRETE when the root reaches the target only through control dependence (a store skipped on one arm). The design covers it via the flip replay: π_flip carries ¬root, the target is reached with a concrete φ, and ⋁(π∧φ) is SAT → MARKER_FLIPPED. Never treat "φ is a literal" alone as PROPAGATION_CUT; the cut is "φ literal AND π has no root decision AND the slice says the target depends on the root". The in-VM "guarded version" (a store under a path guard tracked as guard ? v : v0) is an optimization that would expose such dependence from the seed alone — parked, not required.

**Addendum 2026-09-14 01:40 (composition rules settled on bug3 evidence):**
- Root domains are exactly what the case declares: a fault marker is free in {recorded, flipped}; a configured root within its declared domain; a clock read (a cell minted through the clock hook) within the declared skew window around the SEED's reading; every other root with a recorded value is pinned to it; a handoff variable v_H has no domain of its own (its family constrains it).
- A path π_p carries its own replay's valuation of every VARIED root (not of clock reads — their decisions are already in π); a family arm is guarded by the delivering replay's prefix (decisions with clock < exportEventId) ∧ that replay's valuation of every varied root ∧ v_H = e_p.
- Nothing in the formula may be free that the recording states: key membership in a container base comes from the VM's INITIAL snapshot; an unstated membership is a gate, never a free Boolean.
- φ_p asserts the FATAL arm (predicate == requiredTakenOutcome); the target disjunction is over selectors, not copies.

**Addendum 2026-09-15 09:20 (owner: "这里的设计很臃肿，包括容器符号，你要好好给出一个精简的设计"):** the one-page reference is `/opt/graphchecker-handover/d3-handover/d-design/LEAN-DESIGN.md` (to move into docs/ at cleanup). Symbols come from exactly three declared places — roots, declared region inputs (placeholder reads), wire attaches; everything else is concrete until a symbolic value is written into it (by value). No carrier layer, no region-entry container modelling, no WINDOW_START. Any decision with a symbolic term is a flip target. The IMPORT gate enforces the row contract. Everything the page does not name is a deletion.

**Addendum 2026-09-15 09:55 (owner, containers as v_C):** a container that crosses occurrences is a STATE handoff variable v_C, like v_H: the reader's entry state is v_C, its family arms are the writer endpoint's paths under their π (recorded by brute-force flipping any symbolic branch upstream), and the offline merge substitutes v_C := e_q under π_q. WHEN v_C exists is the whole difference between lean and bloated: NOT at region entry by a static carrier list (deleted, P2n), but from the FIRST SYMBOLIC WRITE to the location — a write of a symbolic value (v_H/root/placeholder) OR a concrete write executed under a non-empty path condition (control-dependent on a symbol). From then on every op is a version (WriteRow with the writer's occurrence, expression and π); readers join by version; across sessions the same writer endpoint's paths are the arms (R-I4); earlier local ops stay concrete. Implementation: VM22 — a guarded concrete store starts the location's log (the VM already carries `path_guard` on stores); runtime/composer/explorer unchanged in principle. Measure the volume on 17960 first.

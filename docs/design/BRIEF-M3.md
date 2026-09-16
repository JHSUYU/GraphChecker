# BRIEF M3 — EXPLORE (Design 3 refactor)

Prerequisite: M1 merged; read CONTRACT-SCHEMA.md, REPORT-M1.md, REFACTOR-D3.md,
DESIGN3-PLAN.md, INTERACTION-ID.md, then REPORT-PRODUCIBLE.md (+ HANDOVER-E1.txt: nested
v_H closure, the 120005 cause), REPORT-DEPTH.md (nested guard chains deepen wave by
wave), REPORT-ROOTENUM.md (domains), REPORT-17897-WITNESS.md.

Scope (concolic/ explore side: ConcolicPathFlipPlanner/Solver, RegionPathWorklist,
BranchReplayContract, HandoffFamilyRows → generalised to interactions; not the
composer):
1. Tasks = focused occurrences (or state-connected factors) from the anchor's closure
   (ancestors ∪ producers of every interaction on admitted paths ∪ writers of every
   version read). No companions; no linked-slice admission.
2. Obligation = the path as its replay ran it (prefix) ∧ one flipped decision; every
   handoff control v_H(I) bound by family(I) closed over nested v_H to a fixed point
   (arms from the corpus keyed by INTERACTION, producer paths' π and e_q; declared roots
   free inside domains, Boolean markers over both values, clocks unbounded, roots without
   a domain pinned); no arm ⇒ free + `UNPRODUCIBLE_ANSWER` row. Answers applied at the
   attach in the replay (as today).
3. Per-region admission: a task's replay is admitted on its own focused region's prefix
   only; producer regions' divergences are their own tasks' business.
4. Fixed point per region; waves = union of frontiers; parallel workers; obligation
   records per M1 rows.
5. Delete: companion planning, slice-based admission, linked replay plumbing superseded.
Tests folded (≤ 80). Gate (offline on the M2 recordings of 17897 and bug3): the target
region reaches the fatal arm with producible answers; the NN rotation tick is a task of
its own; obligation rows name every unproducible control. Report REPORT-M3.md.

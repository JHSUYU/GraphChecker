# CLOSURE V2 — target slice, recursive closure, symbolic frontier (owner-approved 2026-09-15 12:05)

Replaces: E3's "root-dependent occurrences are tasks" and E7's "any symbolic decision in G_S^W is a flip candidate". Keeps: rows as the pairing authority, families, E8 (replacement is a WIRE rule), E10 (a recorded arm is not re-flipped), the IMPORT gate.

## 1. Target slice (demand)
Demand starts at the annotated target: the operands of the fatal predicate and the control guards of the target site — not the whole region.
- Data dependence: read off the VM's expression for the operands (propagated): its leaves are boundary variables (attach v_H, read-from versions v_R) and roots. No static data slice is needed at runtime; the static slice's only jobs stay: which regions are instrumented, which write sites of a declared cell are observed.
- Control dependence: PLAN computes, per target site, the guard set = the branch sites the target site is control-dependent on (post-dominance in the region's CFG). π_p stays the recorded prefix of the occurrence (sound); the guard set is what EXPLORE flips.

## 2. Recursive closure (the causal graph)
For every boundary input of a demanded value:
- attach v_H → the producer endpoint that paired in this session (rows) ∪ every STATIC export site feeding that port in the retained set (unexecuted producers enter the graph before any flip);
- read v_R of location L → the writer occurrence that produced the observed version (rows) ∪ every occurrence of a region containing a STATIC write site of L in the retained set (the seed-overwritten Region3, 17960's deletion region);
then apply §1 to each producer's export value / writer's written value; fixed point; recomputed per wave over all sessions. Static candidates come from PLAN's slice artifacts (write sites per demanded location, export sites per port); dynamic pairing from rows. A candidate occurrence that never ran in any session is a task candidate (its region is instrumented); one that is not instrumented is INTERACTION-ID §8 case 2 (retained set must grow).

## 3. Symbolic frontier and flips
Three symbol classes: authorized roots (MARKER / INTEGRAL with domain / CLOCK ≥ 0) — free within their domain; boundary variables (v_H, v_R, placeholder S) — never free, explained only by a family arm, a joined version or a pin; propagated expressions — not variables. A container read variable is the writer's whole PUT/REMOVE/INITIAL chain (v_C); freedom comes only from the authorized roots at the end of the chain; a chain with none is pinned / UNPRODUCIBLE_ANSWER.
Flip candidates = symbolic decisions of occurrences INSIDE the closure (the target's guards and the closure members' guards of their exports/writes). The flip query binds boundary variables through families; a model on an unbound symbol is UNPRODUCIBLE_ANSWER (final gate). E10: an arm some session already recorded for that occurrence is not re-flipped.

## 4. Where it lands
- PLAN: guard set per target site; write sites per demanded location and export sites per port already exist for declared cells — generalise to the locations/ports the target slice names (the demand is dynamic, so PLAN publishes the static maps and EXPLORE joins).
- EXPLORE: ClosurePlanner uses rows ∪ static candidates; candidate selection restricted to the closure; task `why` = CLOSURE_MEMBER | STATIC_CANDIDATE_WRITER | STATIC_CANDIDATE_PRODUCER.
- COMPOSE unchanged. IMPORT gate unchanged. Expected effect on 17960: identical result with 3 obligations; on 11741: the NN rotation-2 scan and the DN refresh scan both enter the closure through the MAP location L (static write sites) and the block-key port, so the two-flip chain is reachable in two waves.

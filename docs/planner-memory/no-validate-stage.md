---
name: no-validate-stage
description: Owner ruling 2026-09-14 — no VALIDATE / materializing replay stage; the deliverable is the composed .smt (+ z3 verdict, polarity, domains). Do not add a confirmation replay.
metadata:
  type: feedback
---

Owner: "不需要validate，拼出来.smt即可" — the pipeline ends at COMPOSE → SOLVE → DECIDE → EMIT. A finding is the composed .smt2 per anchor plus z3's verdict under the declared root domains, with polarity (recorded valuation unsat) and the finding kind; NO end-to-end materializing replay is run to confirm it.

**Why:** the .smt is the oracle of the design (experiments' smt2 + Z3 verdict); a confirmation replay in a nondeterministic distributed system adds cost and incompleteness without changing what the formula states.
**How to apply:** drop "solve → materialize → validate" from DESIGN3/REFACTOR plans (M2 has no VALIDATE replay mode; M4 has no VALIDATE gate; Verdict = the claim from DECIDE). See [[graphchecker-core-design-principle]], [[graphchecker-refactor-goal]].

**Reaffirmed 2026-09-15 (owner):** "我们不做任何的validation。目前只要拼出来符合因果链的.smt即可". Consequences: no stage re-runs a witness; a focused replay exists only to COLLECT ROWS (arms) the seed lacks, never to confirm a flip or a bug; the per-case deliverable is candidate.smt2 + z3 verdict + claim, with every symbol bound by a family or a pin (causally closed), and refusals named. The contract verdict `VALIDATED` (FocusedReplay) is a misnomer for "prefix reproduced, rows collected" — rename to ADMITTED at the next contract touch; never build anything on the word.

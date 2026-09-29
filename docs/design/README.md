# docs/design — the reference designs

The top-level `README.md` is the design, the status and the handover; these files are the
reference designs it derives from, kept verbatim because the code cites them by section.
Where the README and one of them disagree, the rows decide.

| file | what it is | cited by |
| --- | --- | --- |
| `DESIGN4-FAULTS-INPUTS-ITERATION.md` | the current design (2026-09-23): fault points at the transport doors, symbolic inputs, the growth loop, CONFIRM, the nearest-world rule (§3.7) | `plan`, `explore`, `compose`, `runtime` |
| `LEAN-DESIGN.md` | the fixed one-page design frame (declared roots, in-JVM propagation, one flip per replay, edges joined in the SMT, fail closed) | DESIGN4, README §2 |
| `IDENTITY-V3.md`, `IDENTITY-IMPL.md`, `IDENTITY-V2.md` | the occurrence identity: causal context, hierarchical execution index, endpoints, the scope-base rule | `runtime/Identity`, `Lineage`, `RowPublication` |
| `INTERACTION-ID.md` | one interaction, two endpoints (the pairing of an attach with its producer) | `runtime`, `smt/Arms` |
| `CLOSURE-V2.md` | the target slice, the recursive closure, the symbolic frontier | `explore/ClosurePlanner`, `causynth` |
| `CONTRACT-SPEC.md` | the row and gap contract (its package names predate the current tree; the row semantics stand) | `contract`, `RowInvariants` |

Paths inside these files may refer to a decommissioned host; read them as descriptions of what
an artifact was. The schedule/attribution design (deterministic prefix, rest clock, the
three-rule resolver) and the case-preparation rules are recorded in the README §6 and in
`experiments/lib/README.md`.

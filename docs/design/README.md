# docs/design — the reference design

These documents are the REFERENCE DESIGN the top-level `README.md` derives
from: the fixed design statement (`LEAN-DESIGN.md`), the scoping walk
(`CLOSURE-V2.md`), the occurrence-identity specs (`IDENTITY-V2.md`,
`IDENTITY-V3.md`, `IDENTITY-IMPL.md`, `INTERACTION-ID.md`), the row/gap
contract (`CONTRACT-SPEC.md`), the refactor plans (`DESIGN3-PLAN.md`,
`REFACTOR-D3.md`), the 2026-09-15 stop snapshot (`HANDOVER-D3.md`) and the
per-mandate `REPORT-*.md` / `BRIEF-*.md` measurements that produced the
present engine. They are kept verbatim, as written, because the README
summarizes them and a disagreement between the two should be settled in
favour of whichever the rows support — but the design frame itself
(`LEAN-DESIGN.md`, `graphchecker-core-design-principle.md` under
`docs/planner-memory/`) is FIXED and is not up for rediscovery.

**Paths inside these files may refer to a decommissioned host.** They were
written on the build machine this project ran on, and they name scratch
directories, corpora, worktrees and `/opt/hadoop-*` workload trees that no
longer exist. Read a path as a description of what the artifact WAS, not as
something you can open; the reproducible parts are `experiments/hadoop/`,
`tools/gate3/` and the case `tree-edits/` directories in this repository.
Dates, shas, row counts and measurements in them remain meaningful.

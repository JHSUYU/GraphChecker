# H5 (engine analyst, offline): second session, 2026-10-19 23:50 to 2026-10-20 10:40

No live case runs; debug runs NE1/2/3-22 (`/bigtemp/vnr3ne/gc-out/hbase-reask`) are evidence. Offline material:
`/bigtemp/vnr3ne/analysis/hbase-2026-10-20/reask/` (confirm/, sim-aa/, probe-mat/, probe-nz6/, compose/nc7-co/, worlds/).

## Commits (GraphChecker `hbase-reask`, all merged and gated)
- 8cb3cdfeb (TODO HBase 4): an enum compare over reads that do not move is its writer's name; an untaken fatal over an unmodeled
  operation is held to its recorded movers (15: 458 -> 245 free leaves, the seed no longer FORMULA_SAT).
- 0284392d4: TODO HBase 7 measured (the ~240 refusals cost 459 s of solver time; no PLAN change).
- 4a06f9d88: a hand-off serves only work another thread started (a step's own inline continuations no longer mark it serving).
- 4f80eb7f3 + a4b7879e9: a claimed hand-off held where it runs is held at its claim's entry, before its locks; it falls back to the
  old hold point when the earlier end is inside the claim or the claim's prefix holds another order's earlier end (cycles).
- ddcbbb8ec: DUPLICATE_WORLD (a replay planting exactly an already-run or queued world is settled by it; 10: 466 -> 188 replays).
- 86cdb2603: CONFIRM does not require a STATE row whose reader the plan holds behind the anchor (22's real claims confirm).
- c27f51a03: a file another host replaced is read again from a fresh open on ESTALE (NR10-11's planner death was our own rewrite).
- docs: 0d4d460b3 / af9343249 (TODO HBase 15 with the parked JOIN design), the TODO 13/14 items.

## Findings worth keeping
- 22's NC11 claims were the real HBASE-30483 shape; CONFIRM's STATE check falsely refuted three that observed the fatal.
- #11 NZ2: the fake claims came from the INITIAL pairing AND 301 hand-off arms carrying other sessions' wall-clock constants; a
  CLOCK_SKEW claim needs master0's whole clock chain shifted (T0 >= T1 + 1). The owner's direct workaround superseded this.
- 15's remaining 197 `unsupported__` leaves sit in path conditions only; both claims rest on one after a re-paired procedure-state read.

## Parked / open
TODO HBase 13 (a continuation's registration as its submitter), 15 (JOIN rows: the sound client happens-before, 2-3 days, would
close 08/14/15 and shorten nsrg/07's claim loops), the 245/197 pi leaves on 15 (a model gap), claim-entry holds where the earlier end
was caused by the prefix.

# WIP: FIX1 — the live 17960 run the new IMPORT gate refused

Base commit: `39bedd768` (staging, round 3 after PC3).
Contents: 3 commits (`0001`..`0003`) + `uncommitted.patch` (2 files) + `status.txt`.
This was never a branch on the remote.

**Status in main.** All three commits are MERGED (`Merge r3/FIX1 @9e50a1ee2`)
— mandate items 1, 2 and 3. `uncommitted.patch` is NOT applied — it was
mid-edit when round 3 stopped, and it holds the attempt at item 4. Apply it
with `git apply uncommitted.patch`.

## Why it exists

The last LIVE HDFS-17960 campaign was refused by the per-wave IMPORT gate that
round 3 introduced. FIX1 is the repair of that gate and of the two rules the
refusal exposed. Three parts landed as commits; the fourth is open.

## The mandate

1. `campaign_import_wave_gate` in `run_engine.sh` links the **whole epoch
   roster** (the seed plus every session published so far), not only the
   sessions the wave added.
2. `RowInvariants.decisions` judges `outcome` at the valuation the session
   **RAN under**: SEED → `recordedValue`; FOCUSED → the wave's
   `rootAssignments`.
3. A focused session whose flip prefix did not match, or whose focused root
   never minted, is `NOT_ADMITTED` — a fail-closed verdict.
4. **OPEN.** Why session `793875fb482a10a4-4b39d011`'s prefix stopped matching
   on `39bedd768` when pass #8's matched. Compare the `decisions` and
   `obligation` rows of the two corpora. Suspects named by the planner: the
   `seq=0` rule; PC3's `replayOccurrence` / `primitiveValue`; R1's mint split.

## What the three commits did

* `0001` **The wave's import gate reads the epoch's whole session set.**
  Invariant 1 ("exactly one session of the set states role SEED") is a
  SET-level rule, and the gate handed it `comm -13 sessions-before.txt
  <roster>` — only the sessions that wave added, which by construction never
  include the seed. Every wave gate of every case therefore had no SEED to
  find. WHETHER the gate runs stays the wave's question
  (`campaign_wave_sessions`, `count -eq 0` early return unchanged); WHAT it
  reads is now the epoch (`campaign_session_roster` links every session under
  `sessions/`).
* `0002` **A term is judged at the valuation its session RAN under.**
  `recordedValue` is what the mint OBSERVED. On a focused replay the wave's
  assignment is planted at the mint *after* the observation is read, so every
  rule that reads `recordedValue` as "the values this session executed at" is
  unsound on a focused session (invariants 6 and 9 both were).
  `RowInvariants.executed` is the one notion of what a session ran: SEED →
  `recordedValue`; FOCUSED/MARKER/INTEGRAL → the wave's `rootAssignments`;
  FOCUSED/CLOCK → the mint's own reading plus `clockDeltas`; a root the wave
  assigned nothing → the mint read it. The ask is the FOCUS ROW; a FOCUSED
  session with no focus row this epoch is a named BLOCKING refusal
  (`epoch/valuation`), never a fall back to `recordedValue`.
  Offline, the refused run went 19 violations / 3 blocking → 16 / 0; pass #8
  stayed 19 / 2 with byte-identical gap files.
* `0003` **A verdict is fail-closed on the rows its session carries.**
  ADMITTED is a claim about the SESSION — the rows EXPLORE and COMPOSE read —
  and `FocusedReplay.results` decided it from `FLIPPED` alone, which is process
  state that outlives the rows. The rule now only ever REFUSES an admission,
  on two stated conditions: a prefix this replay was ABANDONED on (the
  `REPLAY_PREFIX_UNMATCHED` gap is the verdict's reason), and a root the wave
  assigns whose MINT ROW the session does not state (`mintPublished`, filed
  where the row is published — told apart from `planted` on purpose).

## What the uncommitted diff holds (item 4, in progress)

`FocusedReplay.complete` asked "has the prefix been taken" occurrence-blind,
so it returned false at the terminal of any focused occurrence while any
obligation was unflipped — including the MINT of an assigned root, which
usually finishes *before* the flip has run. `judgeFinishedOccurrence` then
abandoned the mint, and every row that occurrence published went with it.
17960 obligation `793875fb482a10a4` flips at
`applyEditLogOp@8/deleteSnapshot` (`focusedOccurrenceId ea10d7e883e23973`)
while its `rootMints` name `applyEditLogOp@7/deleteSnapshot`
(`4786cb8a1d2bd655`) — a different occurrence. 42 decision rows and the
session's only root mint row were lost that way, leaving the 0-byte
`roots.jsonl`. The sibling obligation `cb67875d1d896d4d`, whose flip and mint
are the same occurrence, kept everything in the same wave.

The fix in `uncommitted.patch` takes the same join `observe` takes, on the
terminal side: a decision is credited to the obligation whose
`focusedOccurrenceId` it happened at, so only that occurrence is asked the
flip's question. The test additions in
`ManualMintStatesItsValueTest` state the four cases (mint is focused but asked
nothing; the flip's own occurrence is incomplete until it takes it, then
complete; an occurrence outside the focused set is asked nothing).

**Not yet done:** this is a hypothesis with a test, not a measured repair.
It has not been run against the refused corpus, and the planner's open
question (why pass #8 matched and `39bedd768` did not) is answered by it only
if the corpora differ in exactly this way — check the `decisions` and
`obligation` rows before believing it.

## Definition of done

Apply, finish item 4, then re-run the 17960 acceptance campaign live
(`experiments/hadoop/accept`) and show wave 0 admitted.

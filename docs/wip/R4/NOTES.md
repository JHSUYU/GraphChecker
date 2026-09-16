# WIP: R4 — a root symbol without its RootMintRow

Base commit: `0e3c1ab39` (staging, round 3 after C3).
Contents: 1 commit (`0001`) + `uncommitted.patch` (4 files) + `status.txt`.
This was never a branch on the remote.

**Status in main.** The one commit is MERGED (`Merge r3/R4 @a7c53797c`); it is
a measurement and changes no code. `uncommitted.patch` is NOT applied — it was
mid-edit when round 3 stopped. Apply it with `git apply uncommitted.patch`.

## Why it exists

HDFS-11741's composition is satisfiable at every valuation including the
recorded one, so it yields no witness. The reason is that two focused sessions
carry the key-serial root's SYMBOL without its MINT ROW, and nothing refuses
that anywhere in the pipeline.

## The mandate

A root symbol without its `RootMintRow` (11741 campaign #4 sessions
`e635d55d82ff32da` / `ed4ab35cab9bb44b` carry the `HDFS.BLOCK_KEY.SERIAL_NO`
symbol from an ABANDONED activation at NameNode startup):

1. **Runtime.** Keep the value CONCRETE and publish `MINT_UNATTRIBUTED` when no
   admitted activation owns the mint — or publish the row. Never a symbol
   without a row.
2. **IMPORT.** A new invariant, BLOCKING: *every root symbol referenced by a
   session's expressions has a `RootMintRow`.*
3. **COMPOSE.** `Arms.arm` / `ComposedFamilies` refuse an arm whose delivered
   expression references such a symbol — `UNATTESTED_ARM` — instead of emitting
   an empty guard.
4. **Harness.** A PASS rule for `CLOCK_SKEW` (ordinal 0 is legitimate;
   `movedRoots` = the clock cells) in `experiments/hadoop/accept/report.py`.

## What the merged commit established

`0001` **Measure: a symbol with no row comes from an abandoned activation.**
Read-only, over `hdfs-11741` campaign #4.

* Each of the two NN rotation-2 replays publishes 4 `RootMintRow`s — all CLOCK,
  all of `REGION.094a8e3d` (`removeExpiredKeys`) — while its expression table
  names all 14 declared-root symbols. The 10 with no row: `HDFS.BLOCK_KEY.
  SERIAL_NO`, three `REGION.094a8e3d.in.*` and all six `REGION.aaa1cfd7.in.*`.
* **No refusal anywhere.** Neither session files `MINT_UNATTRIBUTED`,
  `EPOCH_UNMATCHED`, `ASSIGNMENT_UNPLANTED` or a `DECLARATION_MISSING` about a
  mint; the whole gap sets are DIAGNOSTIC.
* **The condition is the ABANDONED ACTIVATION, not the mint path.** The mint
  ran — `RootMint#configuredSource` reached `api.symbolizeExactField`
  (`runtime/RootMint.java:456`) and the VM has carried the symbol ever since —
  inside an activation of `REGION.aaa1cfd7` that the obligation FOCUSED.
  `ConcolicRegionRuntime#judgeFinishedOccurrence` (`:1672-1687`) abandons a
  focused activation that did not take the decision its obligation flips;
  `#abandonOccurrence` (`:1590-1596`) sets `active.abandoned = true`;
  `#closeOccurrence` sets `publishRows` only `if (!active.abandoned)`
  (`:1711-1714`) and returns at `:1784-1791` without
  `submitCompletedResultPublication`. So `RowPublication#publish` — and with it
  `RowPlaceholderMint#roots` (`runtime/RowPublication.java:71`), the only
  publisher of a `RootMintRow` — never runs. The session keeps the symbol and
  loses the row.
* **The counts match exactly.** `e635d55d`: `REGION.094a8e3d` 4 unfocused + 3
  focused → exactly 4 root rows; `REGION.aaa1cfd7` 2 focused + 0 unfocused → 0
  rows, and the serial is minted there. By contrast `af9801b6` (ADMITTED)
  publishes roots:1 decisions:5 writes:9 at its one focused occurrence and
  states all 14 roots.
* **Not this defect:** a mint with no active region at all (`generateKeys` at
  NameNode startup, before `startRecording`) returns false at
  `RootMint.java:395` and symbolizes nothing, so it leaves no symbol either.
  That is why the serial's first value `182905` is concrete everywhere.
* **The whole class, 11741 #4:** 7 of 13 sessions reference a declared-root
  symbol they publish no row for — 27 (symbol, session) pairs. `hdfs-17960`'s
  frozen gate corpus: 0.

## What the uncommitted diff holds (items 1–3, in progress)

`ConcolicRegionRuntime`, `RootMint`, `RowPlaceholderMint`, `RowPublication` —
the runtime half (item 1). Items 2 (the IMPORT invariant), 3 (`UNATTESTED_ARM`)
and 4 (the harness PASS rule) are NOT started. Read the diff before trusting
it; it was never built or run.

## Definition of done

Apply, finish items 2–4, then **make a fresh 11741 recording** — the existing
corpus cannot be repaired offline, because the rows the fix publishes were
never written — and re-run the 11741 acceptance campaign.

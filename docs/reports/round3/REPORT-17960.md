# d17960 — why the 39bedd768 17960 acceptance campaign was refused (READ-ONLY)
Source $SPO/wt-stage @39bedd768; run $MY/final-39bedd768-17960; baseline pass #8 $MY/final-f651c4879.

## 1. What refused
`logs/hdfs-17960.driver.log` carries no refusal text (:4 `-- hdfs-17960: exit=1 elapsed=656s`; summary row
`hdfs-17960 1 - - - MISSING - - 656`). The refusal is in `logs/hdfs-17960.log`:

    :188  [campaign] import gate: 14 row invariant violation(s), 0 blocking
    :190  [campaign] wave 0: 4 obligation(s), workers=8
    :191  [campaign] import gate: obligations-0000 published 2 session(s)
    :192  [campaign] import gate: 6 row invariant violation(s), 4 blocking
    :193-197 [campaign:error] stage=IMPORT component=ImportGate
             artifact=.../schedule/iteration-0000/campaign_gaps.jsonl
             reason=4 row invariants violated: epoch/sessions

The wave gate writes no gaps file of its own: `campaign_import_wave_gate` calls `campaign_import_gate`
(run_engine.sh:1969-1970), whose `--out` is the iteration's `campaign_gaps.jsonl`, APPENDED. The wave's six rows are
`out/hdfs-17960/schedule/iteration-0000/campaign_gaps.jsonl` lines 15-20 (1-14 = seed gate). Four BLOCKING, verbatim:

- L15 ADMISSION_GAP, session `793875fb482a10a4-4b39d011`, subject `epoch/sessions`:
  "invariant 1 (CONTRACT-SPEC SS2: every session states its role in manifest.json): 0 of 2 sessions state role SEED []; exactly one must"
- L18 UNSTATED_VALUE, session `cb67875d1d896d4d-73ab772f`, subject
  `decisions.jsonl seq=79 field=outcome <...SnapshotManager: void deleteSnapshot(...)>#u7#1`:
  "invariant 6 (CONTRACT-SPEC SS2: outcome says whether the published term HELD; the conjunct is outcome ? term : (not term)): at this session's own recorded root values the term is false and the row says true"
- L19 same session, `seq=140`, same site `#u7#1`, same detail (term false / row true).
- L20 same session, `seq=145`, subject `<...DirectorySnapshottableFeature: ...Snapshot removeSnapshot(...)>#u10#1`:
  "... the term is true and the row says false"
- L16/L17 = the 2 DIAGNOSTIC LINEAGE_LOST (invariant 4 site index, `writes.jsonl seq=122`), one per session.
Correction to the mandate: the third UNSTATED_VALUE is `removeSnapshot#u10#1`, not `deleteSnapshot#u7#1`; all three
are in ONE session, `cb67875d1d896d4d-73ab772f`.

## 2. `epoch/sessions` — the gate's session set, not a corpus fact
Producer `RowInvariants.sessionSet`, .../contract/RowInvariants.java:96-121 (gap at :114-121). It compares only the
SESSION SET handed to it — `SessionReader.seedSessionIds(sessions)` must have exactly one element — and looks at
nothing else: not obligations, not `obligation_results.jsonl`, not `iteration_manifest`.
The set is what PC2 symlinked. `campaign_import_wave_gate` (run_engine.sh:1947-1971) links ONLY the wave's NEW
sessions: `comm -13 sessions-before.txt <roster>` (:1956-1960, :1974-1977; roster taken at :2197).
`obligations-0000/sessions-before.txt` is exactly `seed-result-7cbb7bbc`, so the seed is excluded by construction and
`import-gate/sessions/` holds only the two FOCUSED sessions; the seed's own manifest.json says
`"role":"SEED","obligationIds":[]` and is fine. Deterministic construction bug that would refuse EVERY wave of EVERY
case. Confirmed by §5: over pass #8's full set (3 sessions incl. SEED) `epoch/sessions` does not appear.

## 3. `field=outcome` — a real row fact, and new this round
Producer `RowInvariants.decisions`, RowInvariants.java:481-497 (helpers `declaredRoots` :500-506, `truth` :519-533):
it evaluates the published `term` over the session's own DECLARED RootMintRow `recordedValue`s and demands
`truth(term) == row.outcome()`, returning early at :483 when no declared root is readable. `outcome` is NOT absent,
empty or wrong-typed — M-C/`JsonFields` is not implicated. The rows (that session's decisions.jsonl; `vmEventId` is
not a DecisionRow field):

    seq=79  siteId <...SnapshotManager: void deleteSnapshot(...)>#u7 ordinal=1 outcome=true  term=EXPR.8876a8d1504b1e4c clockReadings={}
    seq=140 siteId <...SnapshotManager: void deleteSnapshot(...)>#u7 ordinal=1 outcome=true  term=EXPR.659e35b4edb8b4a9 clockReadings={}
    seq=145 siteId <...DirectorySnapshottableFeature: ...removeSnapshot(...)>#u10 ordinal=1 outcome=false term=EXPR.28e65c000363f4cb clockReadings={}

All three terms are `ReadFrom(SnapshotManager.<marker>) op Y_Z_0` (`==` for 79/140, `!=` for 145), leaf symbol
`M_Z_field_SRC.50c885b3...SnapshotManager`. The session's one root row is
`rootId=HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED kind=MARKER recordedValue="true" declared=true seq=0`. At marker=true
`==0` is false (rows say true) and `!=0` is true (row says false); all three outcomes are instead consistent with
marker=FALSE — which is what the replay ran on: `obligations-0000/cb67875d1d896d4d/obligation.jsonl` carries
`rootAssignments:{"HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED":"false"}` and `obligation_query.smt2:6` asserts
`(not (not (= r_HDFS_CONFIG_SNAPSHOT_DELETION_ORDERED false)))`; the plant succeeded (no ASSIGNMENT_UNPLANTED /
UNPRODUCIBLE_ANSWER row in the wave). The wave-level `obligations.jsonl` prints `{}` — the pre-solve copy, not what ran.
So the wrong row is the ROOT row, not `outcome`: a focused session states the PRE-PLANT value. Deliberate and new
this round — RootMint.java:435-446 reads `observed` *before* `applyFocusedRootAssignment` ("WHAT THE REGION OBSERVED
... which in a focused replay is the recording's own"), hands it at :469-471, and
`ActiveRegion.recordConfiguredSourceMint` (ActiveRegion.java:517-546) writes it as both `observedValue` and
`recordedValue`, commenting "so this is never the wave's own value" (commit `f8543b075 A focused root mint states the
value it observed (invariant 8)`). Pass #8, same corpus, obligation ids, decision seqs and `term` EXPR ids:
`final-f651c4879/.../sessions/cb67875d1d896d4d-16309e20/decisions.jsonl` seq=79 true, 140 true, 145 false — IDENTICAL
outcomes; its `roots.jsonl` seq=121 has `recordedValue:""`, and empty ⇒ `truth()` null ⇒ invariant 6 never judged the
rows. This round filled the field with the seed's value, turning silently-unjudged rows into 3 BLOCKING ones.

## 4. Wave 0 otherwise
As before. `obligations-0000/explore_manifest.json` matches pass #8 field for field:
`tasks=11, proposed=4, answered=0, verdicts={}, state=OBLIGATIONS_PROPOSED, wave=0`. 4 obligations; 2 UNSAT
(`1673ef444a3682c5` at `deleteSnapshot#u15#1`, `5b629e50da39c272` at `serializeSnapshotSection#u61#1`, both "no world
of this corpus takes the other arm", `sessionId:""`), 2 ADMITTED — which is why the set is 2: only an ADMITTED
obligation publishes a session. Both manifests `role=FOCUSED` naming their one obligationId; both results read "the
focused prefix reproduced and ...deleteSnapshot(...)#u7#1 took true". Pass #8: same 4/2/2 split (its #u61 obligation
id was `72516d5dda280de7`). `obligations-0000/stderr.log` is 0 bytes.

Two deltas for the planner, neither the refusal:
- `793875fb482a10a4-4b39d011/roots.jsonl` is 0 bytes, its decisions start at seq=140 (no seq=79), and its gaps.jsonl
  carries `TASK_UNANSWERED REPLAY_PREFIX_UNMATCHED: the focused occurrence did not take the decision its obligation
  flips` — while `obligation_result.jsonl` still says ADMITTED. Pass #8's `793875fb482a10a4-26b11bef` had both rows.
  It escaped invariant 6 here only because `declaredRoots` came back empty.
- the focused root mint now publishes `seq=0` where pass #8 published `seq=121` (M-R3, LAST_SEQ deleted).

## 5. The fix, for the whole class
(a) and (b)/(c) are both real and independent; fixing either alone leaves the campaign refused.
(a) OWNER `run_engine.sh:1947-1971`. The IMPORT gate checks an EPOCH's session set and invariant 1 is a set-level
invariant, so the directory handed to it must be the epoch's WHOLE set: change the loop at :1956-1960 to link every
name from `campaign_session_roster "${sessions}"` into `${gate}/sessions`, and keep `campaign_wave_sessions` only to
compute `count` for the log line and the `count -eq 0` return (:1961-1968). `${gate}/obligations-0000 -> ${wave_dir}`
(:1955) already is what invariant 10 needs.
(b)/(c) — one class statement either way: `recordedValue` means "what this mint OBSERVED" (RootMint.java:435-446,
ActiveRegion.java:517-546). For a SEED that is the valuation the session ran under; for a FOCUSED replay it is not,
because the wave's assignment is planted after the read. Every check or lowering that reads `recordedValue` as "the
valuation this session executed under" is unsound on FOCUSED sessions — invariant 6 is one, and `Composer.java:1655`
(`root_domain__N: (= symbol literal)`) is next, since one symbol is shared across sessions.
- (c) recommended, OWNER `RowInvariants.java:481-506`: `decisions()` evaluates the term at the valuation the session
  RAN under — for FOCUSED, the wave's `rootAssignments` from the obligation its manifest names (ImportGateMain
  already reaches the worker dir, ImportGateMain.java:138), falling back to `recordedValue` for roots the wave did
  not assign; for SEED, `recordedValue`. At marker=false all three rows verify, and the laneA2 defect invariant 6 was
  written for is still caught in both roles.
- (b) alternative, OWNER `RootMint.java:440-446` + `ActiveRegion.java:517-546`: publish the post-plant value as
  `recordedValue`, keep the pre-plant one as `observedValue`. That costs the "centre for a relative domain" use named
  at ActiveRegion.java:524-531, so domain resolution (`RootDomain.java:106-108`) must move to `observedValue` in the
  same change.

Would this gate also have refused pass #8's corpus? YES. Offline, 39bedd768 jar, pass #8's full `sessions/`
(`$MY/d17960/gate-old/{summary.json,campaign_gaps.jsonl}`): sessions=3, violations=19, blocking=2, diagnostic=17,
`gaps:{LINEAGE_LOST:17, UNSTATED_VALUE:2}`. Both blocking rows are

    roots.jsonl seq=121 field=recordedValue HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED=
    "invariant 8 (HANDOVER SS1.3): a MARKER reading is spelled true or false"

once for `793875fb482a10a4-26b11bef`, once for `cb67875d1d896d4d-16309e20`. No `epoch/sessions` (the SEED is in that
set) and no invariant-6 row (an empty recordedValue is unjudgeable). Pass #8 was clean only because the gate never ran
over its focused sessions; the same corpus fails invariant 8 today, and `f8543b075` converted that latent invariant-8
refusal into three invariant-6 refusals.

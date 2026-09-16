
### 1.7 RowPublication (1,216) / SharedStateCapture (778) / SessionPublisher (291) / ConcolicResultPublisher (367) / ConcolicVmBroker (400) / JUnitMethodRunner (359) / GuardedStoreSites (230) / PathConditionWindow (204) / SymbolicMessageEnvelope (449)

| file | cluster | ln | notion | fired 17960 / 11741 | verdict |
|---|---|---:|---|---|---|
| RowPublication | entry/dispatch 34, decision rows 22 | 56 | R3 | 3,333 / 8,318 | KEEP — one entry point anywhere (`publish` ← `ConcolicResultPublisher:286`) |
| RowPublication | **root + placeholder 421** | 421 | R3 | placeholder: **4 rows on 17960, 0 on 11741**; `refusedDeclarations` and all five placeholder gap sites: **0 / 0** | **SPLIT-OUT `RowPlaceholderMint`**; delete the synthesis strength (§2.8) |
| RowPublication | write/read rows 220 | 220 | R3 | 100 / 25,206 writes (kinds INSTANCE 65 / MAP 21 / ARRAY 14 and 21,804 / 2,531 / 871; the `STATIC` branch at 1162 is never taken), 75 / 16,083 reads | KEEP |
| RowPublication | event-log + endpoint identity 103 | 103 | R2/R3 | `performer:877-890` fires as LINEAGE_LOST: **7 / 624** rows ("this read states activation -1") | **SPLIT-OUT `LoggedEventSites`** |
| RowPublication | location vocabulary 25, target row 39 | 64 | R3 | targets 6 (4 `observedFatal`) / 194 (all `observedFatal=false, reachedAnchor=true`) | KEEP the target row; **FOLD** `locationKey`/`location`/`kindOfLocation` into `SharedStateCapture`'s (the two spellings disagree: only SharedStateCapture's validates the kind set and `MAP_STATE_SLOT`; RowPublication's defaults the kind to INSTANCE at 1165) |
| SharedStateCapture | read-out paging + decode 153, record reduction 82 | 235 | R3 source | yes / yes | KEEP |
| SharedStateCapture | admission/fault vocabulary 202 | 202 | R3 refusal | **0 / 0** — `failedShared:349-358` filed no `UNSTATED_VALUE` row in either corpus | KEEP the 4 live codes; **DELETE** `SELECT_NO_ACTIVE_CONTEXT`/`SELECT_FIELD_NOT_FOUND`/`SELECT_UNSUPPORTED_TARGET`/`INVOCATION_FAILED` (426–429) + their 4 unreachable `reason()` cases (491–498) + 6 unused constants (399, 404, 410, 414, 417, 451) + 2 unused imports |
| SessionPublisher | registry + open/manifest 40, per-kind writers 39, expression table 35, io 57 | 171 | R7 | yes (17960 manifests `{SEED:1, FOCUSED:2}`) | KEEP; **DELETE `closeAll`** (7 lines; its only caller is its own `resetForTests:287`) and make `SESSIONS`/`at` private — in production the static registry can hold one entry (−≈25) |
| ConcolicResultPublisher | exit barrier 98, daemon pool 83, run totals + halt 42, goal/target 15, gap funnel 4 | 242 | R7 | `TASK_UNANSWERED` 4 / 1,106 (reasons come from CTP/CRR: 17960 = 4× ROOT_NEVER_EXECUTED; 11741 = 363 + 260 REPLAY_PREFIX_UNMATCHED, 118 ROOT_NEVER_EXECUTED, ≈365 OCCURRENCE_ANCHOR_UNMATCHED) | KEEP. **The legacy `CONCOLIC_REGION_RESULT` envelope is gone** (1 javadoc hit tree-wide, 0 in `run_engine.sh`). Its own three reasons (`TERMINAL_NEVER_REACHED`, `RESULT_PUBLICATION_REJECTED`, `RESULT_PUBLICATION_FAILED`) fired 0 / 0 |
| ConcolicVmBroker | status ABI 16, reflective bind 87, 8 capability groups 145 | 248 | R1 | yes (the `CAUSYNTH-SESSION\|GUARDED_STORE_SITES` line appears once per session: 3 / 81) | KEEP — **all 23 bound capabilities are invoked** (per-call-site list measured; the cleanup-2 `sharedFieldVersions` demand is gone). Minor: 2 dead null-guards (140, 263) after `requireCurrentCapabilities`, and 4 status constants only `describe()` mentions |
| JUnitMethodRunner | session lifetime + exit 64 | 64 | R1/R7 | yes (all 4 `execute.sh` launch it) | KEEP |
| JUnitMethodRunner | reflective JUnit lifecycle 198 | 198 | none (harness) | yes | **SPLIT-OUT `JUnitLifecycle`** — shares only `main` with the session half |
| GuardedStoreSites | install + refusal 49, table build 63, wire format 22 | 134 | R1 (the static slice's one runtime consumer) | `installed=17\|guardSites=22` ×3 (17960), `installed=5\|guardSites=7` ×81 (11741); **zero** `GUARDED_STORE_SITES_*` refusals | KEEP; **DELETE the dead `causynth.static.scope.map` property branch** (§2.7) |
| PathConditionWindow | window value 48, VM exact-range read 51, event index decode 39 | 138 | R3 | yes (every decision term) | KEEP minus **`mode()` + `TREE_MODE`/`WINDOW_MODE` + `windowed` + `Read.chars`/`Read.source` (≈14 lines, 0 readers)**; note `ConcolicRegionRuntime:3314` recomputes `contiguousConditionIndices`, the decision `forEvent:124-131` already took |
| SymbolicMessageEnvelope | outbound staging 73, inbound install/decode 142, codec 22, entry 37, clear 6 | 280 | R4 | 53,424 / 3,554 rows; `installInbound`'s own refusal fired **0 / 0** | KEEP; **DELETE `Entry.ordinal()`** (0 callers) and decide `reportUnattached` (§2.6) |

### 1.8 What cleanup round 2 left behind: nothing in the runtime
All of R1/R2's deletions are executed at this tip: the `CONCOLIC_REGION_RESULT` envelope, `ModelAssignment`/
`GuardedReadAssignment`, `FocusedReplay`'s `causynth.task` bundle, `RowRuntime`'s five write-only maps, `Lineage.path`,
`SessionPublisher.ROOT_DOMAINS`, `SymbolicMessageEnvelope.inboundUnattached`/`peek`, `Interactions.expressionRef`, the
`sharedFieldVersions` VM demand, `ReachedUnder` + the thread-name filter, the address-drift reconciliation, the
`causynth.trace.max.events` cap, and the junit/diagnostics keys — 0 code hits each; only three comments still name them
(`SessionPublisher:33`, `SharedStateCapture:424`, `GuardedStoreSites:59`).

### 1.9 FocusedReplay (530) — R5, **X15 is editing this file right now**
Reported, not proposed. Clusters: focus-row load 112, focus set/identity 54, mint-value answers 54, prefix matcher +
verdicts 92, ctor/reset 17. Fired: 80 focus rows (11741) / 2 (17960); `results` wrote 73 obligation rows on 11741
(68 NOT_ADMITTED, 5 ADMITTED) and 2 on 17960 (both ADMITTED); the prefix refusal fired 363 times on 11741.
**There is exactly one mint-value decision**: `ConcolicRegionRuntime.focusedRootValue:2228-2252`, called from the declared-field
writer (`:2267`) and the manual-field mint (`:4128`); `FocusedReplay.clockSkew`/`rootAssignment` each have exactly one
caller (`:2236`, `:2239`). Clock deltas fire on 11741 (13 of 80 focus rows carry non-empty `clockDeltas`) and not on
17960 (both rows `{}`, consistent with 3 MARKER roots). `answers` non-empty 28/80 and 0/2; `rootAssignments` 31/80 and
2/2; `unproducible` empty everywhere; `ASSIGNMENT_UNPLANTED` (the one BLOCKING gap in this area) fired 0 / 0.
Two things for X15's own list, not a mandate: `loadPlanRows:326-329` defaults a flip row with no `ordinal` to **1** and
no `outcome` to **false**; `:358` prints an unreadable focus row to stderr after `handedAFocusRow` is already true, so the
session still reports role FOCUSED with however many obligations it parsed and nothing states the shortfall.

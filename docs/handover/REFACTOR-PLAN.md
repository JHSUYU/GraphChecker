# The 2026-10-18 rewrite: plan (owner-approved)

The owner allowed a large-scale rewrite because the code is too bloated; acceptance is a rerun of all 20 Solr
cases at the end (`experiments/solr/solr-cases.tsv`), each alone on the pool, and debugging what breaks. Every
number below is measured (analysis dirs under `/bigtemp/vnr3ne/analysis/solr-2026-10-1[78]/`).

## Rules

1. One implementation per concept: what a rewrite replaces is deleted -- old paths, flags, unused helpers, tests of
   removed mechanisms (merge the rest table-driven).
2. Where semantics do not change, outputs stay byte-identical on the references: planner 05 r5, 05 r2, 13 r10,
   19 r10, 21 r13 (compressed copies in `analysis/solr-2026-10-17/nfs/`); composer 13, 39, 21, 10.
3. Where semantics change (the exploration core), regression = the 8 bug checks stay SAT + CONFIRMED + native; the
   study checks' claims are equal or more complete.
4. Measure first; a change lands with its before/after numbers.
5. At most 5 coding agents (owner 2026-10-18); one branch each; the lead reviews and merges into `solr-int` = `system/solr`.

## Already on system/solr

GROW pipeline (7b3400ea8); superstep + window walk (36518d672); parallel round and Frontier with its memory fix
(f7850b959); live-set planner hold rule (ae624c5c6); gzip rows (85944a0dd); EMIT gap ledger in Java (6f9921824);
compaction step 1, unread gap text not held (1444260e9).

## Workstreams

| | what | evidence | acceptance |
|---|---|---|---|
| A data representation (solr-compact) | interned ids, primitive-keyed maps, int sets/bitsets for the walk's sets, pooled Endpoint/LocationId/Frame, one representation for planner, composer, solvers, CONFIRM, gate | 05 r5 walk end 12,671 -> 5,012 MB after step 2; 07 composer read 9,379 -> 3,523; round 549 -> 470 s (redundancy/FINDINGS.md) | byte-identical |
| B holding composer (solr-composebatch) | everything held but reads/writes, LRU at 0.15 of heap, re-read on demand (RowHold) | 07: 1/309 -> 309/309 paths, live after read 2.9 GB | byte-identical; 5 planner refs; a full z3 decide on 07's 420 MB body |
| C scheduler (solr-stream2) | dispatch by most room per kind; a killed replay re-queued, never a verdict; land at collection; gate over new sessions; GROW plan/weave in the background; multi-question solvers + oldest-wait rule; z3 answers reused by query text; planner/solvers charged their measured need; a GROW re-run off EXPLORE's critical path exactly when no obligation can come from it, COMPOSE waiting for its paths' re-runs and havocking the grown regions otherwise | 07: pool 70-90 % idle after minute 17; answers waited median 329 s; gate 2491 s; solve queue 2593 ob-min; 33 kills / 31 re-asks; re-runs 36 % of replay-s (idle-pool/, obligation-redundancy/) | invariants named and tested; canary 13 alone |
| D exploration core | SAGE's generational bound (a world flipped at schedule event e_i offers only decisions its replay produced after e_i; the prefix is identical by focused replay); the arm key keyed by exactly what the query reads; the world-depth parameter KEPT as the owner's control of how many branches are explored (named BOUNDED when it cuts), the bound and key applying at any depth; a constraint-slice answer cache; STATUS defect 70 | depth 1: 14 round 4 84 % of 12,438 obligations re-ask prefix decisions the parent asked; 39 40-55 % (world-dedup/) | 8 bug checks hold; study claims equal or more complete |
| E replay and VM | the stall-end halt (43 of 72 stall-ended replays ran on, 5 to the 2400 s timeout); replay heap basis by percentile, not the largest peak (2048 -> 9728 MB); read-out decoding off the VM's one thread (busy 77-87 %); stop at the window close | replay-tail/ | sessions unchanged; 13 and 07 claims unchanged |
| F serial fixed cost | static pass ~9 min, seed replay ~9.5 min, instrument ~1.4 min: cache static artifacts by (tree, static-pass version) digest, parallel passes; measure seed reuse | 07/13 stage metrics | artifacts byte-identical |
| G NFS leftovers | worker schedule prefix/suffix (625 MB in 05 round 0) and flip query files (1.47 GB round 4) gzip; `campaign_solver_read_seed_mb_s` 20 -> measured ~160 | nfs/ | byte-identical decoded |
| H cleanup | shard branches (solr-parplan 3df494a3a, solr-shard d3b663462) shelved, not merged; case-level bounds the new rules replace deleted; docs present-tense; tests table-driven | | gate |

## Order

1. Now: A, B, C running; E starts. B merges first (after its planner refs and the 07 decide), A rebases on it.
2. Then: D once A's step 2 is in (both touch ClosurePlanner) and the world-dedup and capability analyses report;
   F and G as slots free.
3. Integration: everything on system/solr, full gate, a snapshot, then the 20 cases each alone, bug checks first;
   debug, then the readings, STATUS, STATE, TODO and OPTIMIZATIONS.

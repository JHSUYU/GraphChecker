# Checking a verdict and its `.smt` (long-term; read before counting anything as done)

Part of every agent's long-term memory ([RULES.md](RULES.md)). The owner's bar: "如果我们确实正确的跑出了.smt。包含必要的
因果链，符号变量，符号传播。没有新bug也是可以理解的". A row in `summary.tsv` is not a verdict, and a verdict is not
done until its `candidate.smt2` is right. Every lead so far has counted a case as done that was not; each trap below
is one of those, with how it fooled the check and how to see it now.

## 1. The mechanical checks, on every finished case

```bash
GC_OUT=<out> tools/rounds/round-verify.sh <round> [case...]
```

One line per finished case: the claim, how EXPLORE ended (`end=`), z3 on the exported `final/candidate.smt2`,
`BOUNDED:<keys>` (a declared bound cut the search: `result.json` `bounded`), `UNBOUND:<n>` (distinct boundary
variables a fatal condition names that no message family binds: `report/<case>/cone.json` `unbound`),
`BLOCKING:<codes>`, `moved=`/`polarityDecides=`, `leaves=` (the formula's leaf symbols, roots/reads/handoffs; 0 is
`NO-SYMBOL`), `confirmed`. The last line counts BOUNDED and UNBOUND cases.

**An UNSAT is done when** the claim is `UNSAT_CLOSED`, `end=(FIXED_POINT)`, z3 says unsat on the file, there is no
BOUNDED, no UNBOUND on any path, no BLOCKING gap, `defects` is empty (`result.json`; e.g. `OPEN_ARM_UNANSWERED`,
`UNSAT_BESIDE_REFUSED`, `EXPLORATION_CUT` are RUN_DEFECTs), and either `leaves > 0` or a written reason, read in the
code, why the chain is constant inside the window.

**A SAT is done when** the claim is `SAT_CANDIDATE`, CONFIRM confirmed it (`final/confirm.json`), `claim.json`
`movedRoots` names at least one root, `polarityDecides` is true, the claimed path's cone has no unbound handoff
(`cone.json` `unbound`; other paths' are reported as `unboundOffWitness`, lead decision 2026-10-06, RULES), and the
native reproduction ran (`final/reproduce.json`: `reproduced`/`runs`, record k/N; a race-dependent bug may reproduce
4/10). A known bug also needs its mandated mechanism (RULES "Acceptance"; `report.py` PASS) with the mechanism's
roots in `movedRoots`.

## 2. Reading the formula by hand (the hand check written into STATUS)

```bash
python3 tools/analysis/smt-legend.py --repo <the case's tree> <out>/<case>      # names every leaf symbol
```

- The tree is the one the case ran on (`experiments/hadoop/*/case.sh repo=`): r5 `/bigtemp/vnr3ne/wt/hadoop-hdfs-
  study-r5` for every HDFS case but 11741 (`hadoop-hdfs-11741-r5`). The legend reads the tree's classes with `javap`.
- It groups the leaves: ROOT (category, door or configuration key, where minted), CLOCK, HANDOFF (port `<- producer`
  node and method, or `<- ?` when no producer is stated), READ (class.method and the candidate fields), OTHER.
- The formula's shape: `fatal_target` = OR of `path_selector__i`, exactly one selected; `path_fatal__i` = `(=> sel_i
  (and π_i φ_i reads_i))` (path condition, fatal predicate, read pins); `message_family__i__h` = under `sel_i`
  exactly one arm, each arm `π_q ∧ v_H = e_q` (the producer's own condition and expression: this is the
  cross-process propagation); containers are `AssocState` values built by `assoc_put/remove` in `container_dag__*`
  define-funs; roots are `M_<T>_field_REGION.<region>.in.<site>.occ.<hash>_<type>` (clocks, door markers) and
  `M_<T>_field_SRC.<hash>`/`r_CONFIG_<key>` (sources, configuration).
- **Write into STATUS** for each SAT the chain from each moved root through the handoffs and reads to the fatal, with
  file:line in the system's code; for each UNSAT one line saying why no world of the corpus reaches the fatal.
- For a SAT, three more questions (11741, 2026-09-22): is each moved root necessary (pin it to its recorded value in
  the file: the query must go unsat); do other mechanism roots sit at z3's default only because nothing constrains
  them; did the replay of the witness actually observe the fatal (`targets.jsonl` `observedFatal`).

## 3. The traps (each fooled a lead; how to see it now)

1. **A verdict row from a cut search** (HG4's "23 UNSAT", 2026-10-05): `UNSAT_CLOSED` whose exploration ended
   `CAMPAIGN_BUDGET_REACHED`. Now an `EXPLORATION_CUT` RUN_DEFECT; check `end=`. Under a 20-case sweep the 90-min
   default cut six cases (HG9, 2026-10-06): rerun them with `CASE_TIMEOUT_SECONDS=10800`; they closed (11 26 33 37).
2. **Unbound handoffs in an UNSAT counted as done** (HG9, 2026-10-06): 07 (6 unbound: a relayed QJM segment) and 14
   (3: the block fields DataXceiver received from the client, 45 HELD rows) passed round-verify before it read
   `cone.json`. Now `UNBOUND:<n>`; also look for `<- ?` and "producer unstated" (`gaps.json`, the legend).
3. **A fixed point reached under a bound** (05 06 08 09, HG8F/HG9): `end=(FIXED_POINT)` while some task rounds read
   only `region_path_max_paths_per_region` (32) recorded paths. Now `BOUNDED:`; before `bounded` existed, grep
   `gaps.json` for subjects ending ` max-paths-per-region=32`.
4. **A fatal arm that is the constant `false`** (15, 39; 2026-10-05): every `path_fatal` ended in `false` because the
   helper branch deciding the predicate's value (`getBlockUCState`'s `uc == null ? COMPLETE : …`) was never part of
   it, so the UNSAT was free. Look at the `path_fatal__i` assertions: an UNSAT where every fatal is `false` while the
   guard reads tracked state is a scope hole until shown otherwise (fixed by the decider rule, b650a0f6d).
5. **The arm where the bug lives never ran** (39, DO2): the open arm `uc != null` was asked as a flip six times and
   every replay came back NOT_ADMITTED, yet the case said UNSAT. Now named `OPEN_ARM_UNANSWERED` (RUN_DEFECT); read
   `result.json` `openArms` / `defects`. An arm closed UNSAT (or BOUNDED) after refuted worlds (`WORLD_REFUTED`)
   names each on its row (`refutedWorlds`) and in `restsOnRefutations`: read each world's conditions and the
   workload's exception against the code before counting the UNSAT -- a refutation is the run's claim about one
   world, not a fact about the arm.
6. **A root whose domain is one value** (40): `dfs.namenode.replication.min` had domain [1,1] (the hull ignored a
   comparison through a field), so the UNSAT said nothing about other values. The domain now takes every literal a
   recorded decision compares the root with, within its own validation (`validMin`/`validMax` on the mint row). Read
   the root's bounds in the file (the `r_CONFIG_*` declarations and their range asserts) before reading an UNSAT as
   covering a configuration.
7. **A value frozen at its recording (HELD)**: three causes seen. The producer exported nothing (12's
   `NNHAStatusHeartbeatProto.Txid`, legend `<- ?`); the producer's occurrence was never planned (14, fixed by (b2):
   EXPLORE demands what COMPOSE keeps); the "state" was the engine's own carrier field read back after an attach
   (11741, `PBHelper.convert` bci 74: `HandoffLeafCarrier`), engine plumbing that must never be state (codec-capture,
   TODO). A HELD read inside the witness's cone is a broken chain.
8. **Unbound values off the witness** (12, AW4): the SAT's own chain was closed but three other paths held the txid
   (each heartbeat response its own producer occurrence). A SAT is judged on its claimed path; an UNSAT on every path
   (RULES).
9. **The let-binding trap** (2026-09-24): `(let ((s STATE)) (ite (assoc_has s k) (assoc_read s k) null))` -- a naive
   walk takes `s` for the state and finds no symbols. The lead told the owner "the DN's key map is all constants";
   wrong. Always bind let/define-fun parameters when reading a formula (the legend and cone.py do).
10. **NO-SYMBOL accepted without a reason**: an UNSAT over nothing that moves is right only when the code shows why
    (28 31: the block-pool map filled before the window, removed only after the target in unnamed work; 48: one
    thread under the namesystem lock; 45: the edit log's own segment state). Write the reason, with file:line.
11. **A PASS line or a finding kind alone** (17960 once "passed" at valuation 0 with no root moved; v9's bug1/17967
    moved only a clock and passed because four keys collapsed onto one handoff symbol). Read `movedRoots`, the cone and
    the three questions of §2.
12. **CONFIRM with no verdict is no SAT** (12 in HG9: the model's order waited on an event that never exited within
    300 s, `CONFIRM_NO_VERDICT`). Read `confirm.json` and `defects`; with budget left the claim loop excludes the
    model and claims the next one.
13. **A verdict from an older body or looser checks is not current** (the time-model family's "UNSAT" in HG8E, 07's
    and 39's earlier UNSATs). Count only verdicts on the current body that pass §1.
14. **An engine artifact that looks like a regression**: vm-hg5's outside-mutation mark exposed 11741's unplanned
    key-update occurrence that the old VM missed silently (2026-10-05). Read before reverting.
15. **One run is not a verdict on a racy case** (11741, solr-18413; 22's seed varies 0-66 give-ups): rerun before
    blaming a branch, and compare with the base body under the same budget (D1's SH55).

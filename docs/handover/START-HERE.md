# START HERE: ZooKeeper's old bugs put back, on liftlab (system/zookeeper-buggy-detect, 2026-10-28)

You take over the ZooKeeper buggy-detect branch. This file is self-contained: what the branch holds, the result, how
to build the trees, run a case or all of them and read the result, what is left, and the rules.
- **Repo:** `/u/vnr3ne/GraphChecker`, GitHub `git@github.com:JHSUYU/GraphChecker.git`, branch
  **`system/zookeeper-buggy-detect`**: `system/zookeeper` (the 16 ad hoc cases; their takeover file is
  [zookeeper-START-HERE.md](zookeeper-START-HERE.md)) plus two old bugs put back, one case each, and the engine work
  they and the integration line before them added (STATE §Z "The buggy-detect line"). It runs on liftlab: the host
  ledger charges memory, no lift above 70 % (29b8812dc reverted the CloudLab scheduling layer; that cluster's record is
  the tag `archive/system/zookeeper-cloudlab`).
- **The trees:** the fork `https://github.com/JHSUYU/zookeeper.git`, one branch per bug, on the fork commit 92c0f2b5
  (`graphchecker/zookeeper-checks` 889f0e96 plus workload ports below the ephemeral range):
  `graphchecker/zk-bug-710` (4260614d) and `graphchecker/zk-bug-2886` (b8b7149f), the trees `zookeeper-bug-710` and
  `zookeeper-bug-2886` of [`experiments/zookeeper/trees.tsv`](../../experiments/zookeeper/trees.tsv);
  `graphchecker/zk-bug-710-control` (c0488b9b) and `graphchecker/zk-bug-2886-control` (328765d1) carry the same
  workloads and markers on the fixed code (the caveat below).
- **The cases:** `experiments/zookeeper/zk-buggy-<jira>/` (case.sh, workflow.properties and a README with the bug, what
  was put back, the workload, every declaration and every run), listed in
  [`experiments/zookeeper/zookeeper-buggy-cases.tsv`](../../experiments/zookeeper/zookeeper-buggy-cases.tsv) (budget
  21600 s each); `experiments/accept/report.py` holds their expected mechanism.
- **VM image:** `/bigtemp/vnr3ne/vm-force13/j2sdk-image` (as every ZooKeeper case).

## 1. The goal and the result

The owner (2026-10-26): put back by hand, on today's trees, the old bugs that make an ad hoc check fail at the
point's OWN declared throw, and detect them; a bug counts only if GraphChecker's witness fires that throw, confirmed
in the VM, reproduced natively k/N with the control 0/N, report.py PASS. A check truly beyond GraphChecker's
capability is not forced. ZooKeeper has two such bugs, both at zk-adhoc-02's throw (`SessionTrackerImpl.checkSession`'s
`SessionMovedException`, line 367). [BUGGY-DETECT.md](BUGGY-DETECT.md) has the table of all four systems.

| case | bug | CloudLab, 2026-10-26 | liftlab, B1 |
| --- | --- | --- | --- |
| zk-buggy-710 | ZOOKEEPER-710: a SessionMoved never tears the connection down | **SAT** STATE_PAIRING_FLIPPED (the old write's `session.owner` reads paired with the takeover's REVALIDATE), confirmed, native 10/10, control 0/10, PASS (ZB6, 361 s) | B1: SAT, CONFIRM, native 10/10, control 0/10, report.py PASS, 308 s (B1-zk-buggy-710) |
| zk-buggy-2886 | ZOOKEEPER-2886: a multi's SessionMoved stays a per-op error | **SAT**, the same pairing in the second multi, confirmed, native 10/10, control 0/10, PASS (ZB6, 363 s) | B1: SAT, CONFIRM, native 10/10, control 0/10, report.py PASS, 294 s (B1-zk-buggy-2886) |

The caveat (each README): the witness is the plain world, and each fix changes only what follows the throw, so the
fixed-code controls reach the same throw (710's ZC2 and 2886's ZC1: SAT, confirmed, 10/10). The owner (2026-10-27/28)
counts both as detected.

## 2. Read, in this order

1. This file, then [BUGGY-DETECT.md](BUGGY-DETECT.md) and the two case READMEs.
2. [STATE.md](STATE.md) §Z (its "The buggy-detect line": what this branch adds to `system/zookeeper`) and
   [TODO.md](TODO.md) "ZooKeeper: the buggy-detect line" (what is open).
3. [zookeeper-START-HERE.md](zookeeper-START-HERE.md) for the 16 ad hoc cases, which this branch runs too.
4. [RULES.md](RULES.md), [CHECKING.md](CHECKING.md), [OPERATIONS.md](OPERATIONS.md), [LESSONS.md](LESSONS.md) §10.

## 3. Running

Run every command with `env -u BASH_ENV`; the lead's session runs on lift11 (the control host, no Maven). The
workers are lift02-15 less lift07 (unreachable since 2026-10-23) and lift11; Maven only on lift02-06 and lift08-10.

1. **Snapshot** of the branch (an explicit commit; never rebuild one a run reads):
   ```
   flock /localtmp/vnr3ne/worktree-add.lock bash tools/lib/worktree-add.sh /u/vnr3ne/gc-run/bd-zookeeper-<n> <commit> --detach
   env -u BASH_ENV tools/onlift.sh -h lift03 -g 6 bash -c 'cd /u/vnr3ne/gc-run/bd-zookeeper-<n> && mvn -q -o package -DskipTests'
   ```
   B1's is `/u/vnr3ne/gc-run/bd-zookeeper-1`.
2. **The trees**, into the buggy-detect tree set (one for every system's bug trees) and its Maven repositories, from a
   worktree of the branch (the script first builds its checkout's jar, so never from a snapshot a run reads):
   ```
   cd <worktree of system/zookeeper-buggy-detect>
   env -u BASH_ENV tools/onlift.sh -h lift03 -g 8 env GC_TREES=/bigtemp/vnr3ne/wt/bd-trees-1 GC_M2=/bigtemp/vnr3ne/m2/bd-1 \
     bash experiments/zookeeper/prepare-trees.sh zookeeper-bug-710 zookeeper-bug-2886
   ```
   `prepare-trees.sh` clones each named tree's fork branch (`trees.tsv`) into `$GC_TREES/<name>` (a directory already
   there is only built), builds the workload module of every case on it into `$GC_M2/zookeeper<the tree's path, / as _>`
   and runs each case's workload once natively: one `PASSED` line per case (B1's build: `zk-buggy-710` 177 s,
   `zk-buggy-2886` 155 s on lift03). A control: clone `graphchecker/zk-bug-<jira>-control` into another tree set's
   `zookeeper-bug-<jira>` and run the script with that `GC_TREES`. Never rebuild a tree set a run reads, and never run
   natives on it.
3. **The cases**, from lift11 (B1 is `/bigtemp/vnr3ne/analysis/buggy-detect-liftlab-2026-10-28/launch-b1.sh zookeeper
   zk-buggy-710 zk-buggy-2886`, which does exactly this):
   ```
   cd /u/vnr3ne/gc-run/bd-zookeeper-1 && env -u BASH_ENV \
     GC_OUT=/bigtemp/vnr3ne/gc-out/buggy-detect GC_TREES=/bigtemp/vnr3ne/wt/bd-trees-1 GC_M2=/bigtemp/vnr3ne/m2/bd-1 \
     LIFTS="lift02 lift03 lift04 lift05 lift06 lift08 lift09 lift10 lift12 lift13 lift14" \
     CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-force13/j2sdk-image CASE_TIMEOUT_SECONDS=21600 PRUNE=0 \
     CASES="zk-buggy-710 zk-buggy-2886" tools/rounds/launch-round.sh /u/vnr3ne/gc-run/bd-zookeeper-1 B1
   ```
   One case: `CASES=zk-buggy-710`. Each case writes `$GC_OUT/accept-<ROUND>-<case>/` (B1:
   `/bigtemp/vnr3ne/gc-out/buggy-detect/accept-B1-zk-buggy-710`, `-zk-buggy-2886`); a round's name is used once per case.
   Stop one with `tools/rounds/stop-run.sh <ROUND>-<case>` (never by pattern).
4. **Reading:** `GC_OUT=... tools/rounds/round-status.sh B1` (stage or verdict per case); `tools/rounds/round-verify.sh B1
   zk-buggy-710` (how EXPLORE ended, z3 on the formula, BLOCKING gaps, moved roots, CONFIRM); the verdict and
   report.py's PASS/FAIL against the expected mechanism are `<run>/summary.tsv` and `<run>/report/<case>/report.md`
   (by hand: `python3 experiments/accept/report.py <case> <run>/out/<case> <report dir>`); native k/N is
   `<run>/out/<case>/schedule/final/reproduce.json`; `tools/analysis/smt-legend.py <run>/out/<case>` names every symbol
   of `candidate.smt2` for the hand reading; `python3 tools/analysis/vacuity.py --latest --detail <run>` on any UNSAT.
   Then the case README's "On liftlab" line and BUGGY-DETECT.md's B1 column.

## 4. What is left

TODO "ZooKeeper: the buggy-detect line": B1's verdicts and the controls on liftlab; the map-removal encoding (the
`zk-compose` design, whose branch was never pushed); the re-gating of a batch that admitted a later-dropped GROW
re-run. Nothing else is owed by this branch; the ad hoc cases' parked items are TODO "ZooKeeper".

## 5. Rules you must keep (RULES.md has each)

- A bug counts only at the point's own throw, confirmed, reproduced natively with the control 0/N; never force a check
  beyond GraphChecker's capability; CONFIRM and REPRODUCE stay.
- General fixes only, no per-case engine code; a tree workaround is small, marked `// GraphChecker:`, makes an order
  controllable or a value trackable, never switches the fatal outcome, and is named in STATUS "Per-system surface".
  Every engine change on this branch was independently reviewed before it counted.
- Kill only by explicit pid or `stop-run.sh`; never `git add -A`; never rebuild a tree or snapshot a run reads.
- Commits as `Zhenyu Li <zhl136@ucsd.edu>` with the trailer `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`;
  push GraphChecker only with the owner's OK; the ZooKeeper fork may be pushed, apache never.

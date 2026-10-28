# ZOOKEEPER-710 put back (zk-buggy-710, point zk-adhoc-02)

## The bug

[ZOOKEEPER-710](https://issues.apache.org/jira/browse/ZOOKEEPER-710) (fix
[b1c614b2](https://github.com/apache/zookeeper/commit/b1c614b2ca982b2e029d11605717846af790870f), 2010):
a permanent `SESSIONMOVED` after a client reconnects. `session.owner` is the `LearnerHandler` of the
follower that last owns the session (`Leader.revalidateSession` calls `zk.setOwner(id, learnerHandler)`,
and every forwarded request carries `request.setOwner(learnerHandler)`); the leader's
`SessionTrackerImpl.checkSession(sessionId, request.getOwner())` compares them and throws
`SessionMovedException` (master line 367) when they differ. When a late REVALIDATE re-points
`session.owner` at another server, the client's next request throws there; because that
`SessionMoved` was returned as an ordinary error, the connection was never torn down and every later
request on it threw again: a permanent `SESSIONMOVED`. The fix makes `FinalRequestProcessor`
catch `SessionMovedException` and call `cnxn.sendCloseSession()`, so the client reconnects and
revalidates.

Point zk-adhoc-02 is that throw: `SessionTrackerImpl.checkSession`'s `session.owner != owner`
`SessionMovedException`.

## What was put back, on graphchecker/zk-bug-710

`graphchecker/zk-bug-710` = the fork commit 92c0f2b5 (`graphchecker/zookeeper-checks` 889f0e96, the tree every
ZooKeeper check runs, plus workload ports below the ephemeral range) plus:

- **The bug, by hand** (e3659a88): `FinalRequestProcessor.processServed` no longer catches
  `SessionMovedException` to call `cnxn.sendCloseSession()`. A non-multi `SessionMoved` out of Prep now
  falls into the generic `catch (KeeperException e) { err = e.code(); }` and goes back as an ordinary
  `SESSIONMOVED` error, the connection stays open, and the session's next request throws again. Only
  the fix's catch block is removed (the `SessionMovedException` import stays: ZOOKEEPER-2886's code uses
  it). The fix's own test changes (QuorumTest's `testSessionMoved*`, which assert the fixed
  `ConnectionLoss`) stay in the tree; they are not this case's workload.
- **The workload and the target** (dfc0cee9, then 43ff1cb2, 5da76416, 4260614d after the runs below):
  `CausynthSessionMoved710Test`, and `zk-buggy-710` beside `zk-adhoc-02` in the
  `@CausynthExceptionTarget` on `checkSession`'s `SessionMovedException` (line 367).

## The workload

`org.apache.zookeeper.test.CausynthSessionMoved710Test#aMovedConnectionKeepsThrowing` (QuorumBase, the
five-peer ensemble zk-adhoc-02 uses; QuorumTest's `testSessionMoved*` assert the fixed behaviour and fail on
the buggy tree, and they send the old connection's request after `dontReconnect`, which fails it on the
client before it is sent: `ClientCnxn.queuePacket` refuses every packet once `closing` is set). Peer5 is
the leader (highest id). On the test thread:

1. the old handle connects to follower F (`(leader+1)%5`) and creates `/sm710` (EPHEMERAL);
2. a takeover thread starts; it sleeps 5 s, then opens a second handle on follower G (`(leader+2)%5`) with
   the same session id and password (its REVALIDATE sets `session.owner` to G's LearnerHandler) and
   writes once;
3. the old handle writes `/sm710` (w1); then w2 runs on a thread of its own, started after w1 returns
   and joined; each write catches its `KeeperException` (it acts only after the throw);
4. the test joins the takeover and ends without closing either handle (the servers' shutdown ends them).

Natively both old writes finish long before the takeover (the recording's whole window took 882 ms), so
each reads `session.owner = F` and no `SessionMoved` fires; the test passes on the buggy and the fixed tree.
The bug's world is the one where the takeover's REVALIDATE lands before an old write's `checkSession`.

Workarounds in the workload (each makes an order controllable or a value composable; none switches the
fatal outcome):
- **the takeover's delay, with no happens-before from the old writes** (zk-bugs-container-reuse's
  workaround): v1 opened the second handle on the test thread after the synchronous writes returned, so the
  takeover was causally after every old write and no world ordering it first could be replayed;
- **no close at the end**: a `close()` sends `closeSession`, whose `setSessionClosing` is a second
  in-window writer of `SessionImpl.isClosing`, which `checkSession` also reads; COMPOSE states a writer
  occurrence's whole delivery in one arm, so that second writer coupled `isClosing` to the createSession's
  owner and made the takeover's owner unpairable (ZB3);
- **w2 on a thread of its own**: on the test thread every client request is rooted at the handle's API
  root, which started with the handle, and CONFIRM places the hold for "writer before reader" there (ZB4).

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("zk-adhoc-02,zk-buggy-710")` on `checkSession`'s `SessionMovedException` (SessionTrackerImpl line 367) |
| the occurrence | `target_occurrence` in `case.sh` | `auto0/peer5#epoch0/region/REGION.3cfb4ed2-...#3`: the leader's forwarded Prep of the old connection's third request (create, w1, w2): w2, the second `SessionMoved` on the never-closed connection in the bug's world |
| scope | `case.sh` | zk-adhoc-02's: SessionTrackerImpl, LeaderSessionTracker, Leader, LearnerHandler, PrepRequestProcessor |
| no scope growth | `workflow.properties` | `causynth_scope_growth_budget=0`: with growth `ZooKeeperServer` became a region, G's `processConnectRequest` an unplanned region occurrence with no activation row, so the takeover's REVALIDATE write had no chain to a ROOT and `Arms.concurrent` refused it as an alternative writer (ZB2) |
| world depth | `case.sh` | `CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=2`, `CAUSYNTH_CAMPAIGN_MAX_CLAIMS=20`, CONFIRM order timeout 120 s |
| client fault cut | `case.sh` | `client_fault_transports=(ZK_QUORUM)` as zk-adhoc-02 |
| mechanism | `experiments/accept/report.py` | `zk-buggy-710`: `STATE_PAIRING_FLIPPED` |

Budget 21600 s (`zookeeper-buggy-cases.tsv`).

## Result: SAT (confirmed, reproduced 10/10 natively, control 0/10), the plain world

**On liftlab** (B1, `/bigtemp/vnr3ne/gc-out/buggy-detect/accept-B1-zk-buggy-710`): B1 (lead fills in).

The record below is CloudLab's (2026-10-26).
ZB6 (system/zookeeper-buggy-detect bba07d7d1, tree 4260614d, 361 s): EXPLORE stopped
WITNESSED after 4 rounds and 113 obligation verdicts (an admitted replay observed the fatal at the declared
occurrence); claim `SAT_CANDIDATE` `STATE_PAIRING_FLIPPED` at valuation 0, no root moved, `polarityDecides` true;
CONFIRMED ("every edge the model chose was taken, and the claim's anchor observed the fatal"); REPRODUCE 10 of 10
native runs (every order held, none unheld), control 0 of 10; report.py PASS; `round-verify.sh`: z3 sat on
`candidate.smt2`, end WITNESSED, 0 BOUNDED, 0 UNBOUND, 0 HOLD, 7 leaves, confirmed; no BLOCKING gap, no ORDER_UNHELD.

The chain (`candidate.smt2`, CONFIRM's expected edges, the selected session's rows): w2's `checkSession` reads
`SessionImpl.owner` twice (line 301, the null check; line 414, the compare). The model pairs both reads with
`SessionTrackerImpl.setOwner` (line 270) in the leader's LearnerHandler region (`Leader.revalidateSession`, version
629 in the selected session) -- the takeover's REVALIDATE, owner = G's LearnerHandler -- instead of the createSession's
`setOwner` (version 42, owner = F's LearnerHandler, which is also `request.getOwner()` for the forwarded w2);
`isClosing` stays the constructor's false. So `session.owner != owner` and `checkSession` throws
`SessionMovedException` at line 367, the point's own throw, in w2's occurrence. CONFIRM realized the order by holding
the leader's Prep at its claim of w2 (`CLAIM auto0/peer5#epoch0|Anchor:8be7d344...|<Leader.submitLearnerRequest>...`)
until the takeover's `setOwner` exited; the REVALIDATE runs on the LearnerHandler thread for G, not on Prep, so the
hold does not block it. Necessity: excluding the takeover's arm on every path of the exported formula makes it unsat.

**What it shows, and the caveat.** The confirmed witness is the plain world: in the native reproductions w1 completes
with an ordinary reply and w2 throws once (the run ends at the anchor). ZOOKEEPER-710's fix changes only what follows
a throw (the connection's teardown), so the fixed tree reaches this same occurrence: the fixed-tree control ZC2
(graphchecker/zk-bug-710-control c0488b9b = 92c0f2b5 + this workload and marker, the fix intact) ends the same way -- SAT_CANDIDATE, the same pairing, confirmed, reproduced
10/10, report.py PASS. "Two throws from one stale owner", the permanence the bug adds, is a relation between two
occurrences of the throw, which a single-occurrence target cannot express. So this case counts as SAT at the point's
own throw on the buggy tree with the bug's workload (the acceptance the hdfs-adhoc-11 buggy cases use), and the check
does not separate the buggy tree from the fixed one.

**How it got here** (every run, CloudLab 2026-10-26):

| run | GC / tree | result |
| --- | --- | --- |
| ZS1 | f117d1a16 / dfc0cee9 (v1) | SEED only: the target resolves (peer5's forwarded Prep, third old request) |
| ZB1 | aa0bfee3b / dfc0cee9 (v1) | stopped: as 2886's v1, the takeover was causally after the synchronous writes, nothing realizable |
| ZB2 | aa0bfee3b / 43ff1cb2 (v2) | FIXED_POINT 14 rounds / 372 verdicts, claims spurious, stopped: the takeover's REVALIDATE had no chain to a ROOT (scope growth), so COMPOSE never offered it; explored replays hit the fatal but were NOT_ADMITTED |
| ZB3 | b4af526ca / 43ff1cb2 | UNSAT_CLOSED (7 / 74): the takeover arm offered, but coupled to `isClosing` by the test's own closeSession |
| ZB4 | b4af526ca / 5da76416 (v3) | SAT_UNCONFIRMED (8 / 111): the intended pairing; CONFIRM's hold on the client's API root deferred nothing |
| ZB5 | b4af526ca / 4260614d (v4) | SAT_UNCONFIRMED (6 / 63): the hold on w2's thread start, still not applied (a client root is never entered) |
| ZC1 | b4af526ca / control c0488b9b | fixed tree, old engine: the same composed world, SAT_UNCONFIRMED the same way |
| **ZB6** | **bba07d7d1 / 4260614d (v4)** | **SAT, confirmed, 10/10, control 0/10, PASS** |
| ZC2 | bba07d7d1 / control c0488b9b | fixed tree: the same SAT, confirmed, 10/10, PASS (the caveat's evidence) |

The engine step (bba07d7d1; the independent review approved it unchanged, so ZB6 and ZC2 count):
`ConfirmMain.StateClosure.held()` placed the hold for "writer before reader" at the reader's submitter; when that send's
occurrence is uninstrumented (a client's API root, a test thread's start) the hold went on an activation the runtime
never enters, and the order was silently not held. It now walks the reader's own anchor-producer chain and holds at
the instrumented ITEM/HANDOFF_TASK claim nearest that send (here w2's Prep claim on the leader), under the existing
guards; where none qualifies the old hold stays and is reported (ORDER_UNHELD: CONFIRM's summary, EXPLORE's DIAGNOSTIC
gap rows). CONFIRM's checking is unchanged. The review recomputed every past CONFIRM plant of the CloudLab runs: only
F7-11741 and Z10 container-reuse have the affected shape, both with identical edges (container-reuse gains
ORDER_UNHELD notes only). Residual costs it named: a writer that waits on unrelated work queued behind the held claim
on a single-threaded worker (Prep) waits out the 300 s order timeout -- time, no outcome change; and a long hold
stalls later Prep requests, which could expire sessions (the automatic cluster's sessions never expire, `NEVER_MS`).

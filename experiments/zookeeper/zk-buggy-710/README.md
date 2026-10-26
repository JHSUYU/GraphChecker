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

`graphchecker/zk-bug-710` = gc/zk-cloudlab 92c0f2b5 (the tree every ZooKeeper check runs) plus:

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

## Result: SAT_UNCONFIRMED (the bug's world is composed; CONFIRM cannot realize its order)

Runs (snapshots `/bulk/gc-run/zb710-<n>`, GC_OUT `/bulk/gc-out/zk-buggy/710`, image
`/bulk/vm/zookeeper/j2sdk-image`):

| run | GC / tree | result |
| --- | --- | --- |
| ZS1 | f117d1a16 / dfc0cee9 (v1) | SEED only: the target resolves (peer5's forwarded Prep, third old request) |
| ZB1 | aa0bfee3b / dfc0cee9 (v1) | stopped; same claims as 2886's v1 (Request.owner read as null, refuted by ORDER; unminted Prep clocks) |
| ZB2 | aa0bfee3b / 43ff1cb2 (v2) | FIXED_POINT 14 rounds / 372 verdicts; claims spurious; stopped: COMPOSE never offered the takeover's REVALIDATE as a writer (no chain to a ROOT); explored replays did hit the fatal (observedFatal) but were NOT_ADMITTED |
| ZB3 | b4af526ca / 43ff1cb2 | UNSAT_CLOSED (FIXED_POINT 7 / 74): the takeover arm offered, but coupled to `isClosing` (the test's own closeSession): unsat by construction |
| ZB4 | b4af526ca / 5da76416 (v3) | **SAT_UNCONFIRMED** (FIXED_POINT 8 / 111): the intended pairing; CONFIRM's hold on the client's API root deferred nothing |
| ZB5 | b4af526ca / 4260614d (v4) | **SAT_UNCONFIRMED** (FIXED_POINT 6 / 63, 512 s): the intended pairing; the hold now on w2's thread start, still not applied |

ZB5's claim: `STATE_PAIRING_FLIPPED` at valuation 0, no root moved, `polarityDecides` true, z3 sat
(EXACT_REACHABLE), one repaired arm on the seed path. The chain, read off `candidate.smt2` and CONFIRM's
expected edges: the target's two reads of `SessionImpl.owner` (`checkSession` #301, the null check, and
#414, the compare; natively version 42, written by the createSession's `setOwner` = F) take the
takeover's REVALIDATE `SessionTrackerImpl.setOwner` (version 807, the LearnerHandler region on peer5:
`Leader.revalidateSession`) = G; `isClosing` stays the constructor's false; so `session.owner` (G) !=
`request.getOwner()` (F) and `checkSession` throws `SessionMovedException` at line 367 in w2's occurrence.
That is the world the bug lives in, at the point's own throw.

CONFIRM refuted it twice ("the run took an edge the model did not choose: the read observed
INSTANCE/7#40@42 written by the createSession"), each replay in about 37 s with no hold waiting: the order
"the takeover's `setOwner` exits before w2" was never applied. `ConfirmMain.held` puts that hold at the
reader's submitter (`Confirmation.submitter` walks the anchor producers: w2's Prep <- F's role occurrence
<- the old client's root). In ZB4 that was `auto0/client1#epoch0/region/ROLE.CLIENT/ctx:Root:CLIENT/test#1`
with an empty index (the handle's API root, running since the handle was made: nothing to defer); in ZB5
it is w2's own thread start. The runtime holds an activation only where an instrumented entry calls
`Confirmation.waited` -- a client root is no planned occurrence, so the hold is never applied and the
replay keeps the recorded order. Realizing this order needs CONFIRM to hold w2 where it is instrumented
(its Prep claim on the leader) when the submitter chain ends in a client root: engine support, not done
here (owner's rule: send the design to the lead first).

The witness, if confirmed, would be the plain world: w1 passes and w2 throws once (only w2's read is
re-paired). The fixed tree reaches that same occurrence: ZOOKEEPER-710's fix changes only what follows
a throw (the teardown), and "two throws from one stale owner" is a relation between two occurrences,
which a single-occurrence target cannot express. The fixed-tree control (graphchecker/zk-bug-710-control
c0488b9b = 92c0f2b5 + this workload, fix intact; run ZC1 under `/bulk/gc-out/zk-buggy/710ctl`) ends exactly as
the buggy tree: COMPOSE sat, the same `STATE_PAIRING_FLIPPED` world (w2's `SessionImpl.owner` reads paired with the
takeover's REVALIDATE `setOwner`, version 807), CONFIRM refuting it the same way -- SAT_UNCONFIRMED. The fixed tree
composes the same world at line 367.

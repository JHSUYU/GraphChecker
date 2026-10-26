# ZOOKEEPER-710 put back (zk-buggy-710, point zk-adhoc-02)

## The bug

[ZOOKEEPER-710](https://issues.apache.org/jira/browse/ZOOKEEPER-710) (fix
[b1c614b2](https://github.com/apache/zookeeper/commit/b1c614b2ca982b2e029d11605717846af790870f), 2010):
a permanent `SESSIONMOVED` error after a client reconnects. `session.owner` is the `LearnerHandler` of
the follower that most recently owns the session (`Leader.revalidateSession` calls
`zk.setOwner(id, learnerHandler)`, and every forwarded request carries `request.setOwner(learnerHandler)`;
`SessionTrackerImpl.checkSession(sessionId, request.getOwner())` compares them). A client renewing on a
slow follower F times out and reconnects to a fast follower/leader G, whose REVALIDATE sets
`session.owner = G`; F's late REVALIDATE then re-pairs `session.owner` back to F. The client's real
connection (G) sends a request, so `request.getOwner() = G != session.owner = F` and
`checkSession` throws `SessionMovedException` at (master) line 367. Because that `SessionMoved` was
returned to the client as an ordinary error, the connection was never torn down, so every later request on
it threw `SessionMoved` again: a permanent `SESSIONMOVED`.

Point zk-adhoc-02 (`docs/checks/ZOOKEEPER.md`, `zk-adhoc/checks.tsv`) is exactly that throw:
`SessionTrackerImpl.checkSession`'s `session.owner != owner` `SessionMovedException`.

The fix makes `FinalRequestProcessor.processServed` catch `SessionMovedException` and call
`cnxn.sendCloseSession()`, so the client disconnects, reconnects and revalidates and the permanence is
gone.

## What was put back, on graphchecker/zk-bug-710

The fork's branch is `graphchecker/zk-bug-710` (gc/zk-cloudlab 92c0f2b5, the tree every ZooKeeper check
runs) plus two commits:

- **The bug, by hand** (e3659a88, `ZOOKEEPER-710 put back: ...`): `FinalRequestProcessor.processServed` no
  longer catches `SessionMovedException` to call `cnxn.sendCloseSession()`. A non-multi `SessionMoved`
  thrown out of Prep (`checkSession`) is now caught by the generic `catch (KeeperException e) { err =
  e.code(); }` and returned as an ordinary `SESSIONMOVED` error, so the connection stays open and the
  session's next request throws `SessionMoved` again. Only the fix's catch block is removed; the
  `SessionMovedException` import stays (ZOOKEEPER-2886's code on this tree still uses it). The fix's own
  test changes (QuorumTest's `testSessionMoved*`, which assert the fixed `ConnectionLoss`) are left in the
  tree; they are not this case's workload and are not built or run by it.
- **The workload and the target** (dfc0cee9): `CausynthSessionMoved710Test`, and `zk-buggy-710` added to
  the `@CausynthExceptionTarget` on `checkSession`'s `SessionMovedException` throw (line 367), beside
  `zk-adhoc-02`.

## The workload

`org.apache.zookeeper.test.CausynthSessionMoved710Test#aMovedConnectionKeepsThrowing` (a `CausynthZk*` of
its own on `QuorumBase`, the five-peer ensemble zk-adhoc-02 uses; no existing test fits -- QuorumTest's
`testSessionMoved*` assert the fixed `ConnectionLoss` behaviour and would fail on the buggy tree). On the
all-servers ensemble:

1. The old client `zk` connects to a follower F (`(leader+1)%5`); `session.owner = F` on the leader.
2. `zk` creates `/sm710` (EPHEMERAL) and `setData`s it twice, each a forwarded write whose leader-side
   `checkSession` reads `session.owner = F` and passes.
3. A second handle `zknew` connects to another server G (`(leader+2)%5`) with the same session id and
   password; its REVALIDATE sets `session.owner = G` on the leader. `zk.dontReconnect()` keeps the old
   handle from re-establishing.
4. `zknew` writes once and both close. The test ends green.

The recording keeps every old-connection write ahead of G's REVALIDATE (program order: the writes run
before `zknew` is constructed), so each old-connection `checkSession` reads `session.owner = F` and no
`SessionMoved` is thrown natively. No order workaround is needed: a writer recorded after a read is a valid
re-pairing candidate (RULES, "no recorded-order pruning").

The witness is the world where GraphChecker re-pairs the two old-connection `setData` reads of
`session.owner` to G's late `setOwner`: the first `setData` throws `SessionMoved` at `checkSession` and,
because ZOOKEEPER-710 is put back, the connection stays open and the second `setData` throws there again --
the permanent `SESSIONMOVED`. The second throw is the target occurrence; on the fixed tree the first
throw's `sendCloseSession` would tear the connection down so the second request never reaches
`checkSession`.

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("zk-adhoc-02,zk-buggy-710")` on `checkSession`'s `SessionMovedException` throw (SessionTrackerImpl line 367) |
| the occurrence | `target_occurrence` in `case.sh` | the second old-connection `setData`'s `checkSession` (resolved off the SEED; see the run log below) |
| scope | `case.sh` | zk-adhoc-02's: SessionTrackerImpl, LeaderSessionTracker, Leader, LearnerHandler, PrepRequestProcessor |
| world depth | `case.sh` | `CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=2` (two re-pairings of `session.owner`: both old-connection reads to G's late setOwner); `CAUSYNTH_CAMPAIGN_MAX_CLAIMS=20` |
| client fault cut | `case.sh` | `client_fault_transports=(ZK_QUORUM)` as zk-adhoc-02: the mechanism is the owner re-pairing, so the client's ZOOKEEPER doors do not fail |
| mechanism | `experiments/accept/report.py` | `zk-buggy-710`: `STATE_PAIRING_FLIPPED` |

The run's budget is `zookeeper-buggy-cases.tsv`'s 21600 s.

## Result

(pending the campaign; filled with the verdict, the moved roots, the chain read by `smt-legend`, CONFIRM
and native REPRODUCE k/N with control 0/N.)

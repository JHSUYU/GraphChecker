# ZOOKEEPER-2886 put back (zk-buggy-2886, point zk-adhoc-02)

## The bug

[ZOOKEEPER-2886](https://issues.apache.org/jira/browse/ZOOKEEPER-2886) (fix
[b593a8de](https://github.com/apache/zookeeper/commit/b593a8de1cc48534661526685e39d812aa680d36),
[PR 353](https://github.com/apache/zookeeper/pull/353), 2018): the multi-only shape of ZOOKEEPER-710 --
a permanent `SESSIONMOVED` on a connection that issues only multi ops. The owner mechanism is the same as
ZOOKEEPER-710 (see `../zk-buggy-710/README.md`): after a session moves, a request forwarded from the old
connection reads `session.owner != request.getOwner()` and `SessionTrackerImpl.checkSession` throws
`SessionMovedException` at (master) line 367. For a multi, Prep records that as the sub-op's error, and
`FinalRequestProcessor` turned it into a per-op `ErrorResult` instead of throwing it, so ZOOKEEPER-710's
connection-teardown catch never ran for a multi. A multi-only client therefore kept getting `SESSIONMOVED`
from the server the leader no longer considered the owner.

Point zk-adhoc-02 is that same throw (`SessionTrackerImpl.checkSession`'s `SessionMovedException`).

The fix rethrows `SessionMovedException` ahead of the multi check, and throws it out of the multi branch
when a sub-result is `SESSIONMOVED`, so ZOOKEEPER-710's teardown closes the connection.

## What was put back, on graphchecker/zk-bug-2886

The fork's branch is `graphchecker/zk-bug-2886` (gc/zk-cloudlab 92c0f2b5) plus two commits:

- **The bug, by hand** (cf2651ae): `FinalRequestProcessor.processServed` no longer rethrows a
  `SessionMovedException` ahead of the multi check (`if (ke instanceof SessionMovedException) throw ke;`
  removed), and a multi sub-op's `SESSIONMOVED` error no longer throws `SessionMovedException` out of the
  multi branch. A multi's `SessionMoved` now stays an ordinary per-op `ErrorResult`, so ZOOKEEPER-710's
  teardown catch never runs for a multi and the connection stays open. ZOOKEEPER-710's own non-multi
  teardown catch stays in place on this tree (this bug is only about the multi path).
- **The workload and the target** (da71129a): `CausynthSessionMoved2886Test`, and `zk-buggy-2886` added to
  the `@CausynthExceptionTarget` on `checkSession`'s throw (line 367), beside `zk-adhoc-02`.

## The workload

`org.apache.zookeeper.test.CausynthSessionMoved2886Test#aMovedMultiOnlyConnectionKeepsThrowing`
(`QuorumBase`): identical in shape to zk-buggy-710's but the old connection issues only single-op `multi`
calls (create then two setData, each wrapped in a `multi`) while it owns the session; a second handle on
another server then takes the session over (late REVALIDATE `setOwner`). The recording keeps both multis
ahead of the REVALIDATE, so no `SessionMoved` fires natively. GraphChecker re-pairs the two multi setData
reads of `session.owner` to the late `setOwner`: the first multi throws `SessionMoved` at `checkSession`,
becomes a per-op `ErrorResult` (the connection stays open, the bug), and the second multi throws there
again -- the target.

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("zk-adhoc-02,zk-buggy-2886")` on `checkSession`'s throw (SessionTrackerImpl line 367) |
| the occurrence | `target_occurrence` in `case.sh` | the old connection's second multi setData at the leader (resolved off the SEED; see the run log) |
| scope | `case.sh` | zk-adhoc-02's: SessionTrackerImpl, LeaderSessionTracker, Leader, LearnerHandler, PrepRequestProcessor |
| world depth | `case.sh` | `CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=2`; `CAUSYNTH_CAMPAIGN_MAX_CLAIMS=20` |
| client fault cut | `case.sh` | `client_fault_transports=(ZK_QUORUM)` as zk-adhoc-02 |
| mechanism | `experiments/accept/report.py` | `zk-buggy-2886`: `STATE_PAIRING_FLIPPED` |

The run's budget is `zookeeper-buggy-cases.tsv`'s 21600 s.

## Result

(pending the campaign; filled with the verdict, moved roots, the chain, CONFIRM and native REPRODUCE.)

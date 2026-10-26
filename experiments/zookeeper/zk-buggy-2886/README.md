# ZOOKEEPER-2886 put back (zk-buggy-2886, point zk-adhoc-02)

## The bug

[ZOOKEEPER-2886](https://issues.apache.org/jira/browse/ZOOKEEPER-2886) (fix
[b593a8de](https://github.com/apache/zookeeper/commit/b593a8de1cc48534661526685e39d812aa680d36),
[PR 353](https://github.com/apache/zookeeper/pull/353), 2018): the multi-only shape of ZOOKEEPER-710
(`../zk-buggy-710/README.md`). Inside a multi, the owner check's `SessionMovedException`
(`SessionTrackerImpl.checkSession`, master line 367) became a per-op `ErrorResult` in
`FinalRequestProcessor`, so ZOOKEEPER-710's connection teardown never ran for a multi and a multi-only
client kept getting `SESSIONMOVED`. The fix rethrows `SessionMovedException` ahead of the multi check and
out of the multi branch when a sub-result is `SESSIONMOVED`. Point zk-adhoc-02 is that same throw.

## What was put back, on graphchecker/zk-bug-2886

`graphchecker/zk-bug-2886` = gc/zk-cloudlab 92c0f2b5 plus:

- **The bug, by hand** (cf2651ae): `FinalRequestProcessor.processServed` no longer rethrows a
  `SessionMovedException` ahead of the multi check, and a multi sub-op's `SESSIONMOVED` no longer throws out
  of the multi branch; a multi's `SessionMoved` stays an ordinary per-op `ErrorResult` and the connection
  stays open. ZOOKEEPER-710's non-multi teardown stays on this tree.
- **The workload and the target** (da71129a, then b7515c14, 3dd47e98, b8b7149f):
  `CausynthSessionMoved2886Test`, and `zk-buggy-2886` beside `zk-adhoc-02` on line 367's marker.

## The workload

`org.apache.zookeeper.test.CausynthSessionMoved2886Test#aMovedMultiOnlyConnectionKeepsThrowing`:
zk-buggy-710's workload with every old-connection operation a single-op `multi` (create, then two
setData). The same three workarounds, for the same reasons (710's README): the takeover thread's 5 s delay
with no happens-before from the old multis; no close at the end (an in-window `closeSession` is a second
`isClosing` writer, coupled by COMPOSE's per-writer arm); the second setData multi, the target, on a thread
of its own. Natively no `SessionMoved` fires (passes on the buggy and the fixed tree).

## What this case declares

As zk-buggy-710: marker `@CausynthExceptionTarget("zk-adhoc-02,zk-buggy-2886")` (line 367); target
`auto0/peer5#epoch0/region/REGION.3cfb4ed2-...#3` (the old connection's third multi, the second setData);
zk-adhoc-02's scope; `causynth_scope_growth_budget=0`; world depth 2, 20 claims, 120 s CONFIRM order
timeout; `client_fault_transports=(ZK_QUORUM)`; report.py `STATE_PAIRING_FLIPPED`. Budget 21600 s.

## Result: SAT_UNCONFIRMED (as zk-buggy-710)

Runs (snapshots `/bulk/gc-run/zb2886-<n>`, GC_OUT `/bulk/gc-out/zk-buggy/2886`):

| run | GC / tree | result |
| --- | --- | --- |
| ZB1 | 5488f8701 / da71129a (v1) | FIXED_POINT 8 rounds / 315 verdicts; claim 0000 (the target's `Request.owner` read as null) refuted by ORDER (LearnerHandler sets it before submitting: zk-adhoc-02's false positive), 0001-0004 NOT_ADMITTED on an unminted Prep clock (`pRequestHelper#u91`); stopped (lead) |
| ZB2 | 5488f8701 / b7515c14 (v2) | stopped after its first claim (the same null-owner world); cause as zk-buggy-710's ZB2 |
| ZB3 | b4af526ca / b7515c14 | UNSAT_CLOSED (FIXED_POINT 6 / 74): the per-writer arm coupling (`isClosing` from the test's own closeSession) |
| ZB4 | b4af526ca / 3dd47e98 (v3) | **SAT_UNCONFIRMED** (FIXED_POINT 7 / 64): the intended pairing, CONFIRM's hold on the client's API root |
| ZB5 | b4af526ca / b8b7149f (v4) | **SAT_UNCONFIRMED** (FIXED_POINT 9 / 110, 508 s): the intended pairing, the hold on the target thread's start, not applied |

ZB5's claim: `STATE_PAIRING_FLIPPED` at valuation 0, no root moved, `polarityDecides` true, z3 sat: the target's
two `SessionImpl.owner` reads (natively version 42, the createSession's F) take the takeover's REVALIDATE
`setOwner` (version 863) = G, so `checkSession` throws `SessionMovedException` at line 367 in the second setData
multi. CONFIRM refuted it twice (the read observed version 42; no hold waited), for the reason zk-buggy-710's
README gives: the hold for "the takeover's `setOwner` before the target" lands on a client-rooted activation the
runtime never holds. The same caveat holds: a confirmed witness would be the plain world (the first multi passes,
the second throws once), which the fixed tree reaches too; the fix changes only the teardown after a throw.

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

`graphchecker/zk-bug-2886` = the fork commit 92c0f2b5 (as zk-buggy-710's) plus:

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

## Result: SAT (confirmed, reproduced 10/10 natively, control 0/10), the plain world

**On liftlab** (B1, `/bigtemp/vnr3ne/gc-out/buggy-detect/accept-B1-zk-buggy-2886`): B1: SAT, CONFIRM, native 10/10, control 0/10, report.py PASS, 294 s (B1-zk-buggy-2886).

The record below is CloudLab's (2026-10-26). ZB6 (system/zookeeper-buggy-detect bba07d7d1, tree b8b7149f, 363 s):
EXPLORE stopped WITNESSED after 5 rounds and 101 obligation
verdicts; claim `SAT_CANDIDATE` `STATE_PAIRING_FLIPPED` at valuation 0, no root moved, `polarityDecides` true; CONFIRMED
("every edge the model chose was taken, and the claim's anchor observed the fatal"); REPRODUCE 10 of 10 native runs
(every order held), control 0 of 10; report.py PASS; `round-verify.sh`: z3 sat, end WITNESSED, 0 BOUNDED, 0 UNBOUND,
0 HOLD, 4 leaves, confirmed; no BLOCKING gap, no ORDER_UNHELD.

The chain, as zk-buggy-710's: the second setData multi's `checkSession` reads of `SessionImpl.owner` (lines 301 and
414) are paired with the takeover's REVALIDATE `setOwner` (the leader's LearnerHandler region, version 666) instead of
the createSession's (version 42, the request's own owner F), so `checkSession` throws `SessionMovedException` at line
367 in that multi's occurrence. CONFIRM held the leader's Prep at its claim of the multi
(`CLAIM auto0/peer5#epoch0|Anchor:d1b3ac4c...`) until the takeover's `setOwner` exited. Necessity: excluding the
takeover's arm on every path of the exported formula makes it unsat.

**The caveat** (as zk-buggy-710's): the witness is the plain world -- in the native reproductions the first setData
multi completes with an ordinary reply and the second throws once. ZOOKEEPER-2886's fix (rethrow a multi's
`SessionMoved` so 710's teardown runs) changes only what follows a throw, so the fixed tree reaches the same occurrence;
"two throws from one stale owner" is a relation between two occurrences, which a single-occurrence target cannot
express. Evidence: zk-buggy-710's fixed-tree controls ZC1 (old engine: the same composed world) and ZC2 (SAT, confirmed,
10/10), and this case's own fixed-tree control (below).

| run | GC / tree | result |
| --- | --- | --- |
| ZB1 | 5488f8701 / da71129a (v1) | FIXED_POINT 8 rounds / 315 verdicts; claim 0000 (`Request.owner` read as null) refuted by ORDER, 0001-0004 NOT_ADMITTED on an unminted Prep clock; stopped |
| ZB2 | 5488f8701 / b7515c14 (v2) | stopped after its first claim (the same null-owner world) |
| ZB3 | b4af526ca / b7515c14 | UNSAT_CLOSED (6 / 74): the per-writer arm coupling (`isClosing` from the test's own closeSession) |
| ZB4 | b4af526ca / 3dd47e98 (v3) | SAT_UNCONFIRMED (7 / 64): the intended pairing, CONFIRM's hold on the client's API root |
| ZB5 | b4af526ca / b8b7149f (v4) | SAT_UNCONFIRMED (9 / 110): the hold on the target thread's start, not applied |
| **ZB6** | **bba07d7d1 / b8b7149f (v4)** | **SAT, confirmed, 10/10, control 0/10, PASS** |
| ZC1 | bba07d7d1 / control 328765d1 | fixed tree (graphchecker/zk-bug-2886-control = 92c0f2b5 + this workload and marker, the fix intact): the same SAT -- WITNESSED (5 / 111), confirmed, reproduced 10/10, report.py PASS: the caveat's direct evidence |

The engine step bba07d7d1 (CONFIRM holds the reader at the nearest instrumented claim on its chain when its submitter
is an uninstrumented root; reviewed and approved unchanged) and its residual notes are in zk-buggy-710's README.

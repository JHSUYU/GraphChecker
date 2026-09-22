# HDFS-17899

## The bug

[HDFS-17899](https://issues.apache.org/jira/browse/HDFS-17899). A stale data-encryption key
reaches `BlockTokenSecretManager.retrieveDataEncryptionKey` on a DataNode after a key-refresh
RPC has failed. The consumer of the key — Balancer, SPS or a source DataNode — keeps using
the key it holds; the DataNode that has to verify it has already rotated. The three cases
share that one target and differ only in which request flow carries the key to it. The
workloads model the refresh RPC failure with a `Debug.makeSymbolicBoolean` marker in
`org.apache.hadoop.ipc.Client`, so a witness here can be the marker moving, the clocks
disagreeing, or both.

| Case | Request flow | Hadoop worktree | Branch |
| --- | --- | --- | --- |
| `bug1` | NameNode -> Balancer -> DataNode | `/u/vnr3ne/hadoop-hdfs-17899-bug1` | `gc/hdfs-17899-bug1` |
| `bug2` | NameNode -> SPS -> DataNode | `/u/vnr3ne/hadoop-hdfs-17899-bug2` | `gc/hdfs-17899-bug2` |
| `bug3` | NameNode -> source DataNode -> target DataNode | `/u/vnr3ne/hadoop-hdfs-17899-bug3` | `gc/hdfs-17899-bug3` |

## The workloads

All three are bespoke tests, and each drives the mechanism **two links from the root**. An
occurrence IS its causal address and an `ANCHOR` context digests the producer endpoint, which
digests an occurrence, so a long chain has to reproduce byte for byte between the planning
pass and the replay.

| Case | Test | Shape |
| --- | --- | --- |
| `bug1` | `TestCausynthBalancerCachedKey` (`…server.balancer`) | three DataNodes; the mover is the test, holding a real `KeyManager`. It takes the NameNode's keys over the recorded RPC, caches its one `DataEncryptionKey` while the master's current key is still the pinned one, and then sends one REPLACE_BLOCK the way `Dispatcher.PendingMove.dispatch` does |
| `bug2` | `TestExternalStoragePolicySatisfier#testCausynthSpsKeyRefreshRpcFailure` | the SPS asks one DataNode once |
| `bug3` | `TestCausynthDataTransferRpcFailure` | one replication, one target DataNode read |

`bug1` used to be driven by `TestBalancerWithEncryptedTransfer#testEncryptedBalancer1`. That
chain is seventeen links deep and only its root survived into a replay, so the plan and the
replay minted different anchors for the same exchange and every path was refused on identity
(`OCCURRENCE_ANCHOR_UNMATCHED`) — never on the mechanism. Nothing about the defect is given
up by the rewrite: the cached `DataEncryptionKey` in `KeyManager` IS the defect, and the
balancer's block-selection machinery, which no part of the mechanism touches, is what is left
out. `Balancer` and `Dispatcher` are correspondingly out of the analysis scope.

Every workload has to leave a **rotation gap running the right way**: the key the failing
party puts on the wire is serials BEHIND the master's current one, while the consumer still
RETAINS it, so the recording stays healthy and a witness has to buy the expiry with a clock
move or with the marker. With a zero gap every composed path is either self-contradictory
(bug3 measured 63 paths, all unsat with every root free) or satisfied at the recorded
valuation (bug2, `FORMULA_SAT_AT_RECORDED_VALUATION`). Each workload asserts the gap
itself.

## What these cases declare

`workflow.properties`, `symbolic-inputs.jsonl`, `root-domains.jsonl` and
`communication-mappings.jsonl` are shared by all three; `case.sh` carries what is per case.

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | `@CausynthExceptionTarget` in each Hadoop checkout; `target.yaml` | `exception_target_id: hdfs-17899` |
| the occurrence | `target_occurrence` in `case.sh`, exported as `CAUSYNTH_TARGET_OCCURRENCE` | `bug1` `hdfs-17899/target-dn#epoch0/…@hdfs-17899/balancer#epoch0/balance-block#1`; `bug2` `…/target-dn#epoch0/…@hdfs-17899/sps#epoch0/satisfy-storage-policy#1`; `bug3` `…/target-dn#epoch0/…@hdfs-17899/source-dn#epoch0/replicate-block#1`. Left empty, the run keeps every observed occurrence |
| clock roots | `symbolic-inputs.jsonl`, two rows | per-method clock cells, not callee-level ones: `BlockTokenSecretManager.updateKeys()` and `.addKeys(ExportedBlockKeys,boolean)`, each declaring the cell `<org.apache.hadoop.util.Timer: long now()>.return` with `"clock": true`. Those two methods are therefore also region roots by declaration |
| marker root | the Hadoop worktrees, not this directory | `Debug.makeSymbolicBoolean("hadoopIpcRequestFails")` in `org.apache.hadoop.ipc.Client` models the key-refresh RPC failure. It is minted on every path through the send, not only when the outbound context happens to be active: Java's `&&` short-circuits, so a replay reaching the send with no active context materialized no marker at all and the `MARKER_FLIPPED` witness could never be asked for. Only the mint is unconditional; the throw still needs an active context |
| hook-minted roots | the Hadoop checkouts | `CausynthSymbolicSource.symbolize("HDFS.BLOCK_KEY.SERIAL_NO", …)` roots the counter each new `BlockKey` takes its id from; `…("HDFS.BLOCK_KEY.EXPIRY_DATE", …)` roots the inherited `DelegationKey#expiryDate`. A hook site owns its field (`CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED`), so neither is listed in `symbolic-inputs.jsonl` |
| root domains | `root-domains.jsonl`, one row | `HDFS.BLOCK_KEY.SERIAL_NO`, `declaredDomainMin "+0"`, `declaredDomainMax "+3"`: the recorded value and up to three rotations past it, relative because the serial starts at a `SecureRandom` int and increments once per roll. A root with no row is pinned to its recording; a clock has a floor of zero and no window |
| wire mappings | `communication-mappings.jsonl`, four `WIRE_FLOW` rows | `block-key-id`, `block-key-expiry-date`, `data-encryption-key-id` and `namenode-data-encryption-key-id`, each with an exact producer and consumer capture (`CALL_ARGUMENT`, `CALL_RETURN`, `METHOD_PARAMETER`). Declared ports are tracked and mint nothing: the attach installs the producer's own propagated expression at the consumer |
| loop bounds | `loop-bounds.jsonl` (five rows) for `bug1`/`bug2`, `loop-bounds-datanode.jsonl` (four rows) for `bug3`, every row at `loopBodyBound: 8`; `causynth_loop_default_bound=8` | `case.sh` selects the file and `run.sh` exports it as `CAUSYNTH_LOOP_BOUNDS` |

## Build and run

Each case has its own Hadoop worktree, so its source changes and compiled classes stay
independent, and each replay loads that checkout's common, client and HDFS classes. From
this directory, replacing `bug1` as needed:

```bash
../lib/run.sh . bug1 build      # installs the current GraphChecker API, builds that checkout,
                         # runs the concrete workload test, refuses unless it alone passes
../lib/run.sh . bug1 validate
../lib/run.sh . bug1 campaign
```

`lib/run.sh` sets a per-case `CAUSYNTH_OUTPUT_DIR` and `CAUSYNTH_CACHE_DIR`; override
`CAUSYNTH_OUTPUT_DIR` with a fresh directory per campaign. Each workload opens its recording
boundary only after its stable node and application sources and aliases are registered. The
in-tree acceptance harness (`experiments/hadoop/accept/README.md`) runs campaign, z3 probe
and report together, one case at a time:

```bash
export CAUSYNTH_CUSTOM_JDK_HOME=/absolute/path/to/j2sdk-image
CASES="hdfs-17899-bug1 hdfs-17899-bug2 hdfs-17899-bug3" bash experiments/hadoop/accept/accept.sh
```

## What the harness expects

`report.py` passes each of the three on `claim` `SAT_CANDIDATE`, `finalStatus`
`FINAL_READY`, empty `blockers` and no open BLOCKING gap, `polarityDecides` true,
`valuationOrdinal` >= 1, non-empty `movedRoots`, and a `findingKind` of `MARKER_FLIPPED` or
`CLOCK_SKEW`.

## Status

`bug2` and `bug3` pass: `CLOCK_SKEW`, `polarityDecides` true, `FINAL_READY`, no blocking gap,
`.smt` at 838 KB and 773 KB respectively. Two root causes had to be fixed first and they
explain both earlier failures: the cases declared **no clocks**, which made `CLOCK_SKEW`
unreachable by construction and key expiry inexpressible at all; and both recordings had a
**zero rotation gap**. `bug1` is the rewritten workload above.

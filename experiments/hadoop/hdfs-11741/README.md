# HDFS-11741

## The bug

[HDFS-11741](https://issues.apache.org/jira/browse/HDFS-11741). The Balancer caches a
`DataEncryptionKey` and does not check its expiry before reusing it. The workload keeps that
original behaviour: the Balancer caches a key, the NameNode performs two ordinary block-key
rotations, the DataNodes refresh through the block-key RPC, and the DataNode the Balancer
then talks to can no longer find the key id the Balancer presents. The target is that lookup
miss on the DataNode. Whether it happens is a disagreement between two nodes about which key
set is current — an expiry decided against one node's clock while another node's key map has
already moved on — so the witness needs two clock-driven flips on two nodes, recorded
separately and joined in the SMT. There is no Boolean fault marker anywhere in this
workload, so nothing but the declared clock and the block-key serial can open the target arm.

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | `@CausynthExceptionTarget` in the Hadoop checkout; `target.yaml` | `exception_target_id: hdfs-11741` |
| the occurrence | `declared_target_occurrence` in `workflow.properties` | `hdfs-11741/dn1#epoch0/region/REGION.53092d3e-263d-3a18-b7a5-ae5b437d96de@hdfs-11741/balancer#epoch0/balance-block#1` — the campaign is target-directed, and both DataNodes answer `balance-block#1`, so the family and k alone would name two |
| clock roots | `symbolic-inputs.jsonl`, three callee-level rows | `<org.apache.hadoop.util.Timer: long now()>`, `<org.apache.hadoop.util.Time: long now()>` and `<org.apache.hadoop.util.Time: long monotonicNow()>`, each `"kind": "CLOCK"`. A callee-level declaration makes *every* call site of that clock a root, wherever in the application scope it is called |
| declared region roots | `symbolic-inputs.jsonl`, three method rows | `BlockTokenSecretManager.updateKeys()`, `.addKeys(ExportedBlockKeys,boolean)` and `.removeExpiredKeys()`. A declared method is a region root by declaration, whether or not the backward slice reaches it — `removeExpiredKeys` reads the clock, decides an expiry and removes nothing in a healthy run, so no demand-directed walk over recorded flows would ever reach it |
| hook-minted roots | the Hadoop checkout, not this directory | `CausynthSymbolicSource.symbolize("HDFS.BLOCK_KEY.SERIAL_NO", …)` in `BlockTokenSecretManager.updateKeys` roots the counter each new `BlockKey` takes its id from, and `…("HDFS.BLOCK_KEY.EXPIRY_DATE", …)` roots the inherited `DelegationKey#expiryDate`. A hook site owns its field (`CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED`), which is why neither field is listed in `symbolic-inputs.jsonl` |
| root domains | `root-domains.jsonl`, one row | `HDFS.BLOCK_KEY.SERIAL_NO`, `declaredDomainMin "+0"`, `declaredDomainMax "+3"`: the recorded value and up to three rotations past it. Relative, because the serial starts at a `SecureRandom` int and increments by one per roll, so an absolute range would state something about one recording. A root with no row is pinned to its recording; a clock has a floor of zero and no window |
| wire mappings | `communication-mappings.jsonl`, three `WIRE_FLOW` rows | `block-key-id` and `block-key-expiry-date` (`CALL_ARGUMENT` into the `BlockKeyProto` builder, `CALL_RETURN` out of the proto getter) and `data-encryption-key-id` (`CALL_ARGUMENT` at the SASL client, `METHOD_PARAMETER` 0 of `retrieveDataEncryptionKey`). Declared ports are tracked and mint nothing: the consumer gets the producer's own propagated expression |
| loop bounds | `loop-bounds.jsonl`: three rows at `loopBodyBound: 8`; `causynth_loop_default_bound=8` | the expiry scan, the block-key reply conversion and the Balancer's key-updater loop. The file's header says which key-plumbing loops are deliberately left undeclared, and why |

## Build and run

Hadoop checkout `/opt/hadoop-hdfs-11741`, branch `gc/hdfs-11741-current`. From this
directory:

```bash
./run.sh build        # installs the current GraphChecker API, builds the tree,
                      # runs the concrete workload test, refuses unless it alone passes
./run.sh validate
./run.sh campaign
```

Use a fresh `CAUSYNTH_OUTPUT_DIR` per campaign. The recording opens only after the workload
has registered its stable node sources and aliases, so cluster startup creates no
unregistered regions. The in-tree acceptance harness
(`experiments/hadoop/accept/README.md`) runs campaign, z3 probe and report together:

```bash
export CAUSYNTH_CUSTOM_JDK_HOME=/absolute/path/to/j2sdk-image
CASES=hdfs-11741 bash experiments/hadoop/accept/accept.sh
```

## What the harness expects

`report.py` passes this case on `claim` `SAT_CANDIDATE`, `finalStatus` `FINAL_READY`, empty
`blockers` and no open BLOCKING gap, `polarityDecides` true, `valuationOrdinal` >= 1,
non-empty `movedRoots`, and a `findingKind` of `CLOCK_SKEW` or `MARKER_FLIPPED` — either the
clocks disagreed, or the serial moved inside its declared domain.

## Status

Exercised end to end: the seed passes the `IMPORT` gate, the closure reaches the DataNode's
key map through the declared wire ports and that map's static write sites, and exploration
converges. It is at its last round, pending the acceptance campaign, and has **not** yet
published an accepted claim. No artifacts are committed for this case.

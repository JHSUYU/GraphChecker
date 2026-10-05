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
| the failure | `target.yaml` | `exception_target: hdfs-11741 …BlockTokenSecretManager 586`: the `throw new` at that line of `retrieveDataEncryptionKey` |
| the occurrence | `declared_target_occurrence` in `workflow.properties` | `hdfs-11741/dn1#epoch0/region/REGION.7c569c3f-b4d3-305a-bd9c-bebff1048122@hdfs-11741/balancer#epoch0/balance-block#1` — the DataNode SASL handler occurrence (`SaslDataTransferServer$SaslServerCallbackHandler.handle`) that reaches the target lookup. It, not `retrieveDataEncryptionKey`'s own region (`REGION.53092d3e-…`), is the occurrence: a declared region entered inside a running occurrence opens none of its own, and every entry of `retrieveDataEncryptionKey` on the recording is nested in this handler. The campaign is target-directed, and both DataNodes answer `balance-block#1`, so the family and k alone would name two |
| clock roots | the program text (`causynth/RootCatalog`) | every read the slice reaches of a clock -- a JVM clock or a method returning one under constant arithmetic (`Timer.now()`, `Time.now()`, `Time.monotonicNow()`) -- is a root, and the occurrence that reads it is admitted as a root reader |
| hook-minted roots | the Hadoop checkout, not this directory | `CausynthSymbolicSource.symbolize("HDFS.BLOCK_KEY.SERIAL_NO", …)` in `BlockTokenSecretManager.updateKeys` roots the counter each new `BlockKey` takes its id from, and `…("HDFS.BLOCK_KEY.EXPIRY_DATE", …)` roots the inherited `DelegationKey#expiryDate`. A hook site owns its field (`CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED`), which is why neither field is listed in `symbolic-inputs.jsonl` |
| root domains | `root-domains.jsonl`, **no rows** | The file is empty, and deliberately: a root with no row is pinned to its recording, so **`HDFS.BLOCK_KEY.SERIAL_NO` is pinned to the value the recording minted**. Its `+0..+3` window was removed on 2026-09-20, on the case owner's 2026-09-15 ruling that varying the serial cannot open this anchor: the key id `G` the Balancer presents was minted *before* the recording window and is a constant of this run, so no rotation of the serial changes which key id the DataNode is asked to look up. The mechanism this case is about is the two clocks, not the counter. The window only added three valuations that decide nothing, and in the live run its one effect was to let arms produced under a refused obligation's world (`SERIAL_NO=182910`) be selected, mislabelling a two-clock witness as `MARKER_FLIPPED`. The file stays EMPTY rather than carrying a `#` note, because `contract/RootDomain.declared` reads it through `RowCodec.readJsonl`, which parses every non-blank line as JSON. A clock has a floor of zero and no window, and is never declared here |
| wire mappings | `../communication-mappings.jsonl` (every HDFS case's one declaration), four `WIRE_FLOW` rows | `block-key-id`, `block-key-expiry-date`, `namenode-data-encryption-key-id` (`CALL_ARGUMENT` into the proto builder, `CALL_RETURN` out of the proto getter) and `data-encryption-key-id` (`CALL_ARGUMENT` at the SASL client, `METHOD_PARAMETER` 0 of `retrieveDataEncryptionKey`: the key id travels inside the SASL user name, where no automatic port sees it). Declared ports are tracked and mint nothing: the consumer gets the producer's own propagated expression |
| loop bounds | `loop-bounds.jsonl`: three rows at `loopBodyBound: 8`; `causynth_loop_default_bound=8` | the expiry scan, the block-key reply conversion and the Balancer's key-updater loop. The file's header says which key-plumbing loops are deliberately left undeclared, and why |

## Build and run

Hadoop checkout `/bigtemp/vnr3ne/wt/hadoop-hdfs-11741-r5`, branch `gc/hdfs-11741-r5` (Maven repo `/bigtemp/vnr3ne/m2/hdfs-11741-r5`). From this
directory:

```bash
../../lib/run.sh . "" build        # installs the current GraphChecker API, builds the tree,
                      # runs the concrete workload test, refuses unless it alone passes
../../lib/run.sh . "" validate
../../lib/run.sh . "" campaign
```

Use a fresh `CAUSYNTH_OUTPUT_DIR` per campaign. The recording opens only after the workload
has registered its stable node sources and aliases, so cluster startup creates no
unregistered regions. The in-tree acceptance harness
(`experiments/accept/README.md`) runs campaign, z3 probe and report together:

```bash
export CAUSYNTH_CUSTOM_JDK_HOME=/absolute/path/to/j2sdk-image
CASES=hdfs-11741 bash experiments/accept/accept.sh
```

## What the harness expects

`report.py` passes this case on `claim` `SAT_CANDIDATE`, `finalStatus` `FINAL_READY`, empty
`blockers` and no open BLOCKING gap, `polarityDecides` true, non-empty `movedRoots`, and a
`findingKind` of `CLOCK_SKEW` or `MARKER_FLIPPED`. The expected finding is `CLOCK_SKEW` at
`valuationOrdinal` 0: the case declares no windowed root, so the recorded valuation is the only
one, and the witness is the clock cells the model had to move (the NameNode's second rotation
and the DataNode's refresh); `polarityDecides` there means pinning every clock cell to what the
recording read makes the query unsat.

## Status

Exercised end to end: the seed passes the `IMPORT` gate, the closure reaches the DataNode's
key map through the declared wire ports and that map's static write sites, and exploration
converges. It is at its last round, pending the acceptance campaign, and has **not** yet
published an accepted claim. No artifacts are committed for this case.

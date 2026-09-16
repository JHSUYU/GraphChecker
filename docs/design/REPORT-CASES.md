# REPORT-CASES — the six cases' configuration against the refactored pipeline

Read-only, staging `e507f365c`. No file edited. Every "REFUSED/ACCEPTED" below
is measured, not reasoned: `parseSelector` was compiled out of the tree at this
commit and run against the five declarations (probe in
`$SPN/cases-probe`).

**Two blockers, one silent budget, one missing port.**

| # | finding | cases | severity |
|---|---|---|---|
| **B1** | **17960 declares no anchor → `ComposeMain` refuses to start** | 17960 | **blocker** |
| **B2** | **the NN→sender DEK-id port is not declared** | 11741, bug1, bug2, bug3 | **blocker for the closure** |
| **S1** | `reach_max_valuations=128` is an unknown key, silently dropped; `compose_max_valuations` (default **16**) is what runs | all six | silent |
| **S2** | 17960 has no `clock_skew_ms` → default 300 000 ms, not `unbounded` | 17960 | benign today |
| **N1** | bug2/bug3's only MARKER roots are undeclared region inputs | bug2, bug3 (bug1 unmeasured) | decide |
| **N2** | `consumerField` is read by nothing in `src/main` | 17897, 17899 | inert |

Clean: every declared selector parses and round-trips (§1), `root-domains.jsonl`
is exactly the policy (§2), loop-bounds are all referenced (§5), and the dropped
block-key-array port is gone from every case file (§4).

---

## 1. Selectors — all five parse, all five name the right instance

`OccurrenceAddress.parseSelector` compiled from `e507f365c` and run on the five
declarations. All five **accepted**, and `Selector.render()` reproduces the
declaration byte-for-byte in every case:

| case | declared at | node | region | api | k | parse |
|---|---|---|---|---|---|---|
| 11741 | `workflow.properties:38` | `hdfs-11741/dn0#epoch0` | `REGION.53092d3e…` | `hdfs-11741/balancer#epoch0/balance-block` | 1 | **OK**, round-trips |
| 17897 | `workflow.properties:46` | `hdfs-17897/dn0#epoch0` | `REGION.53092d3e…` | `hdfs-17897/client#epoch0/striped-file-checksum` | 1 | **OK**, round-trips |
| bug1 | `case.sh:20` | `hdfs-17899/dn1#epoch0` | `REGION.53092d3e…` | `hdfs-17899/balancer#epoch0/balance-block` | 1 | **OK**, round-trips |
| bug2 | `case.sh:27` | `hdfs-17899/target-dn#epoch0` | `REGION.53092d3e…` | `hdfs-17899/sps#epoch0/satisfy-storage-policy` | 1 | **OK**, round-trips |
| bug3 | `case.sh:35` | `hdfs-17899/target-dn#epoch0` | `REGION.53092d3e…` | `hdfs-17899/source-dn#epoch0/replicate-block` | 1 | **OK**, round-trips |
| **17960** | **nowhere** | — | — | — | — | **n/a — see B1** |

Each names the instance REFACTOR-D3 §0 names: 11741 dn0, 17897 dn0 (striped
checksum), bug1 **dn1** (balancer first hop), bug2/bug3 target-dn. The bug1 =
dn1 / 11741 = dn0 split is the right way round — REPORT-B1D measured that on
bug1 it is dn1's activations that carry a request scope and dn0's that do not,
while lane11741j resolved dn0 with its family intact.

Two things the audit should record even though nothing needs changing:

- **The producer half of the `@…` segment is not verified.**
  `SelectorResolution.apiOf` compares the declaration's api to the anchor's
  `rpcSite` **on the last path segment only** (`sameApi` → `tail`). So
  `…@hdfs-11741/balancer#epoch0/balance-block` matches any anchor whose site
  ends `balance-block`, whatever component produced it. dn0-vs-dn1 is still
  decided, because `Selector.node()` is checked — but a declaration that named
  the wrong *producer* would resolve silently. Worth one line in CONTRACT-SPEC
  rather than a code change: the node is load-bearing, the producer prefix is
  documentation.
- **Region ids are recorded, not derived from these files.** All five name
  `REGION.53092d3e-263d-3a18-b7a5-ae5b437d96de`, which is what the round-2
  corpora carry for `retrieveDataEncryptionKey`. If M2's re-recording changes
  region derivation these five strings all go stale at once, and the failure
  mode is `ADMISSION_GAP`/"that region ran there not at all". Re-checking them
  against the first re-recorded seed session is a gate on M2, not an edit now.

### B1 — 17960 declares no anchor, and COMPOSE requires one

`experiments/hadoop/hdfs-17960/workflow.properties` has no
`declared_target_occurrence`, and `hdfs-17960/run.sh` exports no
`CAUSYNTH_TARGET_OCCURRENCE`. Then:

- `run_engine.sh:587-590` (`do_compose`) adds `--anchor` **only** when
  `declared_target_occurrence` is non-empty;
- `ComposeMain:534-537` — `"--anchor (or --target-occurrence) is required: the
  declared occurrence is the anchor"`.

So on the refactored pipeline 17960 dies at COMPOSE. EXPLORE survives, because
`run_engine.sh:2001` always passes `--task-plan …/execution_task_plan.jsonl`
and `ExploreMain.selectors` falls back to its `occurrenceId` rows (already
resolved addresses, which `SelectorResolution.resolve` accepts via the `/ctx:`
branch) — but that only moves the failure one stage later.

This is the case that currently PASSES, so it is the one regression this audit
found that is certain rather than probable.

**Edit** — `experiments/hadoop/hdfs-17960/workflow.properties`, after line 28:

```
# before: (no declaration)
# after:
declared_target_occurrence=<nn node>#epoch0/region/REGION.<serializeSnapshotSection region>#1
```

I deliberately do **not** invent the two ids. They must be read off the first
re-recorded 17960 seed session (`activations.jsonl`: the activation whose
region is the `serializeSnapshotSection` region, on the NN node id the
recording uses), because a guessed region id resolves to nothing and the
symptom is an `ADMISSION_GAP` that reads like a runtime bug. One command on
the first M2 17960 corpus produces both.

## 2. Roots — the policy is met, but not by the file the brief names

**`symbolic-inputs.jsonl` is not a root list.** Its schema is
`{class, method, cells}` and `InputActionCatalog.DECLARED_SYMBOLIC_ROOT`
documents what it means: *"the search starts at this field"* — hand-named
**cells**, not source ids. All three key-set cases declare exactly two rows,
identical across cases:

```
{"class":"…BlockTokenSecretManager","method":"boolean updateKeys()",
 "cells":["<org.apache.hadoop.util.Timer: long now()>.return"]}
{"class":"…BlockTokenSecretManager","method":"void addKeys(ExportedBlockKeys,boolean)",
 "cells":["<org.apache.hadoop.util.Timer: long now()>.return"]}
```

i.e. **the clock reads, and nothing else**. That is correct and matches the
policy's "every clock read (clockCallee) — CLOCK, unbounded".

The policy's *named* roots are declared **in the workloads**, through
`CausynthSymbolicSource.symbolize(...)` → `symbolizeConfiguredSourceField`, at
six sites in `BlockTokenSecretManager.java` — identical line numbers in all
five key-set trees:

| line | source id |
|---|---|
| 195 | `HDFS.BLOCK_KEY.EXPIRY_DATE.INITIAL_CURRENT` |
| 202 | `HDFS.BLOCK_KEY.EXPIRY_DATE.INITIAL_NEXT` |
| 281 | `HDFS.BLOCK_KEY.EXPIRY_DATE.RETIRED` |
| 288 | `HDFS.BLOCK_KEY.EXPIRY_DATE.CURRENT` |
| 294 | `HDFS.BLOCK_KEY.SERIAL_NO` |
| 299 | `HDFS.BLOCK_KEY.EXPIRY_DATE` |

— **the five expiry sites + SERIAL_NO, exactly**, no extras, no omissions, in
11741, 17897, bug1, bug2 and bug3. 17960 declares its one marker at
`SnapshotManager.java:197` (`HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED`), also
exactly one. ✅

`root-domains.jsonl` — 11741, 17897 and 17899 each carry **one** row,
byte-identical: `HDFS.BLOCK_KEY.SERIAL_NO`, `+0`/`+3`. Nothing else has a
domain, so the five expiry sites are domain-free and every clock is unbounded,
which is the policy verbatim. 17960 has no `root-domains.jsonl` and needs none
(a Boolean marker has no window). ✅ **No extras, no omissions.**

Cross-check against the round-2 corpora (`symbolic_root_policy.jsonl`), which
is the pipeline's own count of what it accepted:

| verdict | bug3 | bug2 | 17897 |
|---|---|---|---|
| `CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED` (the six workload sources) | 9 | 9 | 9 |
| `DECLARED_SYMBOLIC_ROOT` (symbolic-inputs cells) | 10 | — | 9 |
| `DECLARED_COMMUNICATION_CUT_PORT` (ports) | **5** | — | **6** |
| `EXPLICIT_SYMBOLIC_FAULT` | **2** | **2** | **0** |

The port row is B2 measured from the other side: 17897 has six cut ports, bug3
five. See §4.

### N1 — bug2/bug3's markers are undeclared region inputs

The policy lists "the existing Boolean fault markers (bug3's two) — MARKER" as
chosen roots. They exist, but not as anything a case file can name:

```
"regionId":   "REGION.763d087e-89f1-3a45-a53b-21f4012a2fe8"
"sourceKind": "EXPLICIT_SYMBOLIC_FAULT"
"siteId":     "<org.apache.hadoop.ipc.Client$Connection: void sendRpcRequest(Client$Call)>#u18"
"cell":       "…sendRpcRequest…::$z5"
"portId":     "REGION.763d087e….in.<uuid>"
"declared":   false
```

— a compiler temporary at the RPC-send site, with **no source id**, so
`root-domains.jsonl` can never reference it and nothing in `experiments/`
declares it. Two corrections to the policy text follow: **bug2 has them too**
(2 rows, same region), and they are not workload declarations.

Two consequences worth deciding before M2 finishes re-recording:

1. Round 2 rejected exactly these. bug3's and bug2's probes both read
   `REGION.763d087e-…in.<uuid> is not the mechanism` and both cases ended
   `NO_ROOT` on **both** polarities. Whatever these two booleans are, the
   claim layer already says they are not what makes bug2/bug3 fail — so §0's
   expected finding kinds for bug2/bug3 rest on the key-set roots, not on
   these.
2. Under Design 3 they would be **pinned**, not free:
   `FlipQuery.root()` leaves a MARKER free only when `row.declared()` is true,
   and these carry `declared: false`. If M2 publishes `RootMintRow.declared`
   from the same source, bug2/bug3 lose their only MARKER freedom silently.
   This is REPORT-REVIEW-M3 §6 item 4 meeting a real corpus: **M2 must set
   `declared` from the case declaration, and these have none** — so the
   decision is whether an `EXPLICIT_SYMBOLIC_FAULT` counts as declared. My
   recommendation: it does not, and bug2/bug3 should say so with a named gap
   rather than carry a free marker nobody declared.

No edit proposed — this is a ruling, not a line.

## 3. `clock_skew_ms` and `compose_max_valuations`

Both are read in `run_engine.sh`'s config table (`:103`, `:107`) and both are
in the `require_positive_integer` / validation block at `:421-434`.
`clock_skew_ms` is validated as *integer or the literal* `unbounded` (`:432`);
`compose_max_valuations` reaches COMPOSE as `--max-valuations` (`:589`).

| case | `clock_skew_ms` | `compose_max_valuations` |
|---|---|---|
| 11741 | `unbounded` (line 43) ✅ | **absent → 16** |
| 17897 | `unbounded` (line 32) ✅ | **absent → 16** |
| 17899 (all three) | `unbounded` (line 25) ✅ | **absent → 16** |
| **17960** | **absent → 300000** | **absent → 16** |

### S1 — the valuation budget the cases set is not the one that runs

Every case sets `reach_max_inputs=8` and `reach_max_valuations=128`.
**Neither is a known key**: they are not in `workflow_config_keys`, and
`load_workflow_config` does `known_config_key "${key}" || continue`
(`run_engine.sh:157`) — unknown keys are dropped **without a word**. The shell
test's own comment (`run_engine_campaign_helpers_test.sh:627-630`) records that
they "left with the separate solver process" and that
`compose_max_valuations` "joined in their place" — so the dead keys are a
known leftover that was never removed from the cases.

Net: the cases believe they enumerate **128** valuations; the engine enumerates
**16**. That is not a silent *failure*, but it is a silent *disagreement*
between what a case declares and what runs, and REFACTOR-D3's whole oracle is
the enumeration.

**Edits** (four files, one deletion + one addition each):

`experiments/hadoop/hdfs-11741/workflow.properties`
```
line 27  before: reach_max_inputs=8
         after:  (delete)
line 28  before: reach_max_valuations=128
         after:  compose_max_valuations=128
```
`experiments/hadoop/hdfs-17897/workflow.properties` — the same, lines **36, 37**.
`experiments/hadoop/hdfs-17899/workflow.properties` — the same, lines **17, 18**.
`experiments/hadoop/hdfs-17960/workflow.properties` — the same, lines **25, 26**.

(If 128 is too expensive now that COMPOSE runs z3 per valuation — the config
table says it does — set the number deliberately rather than inherit 16 by
omission; the point of the edit is that the case states it.)

### S2 — 17960's clock window

17960 gets the 300 000 ms default. Its closure has no clock root (its only
root is a Boolean config marker, §2), so nothing reads the window today and
this is benign. But the default is *a number somebody picked*, which is the
exact thing 17897's own comment refuses, and a case that inherits it states
nothing. **Edit** — `experiments/hadoop/hdfs-17960/workflow.properties`, after
line 28:

```
# before: (absent, default 300000)
# after:
clock_skew_ms=unbounded
```

## 4. Ports

REFACTOR-D3 §0 needs three flows per key-set case: NN→sender DEK id,
NN→DN block-key id + expiry, sender→DN request id.

| port | 11741 | 17897 | 17899 (all three) |
|---|---|---|---|
| NN→sender DEK id (`namenode-data-encryption-key-id`) | **missing** | ✅ | **missing** |
| NN→DN `block-key-id` | ✅ | ✅ | ✅ |
| NN→DN `block-key-expiry-date` | ✅ | ✅ | ✅ |
| sender→DN `data-encryption-key-id` (SASL REQUEST) | ✅ | ✅ | ✅ |

### B2 — the NN→sender DEK-id port is declared only on 17897

17897 declares it and 11741/17899 do not; the round-2 corpora agree
(`DECLARED_COMMUNICATION_CUT_PORT`: 17897 **6**, bug3 **5**; and 17897's
corpus carries 18 `namenode-data-encryption-key-id` attaches over 1 phase
while bug3's and 11741's carry none).

What it costs: without it the sender's DEK id has no producer endpoint, so the
consumer's arrival is an **unpaired attach**. Under Design 3 that is
`FlipQuery`'s `unpaired|<endpoint id>` — the control is left free and marked
`unproducible` with an `UNPRODUCIBLE_ANSWER` gap (explore) — and the arm from
the NN's DEK mint never enters the closure at all. §0 lists that flow as one
of the three the closure needs, so this is a declaration gap, not a tuning one.

**Edit** — append one line to each of
`experiments/hadoop/hdfs-11741/communication-mappings.jsonl` and
`experiments/hadoop/hdfs-17899/communication-mappings.jsonl`. The record is
17897's line 1 **verbatim**; I verified `PBHelperClient.convert` exists at the
same two signatures in `/opt/hadoop-hdfs-11741`, `-17899-bug1` and `-bug3`
(`…/hadoop-hdfs-client/…/PBHelperClient.java:1732` and `:2295`), so it
resolves unchanged:

```json
{"schemaVersion": 1, "kind": "WIRE_FLOW", "id": "namenode-data-encryption-key-id", "transport": "HADOOP_IPC", "direction": "RESPONSE", "javaType": "int", "producer": {"method": "<org.apache.hadoop.hdfs.protocolPB.PBHelperClient: org.apache.hadoop.hdfs.protocol.proto.HdfsProtos$DataEncryptionKeyProto convert(org.apache.hadoop.hdfs.security.token.block.DataEncryptionKey)>", "kind": "CALL_ARGUMENT", "callee": "<org.apache.hadoop.hdfs.protocol.proto.HdfsProtos$DataEncryptionKeyProto$Builder: org.apache.hadoop.hdfs.protocol.proto.HdfsProtos$DataEncryptionKeyProto$Builder setKeyId(int)>", "occurrence": 0, "index": 0}, "consumer": {"method": "<org.apache.hadoop.hdfs.protocolPB.PBHelperClient: org.apache.hadoop.hdfs.security.token.block.DataEncryptionKey convert(org.apache.hadoop.hdfs.protocol.proto.HdfsProtos$DataEncryptionKeyProto)>", "kind": "CALL_RETURN", "callee": "<org.apache.hadoop.hdfs.protocol.proto.HdfsProtos$DataEncryptionKeyProto: int getKeyId()>", "occurrence": 0}}
```

(`consumerField` dropped — see N2.)

This is a config-only edit in `experiments/`, no hadoop rebuild, and it is the
same shape as the 17899 expiry-port declaration the owner approved after
REPORT-EXPIRYPORT.

### Nothing stale

- **The dropped block-key-array port is gone from every case file.** Its only
  surviving mention in the tree is a test fixture constant,
  `src/test/java/…/runtime/OccurrenceAddressIsNotARequestTest.java:41`
  (`"XCH.1.resp.block-key-array"`), which names a port no config declares. Not
  an experiments edit; flagging it because that test is in the deletion path
  M-D/M2 are working through.
- 17960 declares no ports and needs none (§0: "none (one node)"). ✅

### N2 — `consumerField` has no reader

Five records carry `consumerField` (17897 ×3, 17899 ×2).
`git grep -i consumerfield src/` at `e507f365c` returns **nothing in
`src/main`** — `WireFlowCatalog` reads `id, transport, direction, javaType,
producer, consumer, producerFrameMethod, consumerFrameMethod, schemaVersion,
kind` and never `consumerField`. It is inert. Since it reads like the link
REPORT-EXPIRYPORT was about (`DelegationKey#expiryDate`), leaving it in place
invites someone to conclude the expiry field is wired when it is not. Either
delete the five occurrences or give it a reader; my recommendation is delete,
and state the field→port relation in the port's own `why` if it matters.

(Also note `WireFlowCatalog:84` **skips** any row whose `schemaVersion` is not
`SCHEMA_VERSION` — silently. All ten current records carry `schemaVersion: 1`
and are fine, but a new record written without it disappears without a gap.)

## 5. Loop bounds — all referenced, nothing orphaned

`causynth_loop_bounds` is required: it is in the `require_file` list at
`run_engine.sh:392/407/496`, is hashed into the freeze digest (`:1352`) and is
passed to the analysis as `-Dcausynth.loop.bounds` (`:498`).

| case | how it is set | file | rows |
|---|---|---|---|
| 11741 | `workflow.properties:18` `@config/loop-bounds.jsonl` | `hdfs-11741/loop-bounds.jsonl` | 23 |
| 17897 | `workflow.properties:18` | `hdfs-17897/loop-bounds.jsonl` | 16 |
| bug1, bug2 | `case.sh:4` → `run.sh:22` `CAUSYNTH_LOOP_BOUNDS` | `hdfs-17899/loop-bounds.jsonl` | 19 |
| bug3 | `case.sh:33` overrides → `run.sh:22` | `hdfs-17899/loop-bounds-datanode.jsonl` | 18 |
| 17960 | `workflow.properties:15` | `hdfs-17960/loop-bounds.jsonl` | 31 |

**Every loop-bounds file in the tree is reachable, and every case reaches
one.** 17899's `workflow.properties` deliberately omits `causynth_loop_bounds`
because `case.sh` picks per case and `run.sh` exports the env override — that
is correct, not an omission, and worth leaving as is.

## 6. What to apply, in order

1. **B1** — 17960's `declared_target_occurrence`, read off the first M2
   17960 seed session. Without it 17960 cannot compose, and it is the case
   that passes today.
2. **B2** — the `namenode-data-encryption-key-id` record appended to 11741 and
   17899. Config only; no rebuild.
3. **S1/S2** — `compose_max_valuations` in all four files (replacing the two
   dead `reach_max_*` keys), `clock_skew_ms=unbounded` in 17960.
4. **N1** — rule on whether an `EXPLICIT_SYMBOLIC_FAULT` region input counts
   as a declared marker; route to M2 with REPORT-REVIEW-M3 §6 item 4.
5. **N2** — delete the five inert `consumerField` entries, or give the field a
   reader.

Re-check after M2's first re-recording: the five `REGION.53092d3e…` strings
and 17960's new region id, against the seed session's activation rows.

# HDFS-11741 campaign

The workload retains the original HDFS-11741 behavior: the Balancer caches a
DataEncryptionKey and does not check its expiry on reuse. The Hadoop checkout
ports that cache predicate to the same current tracing and RPC interfaces used
by the other experiments.

The Balancer caches a key before two ordinary NameNode key rotations. DataNodes
refresh through the block-key RPC. The manual symbolic roots are the NameNode's
key id, time and expiry, and they come from two authorities. Two are minted by
configured-source hooks in `BlockTokenSecretManager.updateKeys`:
`CausynthSymbolicSource.symbolize("HDFS.BLOCK_KEY.SERIAL_NO", this, ...)` roots
`<org.apache.hadoop.hdfs.security.token.block.BlockTokenSecretManager: int
serialNo>`, the counter each new `BlockKey` takes its id from, and
`CausynthSymbolicSource.symbolize("HDFS.BLOCK_KEY.EXPIRY_DATE", nextKey, ...)`
roots `<org.apache.hadoop.security.token.delegation.DelegationKey: long
expiryDate>` (the field `BlockKey` inherits). A hook site owns its field: every
competing field-read candidate for it is stamped
`CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED` and left concrete, so each root is
minted once, at its hook -- which is why neither field is listed in
`symbolic-inputs.jsonl`. The third root, the clock
`<org.apache.hadoop.util.Timer: long now()>.return`, has no hook and is still
declared there -- by the two static sites it is read at,
`BlockTokenSecretManager.updateKeys()` and `.addKeys(...)`, which PLAN resolves
to whichever regions cover them. The key id *on the wire* is not a fourth root: it is a
*propagated* value carrying the NameNode's minted `serialNo`, moved by the
`block-key-id` and `data-encryption-key-id` flows in
`communication-mappings.jsonl`, and `allKeys` is shared state reconstructed
from its retained writers. Not a root is not the same as not symbolic: both
are carriers, so the plan tracks them -- the file narrows which inputs may
*mint*, never which are symbolized. (Until the mint-only policy landed it
narrowed both, and concretized 14 of this case's 18 `BOUNDED_CONTAINER_STATE`
actions, `allKeys` among them, which is precisely the reconstruction this
paragraph describes.) There is no Boolean fault marker in this workload --
`/opt/hadoop-hdfs-11741` contains no `Debug.makeSymbolicBoolean` anywhere -- so
the only thing that can open the target branch is the symbolic clock. The
custom JDK propagates the root expressions through the fixed sequence of
replies into the Balancer and DataNode state. Consumer anchors retain each
receive boundary, and selected shared reads retain bounded GuardedRead
snapshots of their writer expressions. The target is a DataNode lookup that
cannot find the Balancer's cached key.

`declared_target_occurrence` in `workflow.properties` names which occurrence
of that lookup the campaign is about, as a full occurrence address. The owner
assumes the failing instance is known; a recording is the healthy path by
nature, so no occurrence is distinguished by the corpus and the case names the
first observed one (rule: first observed, full address). lane11741h observed
four -- `balance-block#1` and `#2`, on dn0 and on dn1 -- and composing all
four cost 76 minutes; naming one turns that into one composition. The family
and k alone would not do: both DataNodes answer `balance-block#1`.

The causal graph selects this closure and its instrumentation sites. Each
region contributes its own path condition; the composer recursively merges the
consumer-anchor families and directly lowers their propagated expressions.
Retained key-update loops use the configured fixed unroll, while every repeated
RPC and shared-state access keeps its boundary occurrence and candidate writer
versions.

Hadoop checkout: `/opt/hadoop-hdfs-11741`, branch `gc/hdfs-11741-current`.
Run `./run.sh build`, then `./run.sh campaign` from this directory. Set
`CAUSYNTH_OUTPUT_DIR` to a fresh directory for each campaign. The trace starts
after all stable sources and aliases are registered and before the cache and
key-map transitions, so cluster startup cannot create unregistered regions.

## The block-key serial number's declared domain

`root-domains.jsonl` states what `HDFS.BLOCK_KEY.SERIAL_NO` may be:
`declaredDomainMin="+0"`, `declaredDomainMax="+3"` — the value this run
recorded, and up to three rotations past it.

The bound is relative because an absolute one would be a statement about one
recording: the NameNode's serial starts at a `SecureRandom` int and increments
by one per key roll, so "119994..119997" says nothing a second run would
recognise. Three rotations is the physical assumption this case is about — the
ad hoc coordination failure here is a key-set disagreement after a rotation,
and a consumer that is more than a few rolls behind has a different problem.
With the domain declared, a witness that moves the serial inside it is a
MARKER_FLIPPED finding naming the rotation; with no domain the root is pinned
to its recording and no key-set disagreement can be witnessed at all.

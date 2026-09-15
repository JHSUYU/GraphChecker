# HDFS-17897 campaign

This experiment detects the striped-file checksum failure fixed by Hadoop
PR #8364. The normal seed caches data-encryption key `G` in the DFS client and
performs two production key rotations, then uses the block-key RPC to update
each DataNode. GraphChecker
symbolically propagates the wire key IDs and the DataNode's bounded `allKeys`
state; the failure model derives that `G` is absent without a test hook that
replaces the map. The buggy checksum loop treats the returned
`InvalidEncryptionKeyException` as an ordinary per-DataNode I/O failure and
ultimately throws `PathIOException` instead of clearing the cache and retrying.

The causal graph selects the two flows that meet at the DataNode:

```text
client -> NameNode (cached key G) -> DataNode request --+
                                                     +-> SASL rejection -> client checksum failure
DataNode -> NameNode (current key G+1) -> DN state ----+
```

Values follow the live execution rather than graph edges. The custom JDK
propagates the key expressions across each RPC and shared-state read, leaving a
consumer anchor at every boundary. Region-local path conditions are merged in
closure-wide waves. Each selected shared read carries a bounded GuardedRead
snapshot of every retained writer expression; its exactly-one selector is
coupled to the corresponding writer case and local path condition.

The manual symbolic roots are the NameNode's key id, time and expiry, and they
come from two authorities. Two are minted by configured-source hooks in
`BlockTokenSecretManager.updateKeys`:
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
to whichever regions cover them. The key IDs observed on the wire are
declared cut ports, not roots of their own: they are tracked and mint
nothing, because `attachCommunicationLeaf` installs the NameNode's own
propagated expression at the consumer. `allKeys` is not modelled at region
entry: the map carries whatever expression a root-derived put left in it.

## Target occurrence

`declared_target_occurrence` in `workflow.properties` names the occurrence of
the annotated site the campaign is about, as a full occurrence address. The
campaign composes and judges that one and reports the others. The owner
assumes the failing instance is known; a recording is the healthy path by
nature, so no occurrence is distinguished by the corpus and the case names the
first observed one (rule: first observed, full address) -- lane17897g observed
`striped-file-checksum#1` and `#2`.

## Clock window

A clock root is free above zero and has no window: the formula asserts
`(>= clock 0)` and nothing else, in the composer and in the flip query alike
(`d3.explore.FlipQuery` line 362).  Nothing declares a skew.

Both removals this experiment needs are `expiryDate < now` at
`BlockTokenSecretManager:220`, and the workload runs with
`keyUpdateInterval = tokenLifetime = 1 min`, so each key's expiry sits a
small multiple of a minute past the clock that minted it.  Measured on the
recorded corpus, the DataNode's `addKeys` case needs **+278.8 s** of skew
for the registration-time copy of K1 -- inside a +/-300 s window, but with
only 21 s of headroom -- while the two copies the recorded RPC refresh
installed need **+653 s** and **+658 s**.  At the default width those two
cases are decided before the solver sees them, so the window, not the
mechanism, picks which copy of the key can expire.

900 000 ms admits all three with room, and it is still a *skew*: every
clock stays within 15 minutes of what that read actually returned, and the
recorded per-node order is unchanged.  Every other experiment keeps the
default; nothing here widens the window globally.

Run `./run.sh campaign`.  Replay concurrency is fixed at 8 in
`workflow.properties`.

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

# AsyncFS production source reading (2026-09-19)

Read all 14 files under `hbase-asyncfs/src/main` in full (3,501 Java
lines). Rechecked every file's SHA-256 and physical line count against
`hbase-main-reading-index.tsv` before marking it `full`. The production
source index now records 100/3,289 full reads. The separate
[test-workload notes](asyncfs-test-reading-notes.md) cover all 11 Java tests
and two XML test resources in the module.

## Coordination semantics checked

- `FanOutOneBlockAsyncDFSOutputHelper.createOutput` asks NameNode to create
  and allocate a block, connects to all returned DataNodes, adds a failed
  connection's DataNode to the local exclusion set, retries with overwrite,
  and begins a DFS lease only after all DataNode setup succeeds. Its
  `completeFile` loop waits for NameNode completion before ending the lease;
  `FanOutOneBlockAsyncDFSOutput` tracks pending packet acknowledgements and
  transitions through STREAMING, CLOSING, BROKEN and CLOSED.
- The slow-stream monitor collects per-DataNode acknowledgements and moves a
  repeatedly slow DataNode into `ExcludeDatanodeManager`'s cache. Subsequent
  WAL output creation takes a snapshot of that cache for NameNode block
  allocation. A configuration change rebuilds the exclusion cache after
  notifying monitors; this is a potentially stale-control-state area, but
  this reading did not establish a new explicit exception caused by its
  branch relation.
- `RecoverLeaseFSUtils` reflects over Hadoop lease recovery interfaces,
  polls asynchronous recovery with cancellation and timeout checks, and
  maps a specific `LeaseExpiredException` text to `FileNotFoundException`.
  The timeout path logs and returns rather than throwing, so no qualifying
  exception witness was inferred from a timeout alone.
- The SASL helper chooses trusted, encrypted, unsecured, privileged-port,
  fallback-auth, or general negotiation paths based on HDFS client and
  DataNode state. An `ERROR_UNKNOWN_KEY` reply clears the cached HDFS data
  encryption key and fails the connection, after which output creation can
  retry. This is expected recovery behavior in the code examined.
- `WrapperAsyncFSOutput`, `ProtobufDecoder`, and the small compatibility
  helpers were read in full. Their buffer/flush and Hadoop-version checks
  did not establish an independently qualifying distributed-state exception.

No finding from this module was added to the ledger. A test or caller-level
witness would be required before treating any cache or lease edge as a bug.

# HBase: injected ad hoc coordination bugs, proposals (research agent, 2026-10-30)

Read-only research for the brief `BRIEF-research.md` with `<sys>` = hbase. Tree read: `/bigtemp/vnr3ne/wt/hb-int-trees-6/hbase-checks`
(graphchecker/hbase-checks b5d5cc6a20). Every file:line below was read in that tree. Old-bug trees read:
`/bigtemp/vnr3ne/wt/bd-trees-1/hbase-bug-{15039,20642,28533}`. Verdicts: `/bigtemp/vnr3ne/wt/gc-hbase/results/hbase/README.md`.
Run artifacts read: `/bigtemp/vnr3ne/gc-out/hbase-final/accept-F2S-adhoc-08` (obligations, trace).

## 0. What constrains HBase (read this before the candidates)

1. **Root kinds with an HBase precedent:** HBASE_RPC REQUEST faults (hbase-adhoc-04 PASS, ns-rsgroup-removal PASS), HBASE_RPC
   RESPONSE faults (backup-lock-reply-lost PASS, hbase-buggy-20642), the ZooKeeper READ fault (hbase-adhoc-34 PASS), STATE
   re-pairing (hbase-adhoc-22 PASS, hbase-buggy-15039), and CONFIG (hbase-bugs-master-active-time PASS: a getter-read key
   stored in a field, a declared domain, the startup window). None for LOCAL_IO or TIMED_WAIT: `io_doors.jsonl` is empty in
   every HBase run (22 final runs, 6 buggy-detect runs). None for CLOCK: master-active-time abandoned the clock route for a
   configured skew. So the candidates use transport, STATE and CONFIG roots only.
2. **Many points are already buggy on the unmodified tree,** each with its own workload: 04 (HBASE-30484, a lost enable),
   22 (HBASE-30483, truncate keeps its count), 34 (a ZK READ fault on refreshKeys), 24 (a store hold past the coordinator's
   timeout), backup-lock (CAS without a nonce), ns-rsgroup (H2-01), master-active-time (skew). An injection there needs a
   workload that avoids the existing witness. Each candidate below says how.
3. **STATE claims against the client's program order:** COMPOSE still proposes re-pairings that the client's synchronous
   calls forbid (TODO HBase 15 is parked), and CONFIRM refutes them (07, 08, 10-15 ended as named bounds that way). An
   injected case may therefore spend claims on refuted models before the real one, as hbase-buggy-20642 did (5-8 claims).
   **Recommendation:** run every injected HBase case with `CAUSYNTH_CAMPAIGN_MAX_CLAIMS=8`.
4. **RPC-handler activations of `ClusterSchemaServiceImpl.getNamespace` are folded** (point 08's throw at :111). In
   F2S-adhoc-08's recording, the handler calls carry `"regionFolded":1` and no occurrence address. These are the test's
   getNamespaceDescriptor (seq 68841) and `HMaster.createTable`'s pre-check at HMaster:2538 (seq 71884), in
   `.../accept-F2S-adhoc-08/out/hbase-adhoc-08/runtime/runtime_trace.jsonl`. Only the procedure-worker activations are
   addressed (8 rows, REGION.9761fd79). So a bug that leaves a namespace permanently uncached throws first in a handler that
   no declared occurrence can name. The 08 candidates below therefore use a consumer that runs only in a procedure: the
   split's namespace-quota check.
5. **Points left out, with the reason:**
   - 07: the client's own `isTableDisabled` check (RawAsyncHBaseAdmin:2216-2220, a meta read through
     `ClientMetaTableAccessor.getTableState`, :857-866) refuses before the server guard can diverge.
   - 10-15: heavy workloads (2400-12600 s), already scope-cut and refuted by program order. 13 is vacuous.
   - 19 and 20: the test builds both descriptors.
   - 21: its counts are deterministic. `regionCount - regionCountOfTable + incr` is at most 9 against "10", so an injection
     there either throws natively or never.
   - 24, backup-lock, master-active-time: pre-buggy for any workload of that point's shape.
   - 28, 31, 35, 37: vacuous by construction (a configuration constant, start-code constants, corrupt meta, no absent
     window).
   - ns-rsgroup: an injected clear-and-refill of the tracked group map (RSGroupInfoManagerImpl:745-756) opens its window
     inside one occurrence, which CONFIRM cannot hold. Also, that map is a GraphChecker workaround map, not HBase's code.
6. **Side finding: a latent real bug on the unmodified tree.** A split that rolls back after
   SPLIT_TABLE_REGION_PRE_OPERATION never returns its namespace-quota increment:
   - SplitTableRegionProcedure:625 charges `onRegionSplit`.
   - No rollback case (SplitTableRegionProcedure:370-414) calls `MasterQuotaManager.onRegionSplitReverted` (:646-650), which
     has had no caller since the AMv2 rewrite (HBASE-14614, 3975bbd008 removed `regionStateListener.onRegionSplitReverted`).
   - So a split that fails in CHECK_CLOSED_REGIONS, CREATE_DAUGHTER_REGIONS, WRITE_MAX_SEQUENCE_ID_FILE or
     PRE_OPERATION_BEFORE_META leaves the count one too high, and a later create in that namespace is refused at
     NamespaceStateManager:168.
   - Consequences: no 22 candidate below uses a split, and this may be worth its own check.

## 1. Detectable candidates (7)

| id | point (throw) | pattern | root | workload | depth | confidence |
| --- | --- | --- | --- | --- | --- | --- |
| hbase-inj-a | hbase-adhoc-04 (AbstractStateMachineTableProcedure:163) | P3 non-idempotent retry | transport RESPONSE | TestCausynthDisableRetryNonce (20642's) | 1 | high |
| hbase-inj-b | hbase-adhoc-22 (NamespaceStateManager:168) | P4 accounting not given back | STATE | TestCausynthTruncatedTableQuota shape, merge instead of truncate | 0 | medium-high |
| hbase-inj-c | hbase-adhoc-08 (ClusterSchemaServiceImpl:111) | P1+P2 failed write drops the cache entry, no refresh on a miss | transport REQUEST | new: namespace, table, modify, split | 0 | medium |
| hbase-inj-d | hbase-adhoc-04 (AbstractStateMachineTableProcedure:163) | P11 (new): state change acknowledged before applied | STATE | TestCausynthQuotaEnableAfterAdvance + 2 s sleep | 0 | medium |
| hbase-inj-e | hbase-adhoc-34 (AuthenticationTokenSecretManager:160) | P1 refresh not consulted | STATE | TestCausynthTokenKeyWatch (15039's) | 0 | high (same world as 15039) |
| hbase-inj-f | hbase-adhoc-08 (ClusterSchemaServiceImpl:111) | P5 transient absence across steps | STATE | same as inj-c, modify async | 0 | medium-low |
| hbase-inj-g | hbase-adhoc-34 (AuthenticationTokenSecretManager:160) | P8 expiry assumption | CONFIG | new: TokenKeyWatch + an old-key token, startup window | 0 | low-medium |

Patterns: P1, P2, P3, P4, P5, P8 and a new P11. Root kinds: transport (a, c), STATE (b, d, e, f), CONFIG (g). Points: 04, 08,
22 and 34. Each doubled point pairs a different pattern with a different root:
- 04: a is P3 with a RESPONSE fault; d is P11 with STATE.
- 08: c is P1+P2 with a REQUEST fault; f is P5 with STATE.
- 34: e is P1 with STATE; g is P8 with CONFIG.

---

### hbase-inj-a: the master ignores a DisableTable's nonce (hbase-adhoc-04)

1. **Point:** hbase-adhoc-04. Guard `!ts.isEnabledOrEnabling()` at AbstractStateMachineTableProcedure:162. Throw
   `TableNotEnabledException` at :163. It runs from DisableTableProcedure's constructor (`preflightChecks(env, true)`), in
   the master's RPC handler (HMaster:2931-2932).
2. **Pattern P3** (a non-idempotent retry after a lost reply). Analogue: HBASE-20642 on the server side. The client keeps
   one nonce per operation (RawAsyncHBaseAdmin:816-821), but the master drops it, believing a disable is idempotent. The
   second procedure's preflight is not idempotent. Also akin to the backup-lock CAS without a nonce (H2-16).
3. **Mutation** (MasterRpcServices:878-887):
   ```diff
        try {
   -      long procId = server.disableTable(ProtobufUtil.toTableName(request.getTableName()),
   -        request.getNonceGroup(), request.getNonce());
   +      // disabling an already-disabling table is a no-op: no nonce bookkeeping needed
   +      long procId = server.disableTable(ProtobufUtil.toTableName(request.getTableName()),
   +        HConstants.NO_NONCE, HConstants.NO_NONCE);
   ```
   With NO_NONCE, `createNonceKey` returns null (ProcedureExecutor:862-863). Then `registerNonce(null)` returns -1
   (:874-877), and `MasterProcedureUtil.submitProcedure` (:133-136) always runs a new procedure.
   **Healthy run:** the workload disables each table once, nothing retries, and each preflight finds its table ENABLED.
   The workload passes natively (2.2 s, hbase-buggy-20642 README).
4. **Workload:** copy `TestCausynthDisableRetryNonce` (hbase-bug-20642 tree, commit 1ba966bb6c) onto the injected tree:
   one region server, two tables created, each disabled once. Copy case.sh from `experiments/hbase/hbase-buggy-20642`:
   - the target occurrence `auto0/master0#epoch0/region/REGION.98cba534-...#2`;
   - scope AbstractStateMachineTableProcedure and TableStateManager;
   - `CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=1`;
   - client faults HBASE_RPC, the default.
5. **Trigger:** an HBASE_RPC RESPONSE fault at the `RpcConnection.finishCall` marker (region REGION.678dfe9c) of client0's
   reply to the first DisableTable. The client retries with the same nonce, and the master builds a second
   DisableTableProcedure for the first table. Its preflight reads DISABLING/DISABLED and throws at :163.
   - Window: everything happens in the test method under the `up` window.
   - Mechanism: MARKER_FLIPPED, fault class `org.apache.hadoop.hbase.ipc.RpcConnection` (report.py's hbase-buggy-20642
     rule).
   - Depth: 1, as in 20642 (the retry's preflight is ordered after the first procedure's DISABLING write when a replay's
     retry runs early).
6. **Why detectable:** the witness world is hbase-buggy-20642's exactly: the same door, the same retry handler, the same
   by-shape address (B1/E1/N1: SAT, CONFIRM, native by shape 10/10, control 0/10). Only the place where the nonce is lost
   moves, from the client to the master. On the unmodified tree the retry is deduplicated, so the world reaches no
   preflight.
7. **Risks:**
   - The native count is by IDENTITY §9 shape (exact 0/10), as 20642's; the owner accepted that for 20642.
   - Refuted claims before the confirmed one (20642: 5-8): set MAX_CLAIMS 8.
   - Low novelty: the same mechanism as an old-bug case. A config caveat: with `hbase.client.nonces.enabled=false` the
     unmodified code behaves the same.
   - Confidence: **high**.

### hbase-inj-b: a merge does not give its region back to the namespace quota (hbase-adhoc-22)

1. **Point:** hbase-adhoc-22. Guard `currentStatus.getRegionCount() + numRegions > getMaxRegions(nspdesc)` at
   NamespaceStateManager:165-167. Throw `QuotaExceededException` at :168. It runs in
   CreateTableProcedure.preCreate (CreateTableProcedure:334-337).
2. **Pattern P4** (state left inconsistent by an operation that skips its bookkeeping). Analogue: HBASE-30483, where a
   truncate keeps the old region count (this point's own bug), and H2-11, where truncate(false) keeps the namespace count.
   The injected mistake is the merge-side twin: "shrinkage is reconciled when the table is deleted".
3. **Mutation** (NamespaceStateManager:98-100). The merge calls this with `incr = -1` through
   MergeTableRegionsProcedure:560-565, then MasterQuotaManager:535-539 (`onRegionMerged`), then NamespaceAuditor:123-134:
   ```diff
         NamespaceTableAndRegionInfo nsInfo = nsStateCache.get(namespace);
   -     if (nsInfo != null) {
   +     if (nsInfo != null && incr > 0) { // a merge only shrinks; reconciled when the table goes
           nsInfo.incRegionCountForTable(name, incr);
   ```
   **Healthy run:** the count stays 2 after the merge, which is wrong but silent. The deletion's release
   (DeleteTableProcedure:149-153, then :448-453, then `removeTable`) subtracts the table's 2, so the creation 2 s later
   checks 0 + 1 ≤ 2 and passes.
4. **Workload:** a new `TestCausynthMergedTableQuota`, modelled on `TestCausynthTruncatedTableQuota` (hbase-adhoc-22's).
   - Quota on; namespace `causynth_quota` with `KEY_MAX_REGIONS "2"`.
   - `createTable(T, split key "m")` makes 2 regions.
   - `admin.mergeRegionsAsync(new byte[][]{a, b}, false).get()` leaves 1 region.
   - `disableTable(T)`, then `Future d = deleteTableAsync(T)`, then `Thread.sleep(2000)`.
   - `createTable(U)` (1 region), then `d.get()`.
   - No truncate, so HBASE-30483's world is absent. The target occurrence is the created table's check, read off a seed
     (22's is `REGION.ebc27075...#2`). Use 22's scope and depth 0.
5. **Trigger:** STATE re-pairing. U's check reads the namespace total paired with T's `addTable(2)` version, before the
   deletion's `removeTable`. The deletion's POST_OPERATION step is held at its claim entry until the read exits. Then
   2 + 1 > 2 throws at :168.
   - On the correct code the same world reads 1 + 1 ≤ 2.
   - Window: everything is in the test method.
   - Mechanism: STATE_PAIRING_FLIPPED, no clock.
6. **Why detectable:** this is hbase-adhoc-22's own PASS formula and hold. Its claim reads "the creation's quota read
   joined to the truncated table's original addTable (the truncate writes none) ... held at its step's claim entry"
   (NC15-22 and F2B-adhoc-22, native 10/10). Here the merge, like the truncate, writes nothing to the count.
7. **Risks:**
   - The merge adds replay cost: it closes 2 regions and opens 1.
   - It is the same mechanism as the point's existing bug, so it is less novel.
   - Confidence: **medium-high**.

### hbase-inj-c: a failed namespace update drops the cached descriptor, and nothing reloads it (hbase-adhoc-08)

1. **Point:** hbase-adhoc-08. Guard `nsd == null` over `TableNamespaceManager.get` (TableNamespaceManager:221-223). Throw
   `NamespaceNotFoundException` at ClusterSchemaServiceImpl:111.
2. **Pattern P1 + P2.** Stale coordination state is not refreshed on a miss: the cache has no reload. A remote error ends
   the operation as if it had succeeded. Analogue: HBASE-15039 (a miss with no refresh), and HDFS-17897 or -12931, where an
   error is mishandled instead of retried with fresh state.
3. **Mutation** (ModifyNamespaceProcedure:85-91, plus a 3-line public wrapper of the private `uncached`,
   TableNamespaceManager:125-127):
   ```diff
        } catch (IOException e) {
          if (isRollbackSupported(state)) {
            setFailure("master-modify-namespace", e);
          } else {
            LOG.warn("Retriable error trying to modify namespace=" ...);
   +        if (state == ModifyNamespaceState.MODIFY_NAMESPACE_UPDATE_NS_TABLE) {
   +          // the cached descriptor may be stale now: drop it, readers reload it from meta
   +          getTableNamespaceManager(env).invalidate(newNsDescriptor.getName());
   +          return Flow.NO_MORE_STATE;
   +        }
          }
   ```
   The assumption is wrong: `get()` reads only the cache, and nothing reloads it.
   **Healthy run:** the meta put never fails, so the catch never runs.
4. **Workload:** a new `TestCausynthNamespaceQuotaSplit`, modelled on TestCausynthTruncatedTableQuota.
   - Quota on, one region server; `createNamespace(ns, KEY_MAX_REGIONS "10")`.
   - `createTable(ns:t)` (1 region).
   - `modifyNamespace(ns with KEY_MAX_REGIONS "20")`.
   - `admin.splitRegionAsync(region, "m").get()`.
   - Declarations:
     - the target occurrence is the split procedure's getNamespace activation, read off a seed (the k-th activation of
       REGION.9761fd79 on master0, after createTable's two);
     - scope: 08's plus ModifyNamespaceProcedure;
     - depth 0.
   - The split is the consumer because its PRE_OPERATION quota check runs on a procedure worker (addressed, §0.4):
     SplitTableRegionProcedure:625, then NamespaceAuditor:111-121, NamespaceStateManager:84, :142, and
     ClusterSchemaServiceImpl:111. NamespaceStateManager:143 catches the throw, which still ends the occurrence in THROW.
5. **Trigger:** an HBASE_RPC REQUEST fault on master0's hbase:meta Mutate in MODIFY_NAMESPACE_UPDATE_NS_TABLE. The door
   is the `AbstractRpcClient.callMethod` marker under `TableNamespaceManager.addOrUpdateNamespace`.
   - The put is single-attempt in automatic mode (TableNamespaceManager:233-235), so one fault surfaces.
   - The injected catch drops the cache entry and finishes; the client's modify returns OK; the split's quota read misses,
     and :111 throws.
   - Window: everything is in the test.
   - Mechanism: MARKER_FLIPPED, fault class `org.apache.hadoop.hbase.ipc.AbstractRpcClient`.
6. **Why detectable:**
   - hbase-bugs-ns-rsgroup-removal PASS moved this very door kind: "the HBASE_RPC REQUEST fault of master0's hbase:meta
     Mutate in CREATE_NAMESPACE_INSERT_INTO_NS_TABLE ... an own-turn earlier door of `TableNamespaceManager#cached`"
     (native 10/10).
   - F2S-adhoc-08 on the unmodified tree explored the same doors in round 0: obligations `688dd4026bc4bcc1` (callMethod
     #u61) and `da0d4a10308716ca` (#u66) in master0's namespace-procedure step, both ADMITTED and refused by the retry.
     They are under `.../accept-F2S-adhoc-08/out/hbase-adhoc-08/schedule/iteration-0000/obligations-0000/`.
   - Here the injected catch makes that refused world reach :111.
7. **Risks:**
   - The split adds replay cost.
   - The k-th selector must be read off a seed.
   - The fatal is caught: count it, as hbase-adhoc-24's caught throw was.
   - Program-order STATE noise (the split's read paired to INITIAL): MAX_CLAIMS 8.
   - Confidence: **medium**.

### hbase-inj-d: the quota observer enables a table asynchronously (hbase-adhoc-04)

1. **Point:** hbase-adhoc-04, the same throw as inj-a (:163), reached from FlushTableProcedure's preflight. That is 04's
   declared occurrence `REGION.98cba534...#2`, "the test's flush".
2. **Pattern P11 (new):** a state change is acknowledged before it is applied, and a dependent step runs in between. It is
   close to P5 (a stale view). Analogue: HBASE-19953, where DDL RPCs returned before the procedure's prepare (the reason for
   the blocking prepare latch, HMaster:2928-2933). Also this point's HBASE-30484, where the observer enables only after advancing.
3. **Mutation** (QuotaUtil:636-643, called from QuotaObserverChore:333):
   ```diff
      public static void enableTableIfNotEnabled(Connection conn, TableName tableName)
        throws IOException {
        try {
   -      conn.getAdmin().enableTable(tableName);
   +      conn.getAdmin().enableTableAsync(tableName); // do not block the chore on the procedure
        } catch (TableNotDisabledException | TableNotFoundException e) {
   ```
   **Healthy run:** with the 2 s sleep added before the flush, the EnableTableProcedure finishes long before it, and the
   flush reads ENABLED.
4. **Workload:** `TestCausynthQuotaEnableAfterAdvance` (04's), with `Thread.sleep(2000)` before `admin.flush(table)` (a
   variant file). Use 04's case row, but `client_fault_transports=(ZOOKEEPER)`, as cases 07 and 11-15 do. This removes
   every HBASE_RPC fault, and with it HBASE-30484's lost-enable world. Depth 0. The target occurrence is read off a seed;
   04's is `#2`.
5. **Trigger:** STATE re-pairing. The flush's preflight read of `TableStateManager.tableName2State`
   (TableStateManager:172-175) is paired with the test's own DISABLED write. The EnableTableProcedure's
   SET_ENABLING_TABLE_STATE step is held at its claim entry until the read exits, and :163 throws.
   - On the unmodified tree the observer's synchronous enable orders the step before the flush, so CONFIRM refutes that
     model.
   - Window: everything is in the test.
   - Mechanism: STATE_PAIRING_FLIPPED.
6. **Why detectable:**
   - The same read and region as 04's PASS (F1B-adhoc-04, 839 s, native 10/10, light workload).
   - The procedure-step claim-entry hold of hbase-adhoc-22's PASS.
   - It is the shape of 15039: a natively ordered sleep, concurrent for GraphChecker.
7. **Risks:**
   - It needs a variant workload, because the sleep is new.
   - Check in the seed that the observer's enable preflight does not shift the `#2` selector.
   - Confidence: **medium**.

### hbase-inj-e: the refreshed keys are never consulted (hbase-adhoc-34)

1. **Point:** hbase-adhoc-34. Guard `masterKey == null` at AuthenticationTokenSecretManager:159. Throw `InvalidToken` at
   :160.
2. **Pattern P1** (stale cached state; the refresh on a miss happens but its result is not used). Analogue: HBASE-15039.
3. **Mutation** (AuthenticationTokenSecretManager:153-157):
   ```diff
          zkWatcher.refreshKeys();
          if (LOG.isDebugEnabled()) {
            LOG.debug("Sync token keys from zookeeper");
          }
   -      masterKey = allKeys.get(identifier.getKeyId());
        }
   ```
   **Healthy run:** the first lookup (:137) finds the key, because the watcher applied it within the 2 s sleep. The miss
   block is never entered.
4. **Workload:** `TestCausynthTokenKeyWatch` from the hbase-bug-15039 tree (c2cecb3756). Copy case.sh from
   `experiments/hbase/hbase-buggy-15039`: target `first`, scope AuthenticationTokenSecretManager and ZKSecretWatcher, depth
   0, window `up`. Do not add ZOOKEEPER faults: on this workload the key master's `addKeyToZK` write fault already reaches
   :160 on the unmodified code (ZKSecretWatcher:180-194 aborts only the key master).
5. **Trigger:** STATE re-pairing. The other server's `allKeys.get` (:137) is paired with the map version before its
   watcher's `addKey` (ZKSecretWatcher:121-134, then :140-160, then AuthenticationTokenSecretManager:189). The watcher's
   occurrences are held after the anchor. The refresh adds the key, the local stays null, and :160 throws.
   - Window: everything is in the test.
   - Mechanism: STATE_PAIRING_FLIPPED.
6. **Why detectable:** this is hbase-buggy-15039's world, with the same holds (B1 SAT native 10/10; E1 8/10). The fixed
   code throws nothing in that world.
7. **Risks:** almost none technically. The objection is novelty, since it is the old-bug case's world. A variant with
   the same world and a different mistake: `refreshKeys` rebuilds from the watcher's last children snapshot instead of
   ZooKeeper (P1, a stale snapshot), about 8 lines. Confidence: **high**.

### hbase-inj-f: a namespace modification hides the namespace between its steps (hbase-adhoc-08)

1. **Point:** hbase-adhoc-08 (ClusterSchemaServiceImpl:111), with the same consumer as inj-c.
2. **Pattern P5:** a reader sees a transient intermediate state, the cache emptied before it is refilled. Analogues:
   SOLR-9440 (a view between updates) and the ZK container reuse.
3. **Mutation** (ModifyNamespaceProcedure:67-75, with the same `invalidate` wrapper as inj-c):
   ```diff
          case MODIFY_NAMESPACE_PREPARE:
            boolean success = prepareModify(env);
            releaseSyncLatch();
            if (!success) { ... return Flow.NO_MORE_STATE; }
   +        // nobody may use the outdated quota while the modification is in flight
   +        getTableNamespaceManager(env).invalidate(newNsDescriptor.getName());
            setNextState(ModifyNamespaceState.MODIFY_NAMESPACE_UPDATE_NS_TABLE);
   ```
   UPDATE_NS_TABLE (:76-78) re-caches the new descriptor (`cached`, TableNamespaceManager:120-123).
   **Healthy run:** the UPDATE step runs milliseconds after PREPARE, and the split comes 2 s later. Nothing else reads the
   namespace in that gap.
4. **Workload:** as inj-c, but `modifyNamespaceAsync(ns')` (it returns after the PREPARE latch, HMaster:3673-3678), then
   `Thread.sleep(2000)`, then the split. Same target, scope and depth 0.
5. **Trigger:** STATE re-pairing. The split's getNamespace read (`cache.get`) is paired with PREPARE's remove. The UPDATE
   step is held at its claim entry until the read exits, and :111 throws (caught at NamespaceStateManager:143). On the
   unmodified tree the cache only ever goes from the old descriptor to the new one, never absent. Mechanism:
   STATE_PAIRING_FLIPPED.
6. **Why detectable:** the hold is hbase-adhoc-22's: the claim-entry hold of a procedure step against a master-cache read,
   native 10/10. The read and its writers (`cached`, `uncached`) already compose as writer arms in the 08 formulas:
   "`nsd == null` over `TableNamespaceManager.cache.get` has writer arms" (HBASE.md §E, 08).
7. **Risks:**
   - The injected line is more contrived than inj-c's.
   - The same split cost and selector risk as inj-c.
   - Confidence: **medium-low**.

### hbase-inj-g: a rolled-out key is retained for (lifetime minus interval) (hbase-adhoc-34)

1. **Point:** hbase-adhoc-34 (:160), reached through the key master deleting the token's key.
2. **Pattern P8** (a time or expiry assumption). Analogue: the HDFS-11741 family, where a key expires before tokens
   signed with it. The flawed reasoning: "the old key already signed tokens for one interval".
3. **Mutation** (AuthenticationTokenSecretManager:262-266, in `rollCurrentKey`):
   ```diff
        if (prev != null) {
          // make sure previous key is still stored
   -      prev.setExpiration(now + tokenMaxLifetime);
   +      prev.setExpiration(now + tokenMaxLifetime - keyUpdateInterval); // it signed for one interval already
   ```
   **Healthy run:** with the defaults (RpcServer:435-436: 1 day and 7 days) the old key is kept for 6 days, so nothing
   expires in the test.
4. **Workload:** a new `TestCausynthTokenKeyRetention`, modelled on TestCausynthTokenKeyWatch.
   - Steps:
     - wait for the key master;
     - `T1 = leader.generateToken(...)`, under key K1;
     - `leader.rollCurrentKey()`, rolling to K2;
     - `leader.removeExpiredKeys()`, which is package-private: the test drives the chore once, as
       TestCausynthQuotaEnableAfterAdvance drives the observer;
     - `Thread.sleep(2000)`;
     - `assertArrayEquals(T1.getPassword(), other.retrievePassword(T1 id))`.
   - Declarations:
     - `recording_window=startup`: the keys are read at server start, RpcServer:431-439;
     - scope: 34's plus `server=:org/apache/hadoop/hbase/ipc/RpcServer`;
     - a declared domain for `CONFIG:hbase.auth.token.max.lifetime` and `CONFIG:hbase.auth.key.update.interval` in a
       root-domains.jsonl, for example [1000, 604800000], like master-active-time's;
     - depth 0.
5. **Trigger:** CONFIG (`hbase.auth.token.max.lifetime`, or the interval).
   - The key master's `key.getExpiration() < now` in `removeExpiredKeys` (:228-236), a guard of the writer
     `iter.remove()`, flips. It deletes K1's znode (ZKSecretWatcher:166-178).
   - The other server's `nodeDeleted` runs `removeKey` (ZKSecretWatcher:83-95, then AuthenticationTokenSecretManager:199-211).
   - Validation: the lookup misses, `refreshKeys` finds no K1, and :160 throws. T1 itself stays valid at :134, as long as
     max.lifetime is at least (validate - issue).
   - On the correct code, removing K1 needs max.lifetime < (remove - roll), which also expires T1 at :134 first, so :160 is
     unreachable there.
   - Mechanism: MARKER_FLIPPED by a CONFIG root, no clock.
6. **Why detectable:**
   - hbase-bugs-master-active-time: a getter-read key stored in a field, a declared domain, the startup window, native
     plant at the getter (49c5698b7).
   - The cross-node token-key chain (watcher occurrences under HBASE_ZK.ZKSECRETWATCHER anchors): 15039 and NZ3-34.
7. **Risks:**
   - Whether ConfigRoots mints these keys through the constructor parameters into AuthenticationTokenSecretManager's fields.
   - The flip compares against two clock cells placed on the recording's timeline.
   - The deletion and its watch event are new topology, and need GROW.
   - The startup window makes the seed heavier (34 took 1016 s).
   - Confidence: **low-medium**. It is the only CONFIG candidate.
   - Run with the default `up` window, the same bug is undetectable by design: its trigger is fixed at server start,
     before the window.

## 2. Undetectable candidate (optional for HBase; 1)

### hbase-inj-u: a key miss is answered with the current key, silently (hbase-adhoc-34)

- **Point and pattern:** hbase-adhoc-34 (:160). P1 + P2: a miss on cached coordination state is converted into a wrong
  value.
- **Mutation** (AuthenticationTokenSecretManager:137-158). Replace the whole miss block (the abort check, the elector
  restart, `refreshKeys` and the re-read) with a "fast path":
  ```diff
      AuthenticationKey masterKey = allKeys.get(identifier.getKeyId());
      if (masterKey == null) {
  -     ... abort check, elector restart, zkWatcher.refreshKeys(), re-read (:139-157) ...
  +     masterKey = currentKey; // a token is almost always signed with the newest key
      }
  ```
- **Workload for the GraphChecker run:** TestCausynthTokenKeyWatch, unchanged (it passes natively). Expected verdict:
  UNSAT_CLOSED. In the window `currentKey` is never null: the startup `addKey` set it before `up`, and every in-window
  writer stores a key. So no world takes :160.
- **Observable symptom, checkable natively and deterministically:** a variant test. Steps: T1 under K1, roll to K2, sleep
  2 s, so the other server's `currentKey` is K2. Then `other.removeKey(K1)`, the "watch event not yet processed" device of
  TestCausynthTokenKeys. Then `assertArrayEquals(T1.getPassword(), other.retrievePassword(T1 id))`. It fails on every run:
  the password is computed with K2. On the correct code, `refreshKeys` reloads K1 from ZooKeeper and the assertion holds.
  A racy variant (TokenKeyWatch without the 2 s sleep) fails intermittently.
- **Why GraphChecker cannot detect it:** the coordination still goes wrong in GraphChecker's own STATE world (the
  validation before the watcher's `addKey`), but its outcome is a wrong password returned silently. GraphChecker answers
  only whether the declared throw `(r,c,i)` fires, and the mutation makes the fatal arm unreachable in every world. The
  wrong value surfaces later, in SASL's digest check or the test's assertion, which is no declared target. This is the
  silent-failure class.

## 3. Ranked recommendation (5)

1. **hbase-inj-a** (04, P3, RESPONSE fault): the most certain. It reuses 20642's proven world and workload; only the place
   where the nonce is lost moves.
2. **hbase-inj-b** (22, P4, STATE): 22's PASS formula and hold with a merge instead of a truncate. A light workload with
   one root.
3. **hbase-inj-e** (34, P1, STATE): technically as certain as 15039. Swap it out if the lead rejects reusing an old-bug
   world; the stale-snapshot variant or inj-g replaces it.
4. **hbase-inj-c** (08, P1+P2, REQUEST fault): a door GraphChecker already explored at this point (F2S-08 round 0) and
   moved in ns-rsgroup's PASS. The injected catch turns a refused world into a witness.
5. **hbase-inj-d** (04, P11, STATE): a new pattern (acknowledged before applied) on 04's light, already-PASSing workload,
   with RPC faults switched off so HBASE-30484 cannot answer.

Alternates: inj-g if the lead wants a CONFIG root from HBase (the other systems may cover CONFIG better: SOLR-6101/6197);
inj-f as a second STATE pattern at 08.

## 4. Doubts

- Claims budget: STATE noise against the client's program order (TODO HBase 15 parked) can use claims before the real
  witness. Use MAX_CLAIMS 8 (hbase-buggy-20642 decided 6-8 claims).
- Selectors: inj-b, c, d and f need their target occurrence read off a seed. inj-c and f need the k-th getNamespace
  activation on master0, because the split's check is not `first`.
- Folded handlers (§0.4): a bug that makes the :111 throw fire first in an RPC handler cannot be declared. This is why the
  08 candidates use the split's procedure-side check.
- inj-g depends on ConfigRoots minting a getter-read key that reaches the target through constructor parameters and a ZK
  deletion. It has no direct precedent beyond master-active-time's simpler chain.
- Side finding §0.6 (a split rollback leaks the namespace quota on the unmodified tree): it is unverified natively, a
  candidate for a real-bug check, and the reason no 22 candidate splits.

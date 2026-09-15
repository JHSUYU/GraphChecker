# GraphChecker

GraphChecker builds bounded, failure-directed causal replays for distributed
Java workloads. From a workload and target it discovers the relevant program
slice, records concrete node and request flows, explores selected alternatives,
propagates symbolic values through heap and message boundaries, and composes an
SMT formula.

The result is about the selected bounded model. An incomplete search is not a
whole-program unreachability proof.

## Toolchain

```text
workload + target + wire flows + loop bounds
  -> static discovery
  -> pass 1 skeleton trace
  -> pass 2 state trace and causal graph
  -> immutable linked region-path plan
  -> concolic replay and import
  -> causal composition
  -> SMT and Z3
```

The shell orchestrator freezes inputs and launches stages; it does not infer
causal edges or symbolic expressions. Static discovery owns capture sites, the
runtime owns observations, the custom VM owns symbolic expressions, and the
Composer owns formula closure.

Tracing runs the workload twice. Pass 1 instruments method activation
envelopes only and selects the candidate region skeletons the run activated;
each selected skeleton is the candidate's own row carrying the anchor names
that run observed. Pass 2 re-instruments only the selected region methods and
records calls, branches, arguments and direct declared-field accesses. The
region finalizer mints each occurrence identity exactly once over the pass-2
trace and stamps it onto the activation; the region planner and every later
stage read that identity instead of deriving one.

Communication uses one transport-neutral model:

- A workload registers each stable node owner, then begins a request flow from
  that node.
- Every HTTP request and response carries the current trace context. Inbound
  handling installs the remote parent, source, and request flow for a scoped
  interval and restores the previous context on exit.
- Exchange correlation contributes topology only. It never reconstructs a
  context or symbolic value.
- A `WIRE_FLOW` declares one typed producer and consumer. Its capture kind is
  exactly one of `METHOD_PARAMETER`, `METHOD_RETURN`, `CALL_ARGUMENT`, or
  `CALL_RETURN`.
- OUT captures export a symbolic message leaf; IN captures attach that leaf.
  Request and response directions use the same mechanism.

Each campaign iteration is immutable. New topology closes the current
iteration and is planned in the next one. Content-addressed caches are reused
only when their relevant frozen inputs match.

## Requirements

- Stock JDK 8 and Maven for GraphChecker and seed tracing
- The customized OpenJDK 8 Zero VM for concolic replay
- Z3, `jq`, `python3`, and `sha256sum`
- Compiled workload production/test classes and their complete classpath

Build GraphChecker and, when needed, the custom VM:

```bash
export JAVA_HOME=/absolute/path/to/jdk8
export PATH="$JAVA_HOME/bin:$PATH"
mvn -q -DskipTests package

JOBS=4 \
  third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_build_in_docker.sh
```

The custom VM build and smoke-test instructions are in
[third_party/OpenJDK-Concolic-Execution-Engine/README.md](third_party/OpenJDK-Concolic-Execution-Engine/README.md).

## Workflow configuration

`run_engine.sh` reads a small `key=value` workflow file. Paths may be absolute
or use `@config`, `@repo`, and `@project`. The corresponding
`GRAPH_CHECKER_*` and `CAUSYNTH_*` environment variables may override values;
the `config` command prints the result.

At minimum, configure the workload repository/module, production classes,
classpath, target, loop-bound declarations, workload command and test identity,
custom VM, scheduling/solver bounds, and fresh output/cache roots. Configure
`causynth_communication_mappings` when the target crosses a message boundary,
and `causynth_symbolic_inputs` to narrow root minting to a declared allowlist.
An empty loop-bound file explicitly means that the selected workload has no
retained condition-controlled loop requiring a bound.
`docs/CONCOLIC_INTEGRATION.md` describes each declaration file.

`solver_timeout_ms` is the per-query Z3 budget for every solver stage,
including each region path-flip query. A flip query that exhausts it is
recorded as the `SOLVER_TIMEOUT` exploration status and named as a
`PATH_FLIP_SOLVER_TIMEOUT` coverage gap: the campaign continues, and only a
closed UNSAT conclusion is withheld. Raise it when a host runs several
campaigns at once.

`schedule_max_jobs` caps how many workload JVMs a stage starts at once. The
members of one linked replay bundle always run in one JVM, so this bounds
concurrent bundles, not concurrent regions. `clock_skew_ms` (default 300000)
bounds how far a witness may move a wall clock from the value that read
returned; cross-node skew is a failure mechanism the checker explores, so it is
bounded rather than pinned.

`region_path_max_waves` (default 12, override
`CAUSYNTH_REGION_PATH_MAX_WAVES`) bounds the EXPLORE closure loop. That loop
normally ends at its own fixed point, when every member's
`region_path_manifest.json` reports `state=CLOSED`. Two guards keep a closure that is not converging from
running forever:

- **No progress.** A wave that proposes exactly the obligations the previous
  wave proposed, over an exploration-record set whose verdict histogram is
  also unchanged, has learned nothing; the loop stops instead of re-solving
  and re-replaying the same set.
- **Wave budget.** Failing that, the loop stops after
  `region_path_max_waves` waves.

Either stop is recorded on every still-pending worklist as a
`REGION_PATH_CLOSURE_NO_PROGRESS` or `REGION_PATH_WAVE_BUDGET_REACHED`
coverage gap, never as a campaign failure. Like any coverage gap these are
telemetry: an unexplored sibling path withholds a closed UNSAT conclusion and
says nothing about a SAT candidate, so the campaign still publishes what it
established. Raise the budget for a workload whose closure legitimately needs
more waves than it has members.

`campaign_stop_after` (default empty, override
`CAUSYNTH_CAMPAIGN_STOP_AFTER`) names the stage after which a campaign returns
successfully, exit code 0. The only value it accepts is `IMPORT`: the campaign
runs PREFLIGHT through IMPORT of its first epoch and stops there, having
published the replay session and its per-kind row census, which is what a
runtime change is gated on; reaching it through EXPLORE..EMIT costs hours and
answers a different question. Left empty the campaign proceeds to EXPLORE
and runs to EMIT as usual. Any other value is a configuration error, named by
`validate` and by the campaign's own PREFLIGHT stage.

Inspect and validate before running:

```bash
./run_engine.sh --config /absolute/path/workflow.properties config
./run_engine.sh --config /absolute/path/workflow.properties validate
```

Run the complete campaign:

```bash
./run_engine.sh --config /absolute/path/workflow.properties campaign
```

## HDFS experiments

All GraphChecker experiments run from `main`. The Hadoop workloads have separate
checkouts so that their source changes and compiled classes remain independent.

| Case | Hadoop checkout | Experiment entry point |
| --- | --- | --- |
| HDFS-11741 | `/opt/hadoop-hdfs-11741` | `experiments/hadoop/hdfs-11741/run.sh` |
| HDFS-17897 | `/opt/hadoop-hdfs-17897` | `experiments/hadoop/hdfs-17897/run.sh` |
| HDFS-17899 Balancer | `/opt/hadoop-hdfs-17899-bug1` | `experiments/hadoop/hdfs-17899/run.sh bug1` |
| HDFS-17899 SPS | `/opt/hadoop-hdfs-17899-bug2` | `experiments/hadoop/hdfs-17899/run.sh bug2` |
| HDFS-17899 DataNode | `/opt/hadoop-hdfs-17899-bug3` | `experiments/hadoop/hdfs-17899/run.sh bug3` |
| HDFS-17960 | `/opt/hadoop-hdfs-17960-jdk8` | `experiments/hadoop/hdfs-17960/run.sh` |

Append `build` to compile a workload and run its concrete test. Append `campaign`
to execute the full GraphChecker pipeline. For example:

```bash
experiments/hadoop/hdfs-17899/run.sh bug1 build
CAUSYNTH_OUTPUT_DIR=/tmp/hdfs-17899-bug1-fresh \
  experiments/hadoop/hdfs-17899/run.sh bug1 campaign
```

Use a fresh output directory for each campaign. Keep its workflow, mappings,
compiled classes and replay scripts unchanged until it finishes. The shared
build and classpath helpers ensure Hadoop compiles against the current
GraphChecker API and loads its own common/client classes, even when another
case has installed the same Hadoop SNAPSHOT coordinates in Maven's cache.

## Results

`schedule/final/` contains exactly six files: `candidate.smt2`,
`candidate_composition_manifest.json` (which carries the SOLVE stage's
valuations and claim under `solver`), `path-closures.json`,
`gaps.json`, `result.json`, and `run-manifest.json`, which records the frozen
provenance digests, the per-iteration manifests, and the digest of every other
published artifact. The frozen inputs themselves are not in `final/`: the
private read-only copy of the tool the run executed is the `GraphChecker.jar`
in `schedule/frozen-inputs/`. Accepted outcomes are:

- `SAT_CANDIDATE`: a bounded witness was found and a symbolic root flips the
  target predicate.
- `UNSAT_CLOSED`: the composed bounded model is closed and unsatisfiable.
- `INCONCLUSIVE_PARTIAL`: no accepted claim; read `whyNotAccepted`.

`ClaimPolicy` decides the claim and names every reason it is not accepted in
`result.json`: one `blockers` row per reason and one `whyNotAccepted` line,
which EMIT also prints. A claim is accepted only when that list is empty, so a
run needs zero aggregate gaps, a root space the solver decided is constrained,
every declared `WIRE_FLOW` reaching the formula by its port family or by the
field its consumer assigns, a fatal read whose own container was reconstructed,
an injected fault marker that decides the verdict, and matching fresh
provenance. Closed selected-path authority is required for `UNSAT_CLOSED`
alone; open sibling paths leave a SAT candidate accepted. The Composer's
`finalStatus: FINAL_READY` states that the formula is complete, not that the
run was accepted. A zero process exit or an old SMT file is not sufficient.
`docs/CONCOLIC_INTEGRATION.md` holds the whole blocker table, and the policy
replays offline on any published `schedule/final/`.

## Development checks

```bash
bash -n run_engine.sh
bash src/test/shell/run_engine_campaign_helpers_test.sh
mvn -q test
git diff --check
```

Main code lives under `src/main/java/.../` in the packages `annotation`,
`causynth`, `concolic`, `contract`, `option`, `runtime` and `transformer`; the
identity and artifact contracts shared across stages live in `contract`. The
custom VM is under `third_party/OpenJDK-Concolic-Execution-Engine`.

## Outstanding work (refactor/flatten-handoff-next, 2026-09-12)

`$SP` = `/tmp/claude-20003/-opt-GraphChecker/99c84a54-86ac-44a4-a030-760f664ae2a1/scratchpad`（本次会话的 scratchpad）。

### 当前状态

- staging 分支 `refactor/flatten-handoff-next` @ `1a6ca9429`（工作树干净，175 commits over `main`），`mvn -o test` 282 绿；`main` 仍在 `3d9355745`，未落地。
- 验收标准：buggy 版本 `claim=SAT_CANDIDATE`、`blockers=[]`、`finalStatus=FINAL_READY`，且完整 `candidate.smt2` 上 buggy 极性 sat、另一极性 unsat（或 `mechanismNecessity` 判定为必要的命名机制）。工具：`$SP/final/accept_final.sh`（串行、`DRY=1` 预检）、`$SP/final/probe_final.sh`、`$SP/final/report_final.py`。
- 17960：`$SP/l1/out5/schedule/final/result.json` = `finalStatus=FINAL_READY`、`gapCount=0`、`claim=INCONCLUSIVE_PARTIAL`、`solverState=CANDIDATE_READY`；`sym__HDFS_CONFIG_SNAPSHOT_DELETION_ORDERED` 取 `false` 时 sat、取 `true` 时 unsat；剩 1 个 blocker `UNDETERMINED_INITIAL_STATE`（subject `MAP_STATE/144#-3`，一个容器载体初始快照被截断，待查是白名单类还是超上限）。
- bug3：链完整、`allKeys` 快照已判定、声明收窄后待终轮；最新语料 `$SP/snap/out/out/hdfs-17899-bug3` 仍是修复前的 `FINAL_REFUSED`、2 缺口、blockers `COMPOSER_NOT_FINAL_READY` / `COMPOSITION_GAPS_UNRESOLVED` / `FAULT_MARKER_NOT_DETERMINING`。
- bug2：同 bug3 待终轮；最新语料 `$SP/verify-out3/out/hdfs-17899-bug2` = `FINAL_READY`、0 缺口、1 个 blocker `DECLARED_WIRE_FLOWS_UNREALIZED`、sat/unsat 两极性已分离。
- 17897：待终轮；最新语料 `$SP/verify-out3/out/hdfs-17897`（13:11，非 staging tip）= `FINAL_READY`、0 缺口、3 个 blocker `UNDECIDED_ROOT_SPACE` / `TARGET_UNCONSTRAINED_BY_ROOTS` / `DECLARED_WIRE_FLOWS_UNREALIZED`，并无 `UNDETERMINED_INITIAL_STATE`。
- bug1：首次跑通，旧 jar 的钉扎伪影已排除（诊断 `$SP/d-bug1/DIAGNOSIS.md`）；语料 `$SP/cap/out-bug1/out/hdfs-17899-bug1` = `FINAL_READY`、1 缺口、3 个 blocker、4 个 valuation（1 timeout + 3 unsat），待终轮。
- 11741：首次通过 PLAN（`planned tasks: 88 by goal REGION_PATH_CLOSURE=84 TARGET_REACH_CLOSURE=4`）并进入 EXPLORE wave 0，被串行规则提前终止，无 `result.json`，待终轮完整跑。

### 待做（按顺序）

1. 完成并合入 `fix/fault-retain`（worktree `$SP/wt-fault`，2 个未提交改动，`ConcolicSmtComposer.java` +68 / `FaultRetainClosureTest.java` +69−6）：F1 契约自检 `FAULT_PARTITION_UNSPLIT`；F2 `FRONTIER_PINNED_UNSAT`（所有尝试的 unsat core 都与驱动自身钉子相交时不许报 unsat）；F3 故障保留语义（fault=true 时被 idle 的写者视为不存在，读回退到 LWW 前一版本或 INITIAL；传递依赖的下游分区随同一标记变为条件式；无前版本报 `FAULT_IDLE_NO_RETAINED_ARM`；manifest 按标记列出 retained (location, predecessor) 对）。诊断：`$SP/d-bug1/DIAGNOSIS.md`。
2. 17960 剩余 blocker：找出 `$SP/l1/out5` 中被截断的初始快照载体（`INITIAL_CONTAINER_SNAPSHOT_TRUNCATED` 行，产生于 `SymbolicPropagationClosure.java:1628`），若是类不在 `InitialContainerSnapshot.VM_VERSIONED_CLASSES`（`InitialContainerSnapshot.java:85`）/ VM `ContainerSupport::whole_state_selectable`（`containerSupport.cpp:153`）白名单则补齐（VM 需增量重建 + smoke 36/36），若超上限则调 `-Dcausynth.concolic.initial.snapshot.max`（`InitialContainerSnapshot.java:41`）；从模型叙述 17960 见证链（无序删除 → 重试的第二次 deleteSnapshot → `DirectorySnapshottableFeature.removeSnapshot` 容忍路径保留列表元素 → `SnapshotManager.deleteSnapshot` 无条件 `numSnapshots.getAndDecrement()`（`SnapshotManager.java:552`）→ `numSnapshots != 1` → throw）。
3. 六案串行终轮：`$SP/final/accept_final.sh`（默认 jar = `$SP/wt-stage/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar`，镜像 = `$SP/wt-l1/third_party/OpenJDK-Concolic-Execution-Engine/build/linux-x86_64-normal-zero-release/images/j2sdk-image`，输出 `summary.tsv` + 每案 `report/<case>/report.md`）；每案预算 ≤ 6 h（`CASE_TIMEOUT_SECONDS=21600`）；一次只跑一个战役。终轮同时验证：`run_engine.sh:1897` 硬链接共享 replay plan、声明即铸造（`declaredSymbolicRoot`，17960 的 `AtomicInteger value` 被强制铸造，见 `ConcolicInstrumentationSelections.java:479`）、`INITIAL_SNAPSHOT_SKIPPED` 行、17897 两条 flow 的 `CONSUMER_FIELD_READ` 路由（`ClaimPolicy.java:393`）。
4. bug3 语义待确认（需 owner 决定）：fault=false 若仍 sat 且见证是录制顺序的竞态（NN 滚 key 68，目标 DN 的刷新在 fatal 读之后），是否作为额外发现而非 blocker；若要求“无故障即 UNSAT”，需把目标 DN 的刷新 RPC 也纳入故障控制（实验层调整）。
5. 落地：写 `$SP/final/ACCEPTED` → `DRY=0 bash $SP/final/land.sh`（`git -C /opt/GraphChecker merge --ff-only refactor/flatten-handoff-next`；`mvn` 构建+测试；VM 镜像：staging `third_party` 树 `47bd04f7f` 与 L1 镜像同源（`wt-l1` 同树），可直接复制，否则 `third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_build_in_docker.sh`（Docker+GCC 6）；smoke 36/36；gate 复核 17960/bug3 sha 与 staging jar 一致）。
6. 结项报告：`$SP/final/REPORT_DRAFT.md` 填数（`$SP/final/LINECOUNT.md`：删冗余净 −739、模型完备性 +3227、门禁 +2141、测试 +6506；该表测于 `8c507bff7`，是 tip 的祖先。tip 上 `src/main` 为 78,104 行 vs 起点 `3d9355745` 的 71,522 行；`main..tip` 全树 210 files、+28696 / −13957）。

### Owner 待决

- VM `BigDecimal` 符号化路径 453 行（`symbolicBigDecimal.cpp` 370 + `.hpp` 83，Java 无消费者）：删或留。
- `DelegationKey#keyId`/`serialNo` 是否恢复为符号根（当前已移除，`src/main` 中仅余注释，因与目标快照常量无恒等关系导致虚假 SAT；恢复需把快照条目表达为同一根的表达式）。
- `edgeBindings` 行级规范化（需改 4 个 `experiments/hadoop/*/execute.sh`，收益约 1.5×）。
- `ConcolicRegionRuntime.ActiveRegion`（831 行，`ConcolicRegionRuntime.java:4975`，全文件 6617 行）拆分。
- 11741 无 DEK 过期检查读（bug 本身），不虚构声明行。

### 已知可选/遗留

- `callId`/`eventSeq` 证据字段；shell A3 项（`schedule_members.tsv`、flip solver own record）；增量 re-plan on topology delta。

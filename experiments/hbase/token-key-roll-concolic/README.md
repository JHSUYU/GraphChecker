# HBase token-key-roll concolic smoke case

This case targets the `Unknown master key for token` throw in
`AuthenticationTokenSecretManager.retrievePassword`. The supplied regression
test creates a token with an old key while a delayed ZooKeeper notification
leaves an issuer's cache stale. It then removes the old key on the leader
before the token expires and observes the explicit `InvalidToken` exception.

`prepare-analysis.sh` compiles one production class family, unedited, and the
regression test into `overlay/`, using Java 8 and the existing JDK 8 HBase
worktree. Neither HBase checkout is edited. The analysis scope is this class
family; the remaining HBase classes and dependencies are on the runtime
classpath. Its clock, `EnvironmentEdgeManager.currentTime()`, reaches the JVM
clock through an interface (`getDelegate().currentTime()`), which
`RootCatalog` does not follow (a delegate may be a manual edge): this case
has no clock root until it does.

The default classpath is the validated Java 8 classpath from the earlier HBase
pressure run. Set `HBASE_JDK8_CLASSPATH_FILE` to a replacement classpath file
if that `/tmp` artifact has moved.

Run from this directory with the bundled `jq` libraries on the loader path:

```bash
export PATH=/tmp/hbase-jq/usr/bin:$PATH
export LD_LIBRARY_PATH=/tmp/hbase-jq/usr/lib/x86_64-linux-gnu:${LD_LIBRARY_PATH:-}
./run.sh config
./run.sh validate
CAUSYNTH_TARGET_OCCURRENCE='workload/unregistered#epoch0/region/REGION.5f745bf3-665d-3cc2-9ebd-a839446f5935#2' \
  CAUSYNTH_CAMPAIGN_STOP_AFTER=IMPORT ./run.sh campaign
```

The selected target has a 23-task seed replay in one workload JVM. The
campaign has one worker and one planning iteration. It is a bounded service
smoke test; its truncated exploration is not a bug discovery completeness
claim. `CAUSYNTH_CAMPAIGN_STOP_AFTER=IMPORT` stops after the seed replay and
session import for a direct runtime pressure measurement. In the 2026-09-19
run, replay reached the target and produced 23 activations, 8 symbolic roots,
and 35 decisions. The import gate then rejected an empty target `phiTerm`;
resource measurements are valid, but the campaign did not complete.

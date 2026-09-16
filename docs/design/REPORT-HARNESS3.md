# REPORT-HARNESS3 — campaign_stop_after restored as a declared key (2026-09-14)

Branch refactor/d3-harness2, tip 394a9707a (parent 01c8a95b4). 3 files, +167/−1; run_engine.sh 2,857 → 2,887; no Java change; 52 @Test unchanged.

- run_engine.sh:63 key-table row `campaign_stop_after CAUSYNTH_CAMPAIGN_STOP_AFTER krp -` (default empty; env override only through apply_environment_overrides :189; the env name occurs once in the script).
- run_engine.sh:448-457 validate_config: only '' or IMPORT accepted, otherwise `die "campaign_stop_after must be empty or IMPORT: <v>"` (reached by `validate` and by PREFLIGHT).
- run_engine.sh:2746-2755 do_campaign: after IMPORT[n], `return 0` when campaign_stop_after=IMPORT; empty falls through to EXPLORE.
- README.md:130-138 documents the key.
- src/test/shell/run_engine_campaign_helpers_test.sh: STOP-1 (:784) table/load/override, STOP-2 (:810) validate accept/refuse, STOP-3 (:863) do_campaign stub stops at IMPORT[0] / runs to EMIT[0]; CONFIG-1 key count 41 → 42. Mutation-checked both ways.
- `bash -n`, shell test, `mvn -o test` (52/0/0), `git diff --check` all green. $SPN/d-runtime/seed_case.sh works unchanged.

Deferred (line numbers on 394a9707a, not fixed): DEAD-7 `campaign_fail CACHE` at :941,:949,:954,:959,:963,:968 and no INSTRUMENT/DECIDE/PREFLIGHT/SETUP labels; five `campaign_fail EMIT` in campaign_publish_iteration_manifest (:2036,:2049,:2053,:2065,:2069) fire from :2758-2759 (after EXPLORE, before COMPOSE); `target_reach` 7th TSV column read at :1588-1589 and :2029-2030 but never declared local (:1518, :2024) nor used; stale comment :108-111 above solver_timeout_ms :112 describes the deleted replay_task_budget.

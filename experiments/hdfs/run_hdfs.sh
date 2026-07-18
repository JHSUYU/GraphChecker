#!/bin/bash

set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE-$0}")"; pwd)
gc_dir=$(realpath "${script_dir}/../..")
conf="${script_dir}/conf/hdfs.properties"
# Long concolic campaigns may overlap read-only sub-agent tests.  Allow the
# caller to pin an immutable, versioned jar snapshot so a concurrent Maven
# package cannot replace the class path of an already-running JVM.
gc_jar="${CAUSYNTH_GC_JAR:-${gc_dir}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar}"

if [[ ! -f "${conf}" ]]; then
    echo "[ERROR] Config not found: ${conf}"
    exit 1
fi
source "${conf}"

graphchecker_java_bin="${GRAPH_CHECKER_JAVA:-${graphchecker_java_bin:-java}}"
hadoop_maven_bin="${GRAPH_CHECKER_MAVEN:-${hadoop_maven_bin:-mvn}}"
container_runtime_bin="${GRAPH_CHECKER_CONTAINER_RUNTIME:-${container_runtime_bin:-docker}}"
z3_bin="${CAUSYNTH_Z3:-${z3_bin:-z3}}"
protoc_bin="${CAUSYNTH_PROTOC:-${protoc_bin:-protoc}}"
configured_causynth_workload_test="${causynth_workload_test}"
causynth_workload_test="${CAUSYNTH_WORKLOAD_TEST:-${causynth_workload_test}}"

configured_tool_path() {
    local tool=$1
    if [[ "${tool}" == */* ]]; then
        # Preserve a configured symlink's basename and parent directory.
        # Some tools (notably Hadoop's protoc plugin) invoke a fixed command
        # name after inheriting PATH rather than executing this path directly.
        printf '%s\n' "${tool}"
    else
        command -v "${tool}"
    fi
}

run_container() {
    if [[ -n "${container_runtime_group:-}" \
            && " $(id -Gn) " != *" ${container_runtime_group} "* ]]; then
        local quoted_command
        printf -v quoted_command '%q ' "${container_runtime_bin}" "$@"
        sg "${container_runtime_group}" -c "${quoted_command}"
        return
    fi
    "${container_runtime_bin}" "$@"
}

with_configured_protoc() {
    local protoc_path protoc_dir
    protoc_path=$(configured_tool_path "${protoc_bin}")
    if [[ ! -x "${protoc_path}" ]]; then
        echo "[ERROR] Configured protoc is not executable: ${protoc_path}" >&2
        return 1
    fi
    protoc_dir=$(dirname "${protoc_path}")
    PATH="${protoc_dir}:${PATH}" "$@"
}

# Versioned experiments override active output/process locations explicitly;
# the checked-in v4 defaults and all historical artifact directories remain
# untouched.  The same overrides are inherited by campaign child executions.
causynth_output_dir="${CAUSYNTH_OUTPUT_DIR:-${causynth_output_dir}}"
instrumented_classes_path="${CAUSYNTH_INSTRUMENTED_CLASSES_PATH:-${instrumented_classes_path}}"
concolic_openjdk_dir="${CAUSYNTH_CONCOLIC_OPENJDK_DIR:-${concolic_openjdk_dir}}"

# Allow one-off audits to reuse a dedicated instrumented-class snapshot
# without editing the pinned experiment configuration or overwriting earlier
# replay classes.
concolic_classes_path="${CAUSYNTH_CONCOLIC_CLASSES_PATH:-${concolic_classes_path}}"

verify_hadoop_source() {
    local configured_root actual_root actual_commit pinned_source actual_hash
    if [[ "${CAUSYNTH_FRESH_HANDOFF_TEST_MODE:-false}" == "true" \
            && "${CAUSYNTH_FRESH_HANDOFF_SCHEDULER_FIXTURE:-false}" \
                == "true" ]]; then
        echo "[Source] explicit fresh-handoff fixture mode"
        return 0
    fi
    configured_root=$(realpath "${causynth_repo}")
    actual_root=$(git -C "${configured_root}" rev-parse --show-toplevel)
    actual_commit=$(git -C "${configured_root}" rev-parse HEAD)

    if [[ "${actual_root}" != "${configured_root}" ]]; then
        echo "[ERROR] Configured Hadoop path is not the repository root: ${configured_root}"
        echo "[ERROR] Git reports: ${actual_root}"
        exit 1
    fi
    if [[ "${actual_commit}" != "${causynth_expected_hadoop_commit}" ]]; then
        echo "[ERROR] Hadoop source revision mismatch."
        echo "[ERROR] Expected pre-HDFS-11741: ${causynth_expected_hadoop_commit}"
        echo "[ERROR] Actual:                  ${actual_commit}"
        exit 1
    fi
    pinned_source="${configured_root}/${causynth_hadoop_pinned_source}"
    if [[ ! -f "${pinned_source}" ]]; then
        echo "[ERROR] Pinned experimental HDFS source is missing: ${pinned_source}"
        exit 1
    fi
    actual_hash=$(shasum -a 256 "${pinned_source}" | awk '{print $1}')
    if [[ "${actual_hash}" != "${causynth_hadoop_pinned_source_sha256}" ]]; then
        echo "[ERROR] Experimental HDFS source fingerprint mismatch."
        echo "[ERROR] Mode:     ${causynth_hadoop_experiment_patch}"
        echo "[ERROR] Expected: ${causynth_hadoop_pinned_source_sha256}"
        echo "[ERROR] Actual:   ${actual_hash}"
        exit 1
    fi
    echo "[Source] Hadoop ${actual_commit} at ${actual_root}"
    echo "[Source] Experimental patch ${causynth_hadoop_experiment_patch} (${actual_hash})"
}

# Resolve and optionally attest the exact custom JVM used for concolic replay.
# Historical configurations may still point at an older development tree, so
# strict pinning is opt-in for those runs.  Every new campaign in this
# repository sets CAUSYNTH_REQUIRE_PINNED_OPENJDK=true together with all three
# expected hashes; a mismatch then fails before Docker starts.
verify_concolic_openjdk() {
    local image java_binary libjvm rt_jar expected_java expected_lib
    local expected_rt require_pinned
    image="${concolic_openjdk_dir}/build/linux-x86_64-normal-zero-release/images/j2sdk-image"
    java_binary="${image}/bin/java"
    libjvm="${image}/jre/lib/amd64/server/libjvm.so"
    rt_jar="${image}/jre/lib/rt.jar"
    if [[ ! -x "${java_binary}" || ! -f "${libjvm}" \
            || ! -f "${rt_jar}" ]]; then
        echo "[ERROR] Built concolic OpenJDK image is incomplete: ${image}" >&2
        exit 1
    fi
    concolic_java_sha256=$(shasum -a 256 "${java_binary}" | awk '{print $1}')
    concolic_libjvm_sha256=$(shasum -a 256 "${libjvm}" | awk '{print $1}')
    concolic_rt_sha256=$(shasum -a 256 "${rt_jar}" | awk '{print $1}')
    expected_java="${CAUSYNTH_CONCOLIC_OPENJDK_JAVA_SHA256:-}"
    expected_lib="${CAUSYNTH_CONCOLIC_OPENJDK_LIBJVM_SHA256:-}"
    expected_rt="${CAUSYNTH_CONCOLIC_OPENJDK_RT_SHA256:-}"
    require_pinned="${CAUSYNTH_REQUIRE_PINNED_OPENJDK:-false}"
    if [[ "${require_pinned}" == "true" \
            && ( -z "${expected_java}" || -z "${expected_lib}" \
                || -z "${expected_rt}" ) ]]; then
        echo "[ERROR] Strict concolic OpenJDK pinning requires java, libjvm, and rt.jar SHA-256 values" >&2
        exit 1
    fi
    if [[ -n "${expected_java}" \
            && "${concolic_java_sha256}" != "${expected_java}" ]]; then
        echo "[ERROR] Concolic OpenJDK java SHA-256 mismatch" >&2
        echo "[ERROR] Expected: ${expected_java}" >&2
        echo "[ERROR] Actual:   ${concolic_java_sha256}" >&2
        exit 1
    fi
    if [[ -n "${expected_lib}" \
            && "${concolic_libjvm_sha256}" != "${expected_lib}" ]]; then
        echo "[ERROR] Concolic OpenJDK libjvm SHA-256 mismatch" >&2
        echo "[ERROR] Expected: ${expected_lib}" >&2
        echo "[ERROR] Actual:   ${concolic_libjvm_sha256}" >&2
        exit 1
    fi
    if [[ -n "${expected_rt}" \
            && "${concolic_rt_sha256}" != "${expected_rt}" ]]; then
        echo "[ERROR] Concolic OpenJDK rt.jar SHA-256 mismatch" >&2
        echo "[ERROR] Expected: ${expected_rt}" >&2
        echo "[ERROR] Actual:   ${concolic_rt_sha256}" >&2
        exit 1
    fi
    echo "[Concolic JDK] java=${concolic_java_sha256} libjvm=${concolic_libjvm_sha256} rt.jar=${concolic_rt_sha256}"
}

# Compose every supplemental Soot application-class directory instead of
# letting a one-off environment override silently replace the configured
# hdfs-client classes.  Pinned HDFS experiments additionally require the two
# common-module support classes whose field/time bodies are part of the
# addKeys/removeExpiredKeys symbolic closure.
resolved_process_dirs() {
    local result="" raw entry canonical
    local -a entries=()
    for raw in "${causynth_extra_process_dirs:-}" \
            "${CAUSYNTH_ANALYSIS_SUPPORT_DIRS:-}" \
            "${CAUSYNTH_PROCESS_DIRS:-}"; do
        [[ -n "${raw}" ]] || continue
        IFS=':' read -r -a entries <<< "${raw}"
        for entry in "${entries[@]}"; do
            [[ -n "${entry}" ]] || continue
            if [[ ! -d "${entry}" ]]; then
                echo "[ERROR] Supplemental Soot process directory is missing: ${entry}" >&2
                return 1
            fi
            canonical=$(realpath "${entry}")
            case ":${result}:" in
                *":${canonical}:"*) ;;
                *) result="${result:+${result}:}${canonical}" ;;
            esac
        done
    done
    printf '%s' "${result}"
}

verify_required_analysis_support() {
    local process_dirs=$1 relative directory found
    local -a directories=()
    [[ "${CAUSYNTH_REQUIRE_HDFS_ANALYSIS_SUPPORT:-false}" == "true" ]] \
        || return 0
    IFS=':' read -r -a directories <<< "${process_dirs}"
    for relative in \
            org/apache/hadoop/security/token/delegation/DelegationKey.class \
            org/apache/hadoop/util/Time.class; do
        found=false
        for directory in "${directories[@]}"; do
            if [[ -f "${directory}/${relative}" ]]; then
                found=true
                break
            fi
        done
        if [[ "${found}" != "true" ]]; then
            echo "[ERROR] Required HDFS analysis support class is not an application class input: ${relative}" >&2
            return 1
        fi
    done
}

usage() {
    echo "Usage: ./run_hdfs.sh <command> [options]"
    echo ""
    echo "Commands:"
    echo "  build                         Build GraphChecker jar"
    echo "  build-hadoop                  Build required Hadoop modules"
    echo "  compile                       Compile HDFS and snapshot original classes"
    echo "  process                       Run the Causynth Soot transformer"
    echo "  verify-region-roots [catalog] Validate configured NN/DN maintenance roots"
    echo "  test [TestClass[#method]]     Run HDFS unit tests"
    echo "  run [TestClass[#method]]      process + test"
    echo "  schedule-concolic [test] [region] [activation]"
    echo "                                Build a graph-directed concolic schedule"
    echo "  schedule-concolic-capture [test] [region] [activation]"
    echo "                                Build a clean capture plan with no replay action"
    echo "  process-concolic <plan> [activation]"
    echo "                                Generate activation-specific replay classes"
    echo "  replay-concolic <plan> [activation] [test]"
    echo "                                Run one HDFS-owned test on the custom JDK"
    echo "  replay-concolic-batch <JSONL manifest>"
    echo "                                Process/replay isolated jobs in parallel, then import"
    echo "  import-concolic <plan> <results>"
    echo "                                Normalize the raw VM region result"
    echo "  campaign-concolic [test]      Close recursive captures and path flips"
    echo "  publish-campaign-handoff [test] [campaign-dir]"
    echo "                                Schedule and publish one immutable fresh target"
    echo "  verify-campaign-handoff <manifest>"
    echo "                                Revalidate every hash and exact target identity"
    echo "  hdfs-port-map [test]          Map HDFS names to generic region ports only"
    echo "  compose-smt [test]            Compose fatal and captured region relations"
    echo "  derive-producer-groups [test] Derive schema-2 producer roles and witnesses"
    echo "  verify-relationships [test]   Prove symbolic relationships by negated SMT checks"
    echo "  project-composed-model [test] Project bounded Z3 model to upstream inputs"
    echo "  validate-natural-replay [test] Validate an existing upstream-only replay"
    echo "  run-natural-replay [test]     Project, instrument, replay, and validate"
    echo "  restore                       Recompile HDFS to restore original classes"
    echo ""
    echo "Fresh compose/project/replay environment:"
    echo "  CAUSYNTH_CAMPAIGN_HANDOFF_MANIFEST    Completed immutable fresh handoff;"
    echo "                                         disables all target schedule guessing"
    echo "  CAUSYNTH_TARGET_SCHEDULE_DIR          Exact rebased target schedule;"
    echo "                                         otherwise exactly one is auto-resolved"
    echo "  CAUSYNTH_REBASE_CAMPAIGN_MANIFEST     Optional exact rebase authority check"
    echo "  CAUSYNTH_PRODUCER_GROUPS_CATALOG      Existing schema-2 catalog; otherwise"
    echo "                                         project derives one automatically"
    echo "  CAUSYNTH_PRODUCER_GROUP_OUTPUT_DIR    Fresh derived catalog output directory"
    echo "  CAUSYNTH_PRODUCER_SUMMARIES           Original merged summaries used by planner"
    echo "  CAUSYNTH_PRODUCER_ACTIVATIONS         Optional activation-path attestation; must"
    echo "                                         match target-schedule provenance"
    echo "  CAUSYNTH_PRODUCER_RUNTIME_EDGES       Optional runtime-edge-path attestation; must"
    echo "                                         match target-schedule provenance"
    echo "  CAUSYNTH_BOUNDED_UPSTREAM_REGIONS     Optional comma-separated composition bound;"
    echo "                                         otherwise scope is discovered semantically"
    echo "  CAUSYNTH_UPSTREAM_REGION              Required in single-producer mode"
    echo "  CAUSYNTH_UPSTREAM_ACTIVATIONS         Required in single-producer mode"
    echo "  CAUSYNTH_BROADCAST_ACTIVATIONS        Single-mode runtime activation catalog"
    echo "  CAUSYNTH_EXPECTED_BROADCAST_CANDIDATES Required positive single-mode bound"
    echo "  CAUSYNTH_TARGET_SUMMARIES             Validated exact-target summaries"
    echo "  CAUSYNTH_COMPOSITION_SUMMARIES        Required exact merged summaries used"
    echo "                                         by composition (no directory guessing)"
    echo "  CAUSYNTH_PROJECTION_SUMMARIES         Single-mode raw summaries only; schema-2"
    echo "                                         projection always uses enriched summaries"
    echo "  CAUSYNTH_COMPOSITION_OUTPUT_DIR       Fresh composition output directory"
    echo "  CAUSYNTH_NATURAL_REPLAY_OUTPUT_DIR    Fresh projection/replay output directory"
    echo "  CAUSYNTH_NATURAL_REPLAY_CLASSES_PATH  Fresh path below natural output only"
    echo "  CAUSYNTH_NATURAL_REPLAY_STATIC_OUTPUT_DIR Fresh path below natural output only"
    echo ""
    echo "Batch JSONL schema (one object per independent activation):"
    echo '  {"schemaVersion":2,"jobId":"...","plan":"/abs/.../scheduled_activation_plan.jsonl",'
    echo '   "activationId":"ACT...","outputDir":"/abs/plan-parent",'
    echo '   "classesDir":"/abs/output/classes","staticOutputDir":"/abs/output/static",'
    echo '   "regions":"/abs/static/symbolic_regions.jsonl","regionsSha256":"<sha256>"}'
    echo "  The sibling schedule_input_provenance.json must bind plan and regions hashes"
    echo "  Optional per-job: hadoopTargetDir, workDir; both must be below outputDir"
    echo "  Parallelism: CAUSYNTH_HDFS_CONCOLIC_PARALLELISM (or conf default)"
}

timing() {
    local label=$1
    shift
    local start=$SECONDS
    "$@"
    echo "[Profiler] ${label} took $((SECONDS - start))s"
}

do_build() {
    "${hadoop_maven_bin}" -f "${gc_dir}/pom.xml" clean package -DskipTests
}

do_build_hadoop() {
    verify_hadoop_source
    local hadoop_root
    hadoop_root=$(realpath "${hdfs_dir}/../..")
    with_configured_protoc "${hadoop_maven_bin}" -f "${hadoop_root}/pom.xml" install -DskipTests -Pdist \
        -pl hadoop-common-project/hadoop-common,\
hadoop-common-project/hadoop-kms,\
hadoop-hdfs-project/hadoop-hdfs-client,\
hadoop-hdfs-project/hadoop-hdfs \
        -am
}

do_compile() {
    verify_hadoop_source
    # Soot places selected hdfs-client classes in the HDFS output directory.
    # A non-clean incremental javac can then resolve the transformed outer
    # class instead of the dependency jar and lose nested-class metadata.
    with_configured_protoc "${hadoop_maven_bin}" -f "${hdfs_dir}/pom.xml" clean package -DskipTests
    rm -rf "${system_classes_path}"
    mkdir -p "${system_classes_path}"
    rsync -a "${hdfs_dir}/target/classes/" "${system_classes_path}/"
}

verify_region_root_spec() {
    local catalog=$1
    local label=$2
    local root_method=$3
    local required_methods=$4
    local jq_filter
    jq_filter='($required | split("|") | map(select(length > 0))) as $need
      | select(.rootMethod == $root
          and ((.methods? // null) | type) == "array")
      | . as $region
      | select($need | all(. as $method
          | (($region.methods | index($method)) != null)))'

    local matches
    if ! matches=$(jq -r --arg root "${root_method}" \
            --arg required "${required_methods}" \
            "${jq_filter} | .regionId" "${catalog}"); then
        echo "[ERROR] Invalid static region-root catalog: ${catalog}" >&2
        return 1
    fi
    if [[ -n "${matches}" ]]; then
        matches=${matches//$'\n'/,}
        echo "[Static region root] ${label}: ${matches}"
        return 0
    fi

    echo "[ERROR] No ${label} region has the configured root and all required methods" >&2
    echo "[ERROR] Root: ${root_method}" >&2
    echo "[ERROR] Required: ${required_methods}" >&2
    jq -rc --arg root "${root_method}" --arg required "${required_methods}" '
        ($required | split("|") | map(select(length > 0))) as $need
        | select(.rootMethod == $root)
        | . as $region
        | {regionId, missing:($need - ($region.methods // []))}' \
        "${catalog}" >&2
    return 1
}

verify_hdfs_region_roots() {
    local requested_catalog="${1:-}"
    local enabled="${CAUSYNTH_HDFS_REGION_ROOT_GATE_ENABLED:-${causynth_hdfs_region_root_gate_enabled:-true}}"
    if [[ "${enabled}" != "true" ]]; then
        echo "[Static region root] validation disabled by configuration"
        return 0
    fi

    local configured_catalog catalog
    configured_catalog="${CAUSYNTH_HDFS_REGION_ROOT_GATE_FILE:-${causynth_hdfs_region_root_gate_file:-symbolic_regions.jsonl}}"
    if [[ -n "${requested_catalog}" ]]; then
        catalog="${requested_catalog}"
    elif [[ "${configured_catalog}" = /* ]]; then
        catalog="${configured_catalog}"
    else
        catalog="${causynth_output_dir}/${configured_catalog}"
    fi
    if [[ ! -s "${catalog}" ]]; then
        echo "[ERROR] Static region-root catalog is missing or empty: ${catalog}" >&2
        return 1
    fi

    local dn_root dn_methods nn_root nn_methods
    dn_root="${CAUSYNTH_HDFS_DN_REGION_ROOT_METHOD:-${causynth_hdfs_dn_region_root_method:-}}"
    dn_methods="${CAUSYNTH_HDFS_DN_REGION_REQUIRED_METHODS:-${causynth_hdfs_dn_region_required_methods:-}}"
    nn_root="${CAUSYNTH_HDFS_NN_REGION_ROOT_METHOD:-${causynth_hdfs_nn_region_root_method:-}}"
    nn_methods="${CAUSYNTH_HDFS_NN_REGION_REQUIRED_METHODS:-${causynth_hdfs_nn_region_required_methods:-}}"
    if [[ -z "${dn_root}" || -z "${dn_methods}" \
            || -z "${nn_root}" || -z "${nn_methods}" ]]; then
        echo "[ERROR] HDFS region-root gate signatures are incomplete in ${conf}" >&2
        return 1
    fi

    verify_region_root_spec "${catalog}" "NN-to-DN block-key snapshot" \
        "${dn_root}" "${dn_methods}"
    verify_region_root_spec "${catalog}" "NN block-key rotation" \
        "${nn_root}" "${nn_methods}"
}

do_process() {
    verify_hadoop_source
    if [[ ! -f "${gc_jar}" ]]; then
        echo "[ERROR] GraphChecker jar not found: ${gc_jar}"
        echo "Run './run_hdfs.sh build' first."
        exit 1
    fi
    if [[ ! -d "${system_classes_path}" ]]; then
        echo "[ERROR] Original classes snapshot not found: ${system_classes_path}"
        echo "Run './run_hdfs.sh compile' first."
        exit 1
    fi

    rm -rf "${instrumented_classes_path}"
    mkdir -p "${instrumented_classes_path}"

    local process_dirs
    process_dirs=$(resolved_process_dirs)
    verify_required_analysis_support "${process_dirs}"
    local properties=(
        -Dcausynth.instrument.trace=true
        -Dcausynth.output.dir="${causynth_output_dir}"
        -Dcausynth.coverage.strict="${causynth_coverage_strict:-true}"
        -Dcausynth.static.max.methods="${causynth_static_max_methods:-1000}"
        -Dcausynth.static.max.edges="${causynth_static_max_edges:-50000}"
    )
    if [[ -n "${process_dirs}" ]]; then
        properties+=(-Dcausynth.process.dirs="${process_dirs}")
    fi
    "${graphchecker_java_bin}" "${properties[@]}" \
        -cp "${gc_jar}:${java_class_path}" \
        edu.uva.liftlab.graphchecker.GraphCheckerMain \
        -i "${system_classes_path}" \
        -x "${java_class_path}" \
        -C "${conf}" \
        -o "${instrumented_classes_path}"

    # Guard against accidentally treating removeExpiredKeys() as a standalone
    # region entry.  Both maintenance slices must remain rooted at the actual
    # long-running heartbeat actors before this process output is accepted.
    verify_hdfs_region_roots

    local graphchecker_jar_sha256
    graphchecker_jar_sha256=$(shasum -a 256 "${gc_jar}" | awk '{print $1}')
    jq -n \
        --arg mode "PINNED_STATIC_PROCESS_INPUTS" \
        --arg graphCheckerJar "$(realpath "${gc_jar}")" \
        --arg graphCheckerJarSha256 "${graphchecker_jar_sha256}" \
        --arg originalClasses "$(realpath "${system_classes_path}")" \
        --arg supplementalProcessDirs "${process_dirs}" \
        --arg requireHdfsAnalysisSupport \
            "${CAUSYNTH_REQUIRE_HDFS_ANALYSIS_SUPPORT:-false}" \
        '{schemaVersion:1, mode:$mode,
          graphCheckerJar:$graphCheckerJar,
          graphCheckerJarSha256:$graphCheckerJarSha256,
          originalClasses:$originalClasses,
          supplementalProcessDirs:($supplementalProcessDirs
            | split(":") | map(select(length > 0))),
          requireHdfsAnalysisSupport:
            ($requireHdfsAnalysisSupport == "true"), complete:true}' \
        > "${causynth_output_dir}/static_process_provenance.json"

    # Rich field/map tracing shares the exact code-position and region runtime
    # helpers used by concolic replay.  Keep the complete runtime dependency
    # family beside normally instrumented Hadoop classes as well; extracting
    # only CausynthTraceRecorder leaves a fresh process output unloadable.
    while IFS= read -r runtime_class; do
        (cd "${instrumented_classes_path}" && jar xf "${gc_jar}" "${runtime_class}")
    done < <(jar tf "${gc_jar}" | grep -E \
        '^edu/uva/liftlab/graphchecker/(runtime/(ConcolicRegionRuntime|CausynthTraceRecorder|RuntimeRegionPlanner)|concolic/ConcolicCodePosition)')

    find "${hdfs_dir}/target/classes" -name "*.class" -delete
    cp -r "${instrumented_classes_path}/." "${hdfs_dir}/target/classes/"
}

safe_test_name() {
    printf "%s" "$1" | tr -c 'A-Za-z0-9._-' '_'
}

do_schedule_concolic() {
    verify_hadoop_source
    local test_name="${1:-${causynth_workload_test}}"
    local region_id="${2:-${CAUSYNTH_SCHEDULE_REGION_ID:-}}"
    local activation_id="${3:-${CAUSYNTH_SCHEDULE_ACTIVATION_ID:-}}"
    local safe_name trace_dir schedule_dir capture_dir region_suffix
    local activation_plan edge_validations schedule_summaries
    local schedule_regions schedule_static_graph schedule_path_records
    local schedule_root
    if [[ -z "${region_id}" ]]; then
        echo "[ERROR] schedule-concolic requires a runtime-selected region argument or CAUSYNTH_SCHEDULE_REGION_ID" >&2
        return 1
    fi
    safe_name=$(safe_test_name "${test_name}")
    trace_dir="${causynth_output_dir}/unit-test-graphs/${safe_name}"
    region_suffix=$(printf "%s" "${region_id}" | tr -c 'A-Za-z0-9_-' '_')
    schedule_dir="${CAUSYNTH_SCHEDULE_OUTPUT_DIR:-${trace_dir}/concolic-schedule-${region_suffix}}"
    capture_dir="${trace_dir}/concolic-capture-${region_suffix}"
    activation_plan="${CAUSYNTH_SCHEDULE_ACTIVATION_PLAN:-${trace_dir}/concolic_activation_plan.jsonl}"
    edge_validations="${CAUSYNTH_SCHEDULE_EDGE_VALIDATIONS:-${trace_dir}/runtime_region_edge_validation.jsonl}"
    schedule_summaries="${CAUSYNTH_SCHEDULE_SUMMARIES:-}"
    schedule_regions="${CAUSYNTH_SCHEDULE_REGIONS:-${causynth_output_dir}/symbolic_regions.jsonl}"
    schedule_static_graph="${CAUSYNTH_SCHEDULE_STATIC_GRAPH:-${causynth_output_dir}/static_dataflow_edges.jsonl}"
    schedule_path_records="${CAUSYNTH_SCHEDULE_PATH_RECORDS:-}"
    schedule_root="${CAUSYNTH_SCHEDULE_ROOT:-}"
    if [[ "${CAUSYNTH_CAPTURE_ONLY:-false}" == "true" ]]; then
        schedule_dir="${CAUSYNTH_SCHEDULE_OUTPUT_DIR:-${capture_dir}}"
    fi
    for schedule_input in "${activation_plan}" "${edge_validations}" \
            "${schedule_regions}" "${schedule_static_graph}"; do
        if [[ ! -s "${schedule_input}" ]]; then
            echo "[ERROR] Concolic schedule input is missing or empty: ${schedule_input}" >&2
            exit 1
        fi
    done

    local args=(
        --regions "${schedule_regions}"
        --activation-plan "${activation_plan}"
        --edge-validations "${edge_validations}"
        --static-graph "${schedule_static_graph}"
        --output-dir "${schedule_dir}"
        --region-id "${region_id}"
        --max-jobs 1
    )
    if [[ -n "${schedule_path_records}" ]]; then
        if [[ ! -f "${schedule_path_records}" ]]; then
            echo "[ERROR] Schedule path records are missing: ${schedule_path_records}" >&2
            return 1
        fi
        args+=(--path-records "${schedule_path_records}")
    fi
    if [[ -n "${activation_id}" ]]; then
        args+=(--activation-id "${activation_id}")
    fi
    if [[ "${CAUSYNTH_CAPTURE_ONLY:-false}" == "true" ]]; then
        args+=(--capture-only)
    else
        if [[ -z "${schedule_summaries}" \
                && -s "${capture_dir}/concolic_region_summaries.jsonl" ]]; then
            schedule_summaries="${capture_dir}/concolic_region_summaries.jsonl"
        elif [[ -z "${schedule_summaries}" \
                && -s "${schedule_dir}/concolic_region_summaries.jsonl" ]]; then
            schedule_summaries="${schedule_dir}/concolic_region_summaries.jsonl"
        elif [[ -z "${schedule_summaries}" \
                && -s "${trace_dir}/concolic_region_summaries.jsonl" ]]; then
            schedule_summaries="${trace_dir}/concolic_region_summaries.jsonl"
        fi
    fi
    if [[ -n "${schedule_summaries}" ]]; then
        if [[ ! -s "${schedule_summaries}" ]]; then
            echo "[ERROR] Requested schedule summaries are missing or empty: ${schedule_summaries}" >&2
            exit 1
        fi
        args+=(--summaries "${schedule_summaries}")
    fi
    if [[ "${CAUSYNTH_FORCE_BRANCH_VALIDATION:-false}" == "true" ]]; then
        args+=(--force-branch-validation)
    fi

    if [[ "${CAUSYNTH_FRESH_HANDOFF_SCHEDULER_FIXTURE:-false}" == "true" ]]; then
        if [[ "${CAUSYNTH_FRESH_HANDOFF_TEST_MODE:-false}" != "true" \
                || -z "${schedule_root}" || -z "${activation_id}" ]]; then
            echo "[ERROR] Fresh handoff scheduler fixture is test-only and requires one exact root/activation" >&2
            return 1
        fi
        case "$(realpath -m "${schedule_dir}")" in
            "${gc_dir}"/target/causynth-handoff-fixture.*/*) ;;
            *)
                echo "[ERROR] Fresh handoff scheduler fixture output must stay in a disposable target fixture" >&2
                return 1
                ;;
        esac
        mkdir -p "${schedule_dir}"
        cp "${schedule_root}" "${schedule_dir}/branch_queries.jsonl"
        jq -c --arg activation "${activation_id}" \
            --arg region "${region_id}" '
            select(.activationId == $activation and .regionId == $region)
            | {activationId,regionId,regionInstanceId,
               activationBundleMemberRole:"PRIMARY"}' \
            "${schedule_root}" \
            > "${schedule_dir}/scheduled_activation_plan.jsonl"
        jq -nc '{}' > "${schedule_dir}/concolic_schedule.jsonl"
        jq -n '{}' > "${schedule_dir}/symbolic_merge_plan.json"
        jq -n '{}' > "${schedule_dir}/concolic_scheduler_summary.json"
    else
        "${graphchecker_java_bin}" -cp "${gc_jar}" \
            edu.uva.liftlab.graphchecker.concolic.ConcolicScheduler \
            "${args[@]}"
    fi
    local graphchecker_jar_sha activation_plan_sha edge_validations_sha
    local regions_sha static_graph_sha summaries_sha path_records_sha
    local root_sha branch_queries_sha scheduled_plan_sha merge_plan_sha
    local concolic_schedule_sha scheduler_summary_sha provenance_authority
    local selected_activation_id selected_region_instance_id
    local selected_primary_count
    graphchecker_jar_sha=$(shasum -a 256 "${gc_jar}" | awk '{print $1}')
    activation_plan_sha=$(shasum -a 256 "${activation_plan}" | awk '{print $1}')
    edge_validations_sha=$(shasum -a 256 "${edge_validations}" | awk '{print $1}')
    regions_sha=$(shasum -a 256 "${schedule_regions}" | awk '{print $1}')
    static_graph_sha=$(shasum -a 256 "${schedule_static_graph}" | awk '{print $1}')
    summaries_sha=""
    path_records_sha=""
    root_sha=""
    if [[ -n "${schedule_summaries}" ]]; then
        summaries_sha=$(shasum -a 256 "${schedule_summaries}" | awk '{print $1}')
    fi
    if [[ -n "${schedule_path_records}" ]]; then
        path_records_sha=$(shasum -a 256 "${schedule_path_records}" | awk '{print $1}')
    fi
    if [[ -n "${schedule_root}" ]]; then
        require_nonempty_input "exact campaign target root" "${schedule_root}"
        root_sha=$(shasum -a 256 "${schedule_root}" | awk '{print $1}')
    fi
    for schedule_output in \
            "${schedule_dir}/concolic_schedule.jsonl" \
            "${schedule_dir}/scheduled_activation_plan.jsonl" \
            "${schedule_dir}/branch_queries.jsonl" \
            "${schedule_dir}/symbolic_merge_plan.json" \
            "${schedule_dir}/concolic_scheduler_summary.json"; do
        if [[ ! -f "${schedule_output}" ]]; then
            echo "[ERROR] Scheduler output is missing: ${schedule_output}" >&2
            return 1
        fi
    done
    branch_queries_sha=$(shasum -a 256 \
        "${schedule_dir}/branch_queries.jsonl" | awk '{print $1}')
    scheduled_plan_sha=$(shasum -a 256 \
        "${schedule_dir}/scheduled_activation_plan.jsonl" | awk '{print $1}')
    merge_plan_sha=$(shasum -a 256 \
        "${schedule_dir}/symbolic_merge_plan.json" | awk '{print $1}')
    concolic_schedule_sha=$(shasum -a 256 \
        "${schedule_dir}/concolic_schedule.jsonl" | awk '{print $1}')
    scheduler_summary_sha=$(shasum -a 256 \
        "${schedule_dir}/concolic_scheduler_summary.json" | awk '{print $1}')
    provenance_authority="DIRECT_HASHED_SCHEDULER_INPUTS_AND_OUTPUTS"
    if [[ -n "${schedule_root}" && -n "${schedule_summaries}" \
            && -n "${schedule_path_records}" ]]; then
        provenance_authority="IMMUTABLE_CAMPAIGN_GENERATION_FRESH_TARGET_SCHEDULE"
    fi
    selected_primary_count=$(jq -r -s --arg region "${region_id}" \
        --arg requested "${activation_id}" '
        [.[] | select(.regionId == $region
            and ($requested == "" or .activationId == $requested)
            and ((.activationBundleMemberRole // "PRIMARY") == "PRIMARY"))]
        | length' "${schedule_dir}/scheduled_activation_plan.jsonl")
    if [[ "${selected_primary_count}" -ne 1 ]]; then
        echo "[ERROR] Scheduler did not emit one exact primary activation for provenance: region=${region_id} requested=${activation_id}" >&2
        return 1
    fi
    selected_activation_id=$(jq -r -s --arg region "${region_id}" \
        --arg requested "${activation_id}" '
        [.[] | select(.regionId == $region
            and ($requested == "" or .activationId == $requested)
            and ((.activationBundleMemberRole // "PRIMARY") == "PRIMARY"))]
        | .[0].activationId' \
        "${schedule_dir}/scheduled_activation_plan.jsonl")
    selected_region_instance_id=$(jq -r -s --arg region "${region_id}" \
        --arg requested "${activation_id}" '
        [.[] | select(.regionId == $region
            and ($requested == "" or .activationId == $requested)
            and ((.activationBundleMemberRole // "PRIMARY") == "PRIMARY"))]
        | .[0].regionInstanceId' \
        "${schedule_dir}/scheduled_activation_plan.jsonl")
    if [[ -z "${selected_activation_id}" \
            || -z "${selected_region_instance_id}" ]]; then
        echo "[ERROR] Scheduler primary activation lacks exact identity provenance" >&2
        return 1
    fi
    jq -n \
        --arg graphCheckerJar "$(realpath "${gc_jar}")" \
        --arg graphCheckerJarSha256 "${graphchecker_jar_sha}" \
        --arg activationPlan "$(realpath "${activation_plan}")" \
        --arg activationPlanSha256 "${activation_plan_sha}" \
        --arg edgeValidations "$(realpath "${edge_validations}")" \
        --arg edgeValidationsSha256 "${edge_validations_sha}" \
        --arg regions "$(realpath "${schedule_regions}")" \
        --arg regionsSha256 "${regions_sha}" \
        --arg staticGraph "$(realpath "${schedule_static_graph}")" \
        --arg staticGraphSha256 "${static_graph_sha}" \
        --arg summaries "${schedule_summaries:+$(realpath "${schedule_summaries}")}" \
        --arg summariesSha256 "${summaries_sha}" \
        --arg pathRecords "${schedule_path_records:+$(realpath "${schedule_path_records}")}" \
        --arg pathRecordsSha256 "${path_records_sha}" \
        --arg exactTargetRoot "${schedule_root:+$(realpath "${schedule_root}")}" \
        --arg exactTargetRootSha256 "${root_sha}" \
        --arg concolicSchedule "$(realpath "${schedule_dir}/concolic_schedule.jsonl")" \
        --arg concolicScheduleSha256 "${concolic_schedule_sha}" \
        --arg scheduledActivationPlan "$(realpath "${schedule_dir}/scheduled_activation_plan.jsonl")" \
        --arg scheduledActivationPlanSha256 "${scheduled_plan_sha}" \
        --arg branchQueries "$(realpath "${schedule_dir}/branch_queries.jsonl")" \
        --arg branchQueriesSha256 "${branch_queries_sha}" \
        --arg symbolicMergePlan "$(realpath "${schedule_dir}/symbolic_merge_plan.json")" \
        --arg symbolicMergePlanSha256 "${merge_plan_sha}" \
        --arg schedulerSummary "$(realpath "${schedule_dir}/concolic_scheduler_summary.json")" \
        --arg schedulerSummarySha256 "${scheduler_summary_sha}" \
        --arg authority "${provenance_authority}" \
        --arg requestedActivationId "${activation_id}" \
        --arg activationId "${selected_activation_id}" \
        --arg regionId "${region_id}" \
        --arg regionInstanceId "${selected_region_instance_id}" \
        '{schemaVersion:2, kind:"CONCOLIC_SCHEDULE_INPUT_PROVENANCE",
          authority:$authority,
          graphCheckerJar:$graphCheckerJar,
          graphCheckerJarSha256:$graphCheckerJarSha256,
          activationPlan:$activationPlan,
          activationPlanSha256:$activationPlanSha256,
          edgeValidations:$edgeValidations,
          edgeValidationsSha256:$edgeValidationsSha256,
          regions:$regions, regionsSha256:$regionsSha256,
          staticGraph:$staticGraph, staticGraphSha256:$staticGraphSha256,
          summaries:$summaries, summariesSha256:$summariesSha256,
          pathRecords:$pathRecords, pathRecordsSha256:$pathRecordsSha256,
          exactTargetRoot:$exactTargetRoot,
          exactTargetRootSha256:$exactTargetRootSha256,
          concolicSchedule:$concolicSchedule,
          concolicScheduleSha256:$concolicScheduleSha256,
          scheduledActivationPlan:$scheduledActivationPlan,
          scheduledActivationPlanSha256:$scheduledActivationPlanSha256,
          branchQueries:$branchQueries,
          branchQueriesSha256:$branchQueriesSha256,
          symbolicMergePlan:$symbolicMergePlan,
          symbolicMergePlanSha256:$symbolicMergePlanSha256,
          schedulerSummary:$schedulerSummary,
          schedulerSummarySha256:$schedulerSummarySha256,
          requestedActivationId:$requestedActivationId,
          activationId:$activationId, regionId:$regionId,
          regionInstanceId:$regionInstanceId, complete:true}' \
        > "${schedule_dir}/schedule_input_provenance.json"
    echo "[Concolic] schedule: ${schedule_dir}/concolic_schedule.jsonl"
    echo "[Concolic] activation plan: ${schedule_dir}/scheduled_activation_plan.jsonl"
}

activation_plan_requires_all() {
    local activation_plan=$1
    jq -e -s 'any(.[];
        .activationSelectionRequired == "ALL"
        or ((.activationBundleSize // 0) > 1))' \
        "${activation_plan}" >/dev/null
}

do_process_concolic() {
    verify_hadoop_source
    local activation_plan="${1:-}"
    local activation_id="${2:-}"
    if [[ -z "${activation_plan}" || ! -f "${activation_plan}" ]]; then
        echo "[ERROR] Scheduled activation plan not found: ${activation_plan}"
        exit 1
    fi
    if activation_plan_requires_all "${activation_plan}"; then
        if [[ -n "${activation_id}" && "${activation_id}" != "ALL" ]]; then
            echo "[Concolic] activation bundle requires ALL; overriding ${activation_id}"
        fi
        activation_id=""
    elif [[ "${activation_id}" == "ALL" ]]; then
        activation_id=""
    fi
    if [[ ! -f "${gc_jar}" || ! -d "${system_classes_path}" ]]; then
        echo "[ERROR] Build GraphChecker and snapshot original HDFS classes first."
        exit 1
    fi

    rm -rf "${concolic_classes_path}"
    mkdir -p "${concolic_classes_path}"
    local process_dirs
    process_dirs=$(resolved_process_dirs)
    verify_required_analysis_support "${process_dirs}"
    local properties=(
        -Dcausynth.instrument.concolic=true
        -Dcausynth.concolic.activation.plan="$(realpath "${activation_plan}")"
        -Dcausynth.output.dir="${CAUSYNTH_CONCOLIC_STATIC_OUTPUT_DIR:-${causynth_output_dir}/concolic-replay-static}"
        -Dcausynth.coverage.strict="${causynth_coverage_strict:-true}"
        -Dcausynth.static.max.methods="${causynth_static_max_methods:-1000}"
        -Dcausynth.static.max.edges="${causynth_static_max_edges:-50000}"
    )
    if [[ -n "${process_dirs}" ]]; then
        properties+=(-Dcausynth.process.dirs="${process_dirs}")
    fi
    if [[ -n "${CAUSYNTH_CAMPAIGN_DISCOVERED_ACTIVATIONS:-}" \
            || -n "${CAUSYNTH_CAMPAIGN_DISCOVERED_EDGES:-}" ]]; then
        if [[ -z "${CAUSYNTH_CAMPAIGN_DISCOVERED_ACTIVATIONS:-}" \
                || -z "${CAUSYNTH_CAMPAIGN_DISCOVERED_EDGES:-}" ]]; then
            echo "[ERROR] Campaign discovery requires both activation and edge output paths"
            exit 1
        fi
        # The same application execution must be both concolically observed
        # and richly traced.  Dynamic activations discovered after a branch
        # flip are otherwise invisible to the next campaign iteration.
        properties+=(-Dcausynth.instrument.trace=true)
    fi
    if [[ -n "${activation_id}" ]]; then
        properties+=(-Dcausynth.concolic.activation.id="${activation_id}")
    fi
    "${graphchecker_java_bin}" -Xmx4g "${properties[@]}" \
        -cp "${gc_jar}:${java_class_path}" \
        edu.uva.liftlab.graphchecker.GraphCheckerMain \
        -i "${system_classes_path}" \
        -x "${java_class_path}" \
        -C "${conf}" \
        -o "${concolic_classes_path}"

    # Keep runtime-only dependencies beside the instrumented Hadoop classes.
    # ConcolicRegionRuntime intentionally shares code-position normalization
    # with the offline importer, so both class families are required at replay.
    while IFS= read -r runtime_class; do
        (cd "${concolic_classes_path}" && jar xf "${gc_jar}" "${runtime_class}")
    done < <(jar tf "${gc_jar}" | grep -E \
        '^edu/uva/liftlab/graphchecker/(runtime/(ConcolicRegionRuntime|CausynthTraceRecorder|RuntimeRegionPlanner)|concolic/ConcolicCodePosition)')
    echo "[Concolic] replay classes: ${concolic_classes_path}"
}

workspace_container_path() {
    local absolute
    absolute=$(realpath "$1")
    case "${absolute}" in
        "${gc_dir}"/*)
            printf "/graphchecker/%s" "${absolute#${gc_dir}/}"
            ;;
        *)
            echo "[ERROR] Concolic artifacts must be inside ${gc_dir}: ${absolute}" >&2
            exit 1
            ;;
    esac
}

do_replay_concolic() {
    verify_hadoop_source
    local activation_plan="${1:-}"
    local activation_id="${2:-${CAUSYNTH_REPLAY_ACTIVATION_ID:-}}"
    local test_name="${3:-${causynth_workload_test}}"
    if [[ -z "${activation_plan}" || ! -f "${activation_plan}" ]]; then
        echo "[ERROR] Scheduled activation plan not found: ${activation_plan}"
        exit 1
    fi
    if activation_plan_requires_all "${activation_plan}"; then
        if [[ -n "${activation_id}" && "${activation_id}" != "ALL" ]]; then
            echo "[Concolic] activation bundle requires ALL; overriding ${activation_id}"
        fi
        activation_id=""
    elif [[ "${activation_id}" == "ALL" ]]; then
        activation_id=""
    fi
    if [[ ! -d "${concolic_classes_path}" ]]; then
        echo "[ERROR] Replay classes not found. Run process-concolic first."
        exit 1
    fi
    verify_concolic_openjdk
    local graphchecker_jar_sha256
    graphchecker_jar_sha256=$(shasum -a 256 "${gc_jar}" | awk '{print $1}')
    if [[ ! -x "${concolic_maven_dir}/bin/mvn" ]]; then
        echo "[ERROR] Maven distribution not found: ${concolic_maven_dir}"
        exit 1
    fi

    local plan_in_container result_file result_in_container log_dir arg_line
    local hadoop_repo_mount replay_target_dir replay_work_dir
    local replay_work_in_container
    local surefire_test_selector test_classes_overlay
    local replay_status=0
    local -a discovery_properties=()
    local -a isolated_target_mount=()
    local -a isolated_test_properties=()
    local -a test_classes_mount=()
    local -a container_user_args=()
    plan_in_container=$(workspace_container_path "${activation_plan}")
    result_file="$(dirname "$(realpath "${activation_plan}")")/concolic_region_results.jsonl"
    rm -f "${result_file}"
    result_in_container=$(workspace_container_path "${result_file}")
    log_dir="/graphchecker/target/hdfs-concolic-test-logs"
    hadoop_repo_mount="${causynth_repo}:/hadoop"
    replay_target_dir="${CAUSYNTH_REPLAY_HDFS_TARGET_DIR:-}"
    replay_work_dir="${CAUSYNTH_REPLAY_WORK_DIR:-}"
    if [[ -n "${replay_target_dir}" || -n "${replay_work_dir}" ]]; then
        if [[ -z "${replay_target_dir}" || ! -d "${replay_target_dir}" \
                || -z "${replay_work_dir}" ]]; then
            echo "[ERROR] Isolated replay requires an existing target snapshot and a work directory" >&2
            exit 1
        fi
        replay_target_dir=$(realpath "${replay_target_dir}")
        require_workspace_output_path "isolated HDFS target snapshot" \
            "${replay_target_dir}"
        replay_work_dir=$(realpath -m "${replay_work_dir}")
        require_workspace_output_path "isolated HDFS replay work directory" \
            "${replay_work_dir}"
        mkdir -p "${replay_work_dir}/logs" \
            "${replay_work_dir}/test-build-data" \
            "${replay_work_dir}/test-build-dir" \
            "${replay_work_dir}/shared-data" \
            "${replay_work_dir}/hadoop-tmp" \
            "${replay_work_dir}/java-tmp"
        replay_work_in_container=$(workspace_container_path \
            "${replay_work_dir}")
        log_dir="${replay_work_in_container}/logs"
        # The source checkout is read-only in batch mode.  The nested target
        # mount owns every Maven/Surefire write, while explicit test and tmp
        # properties isolate MiniDFSCluster state outside that target too.
        hadoop_repo_mount="${causynth_repo}:/hadoop:ro"
        isolated_target_mount=(
            -v "${replay_target_dir}:/hadoop/hadoop-hdfs-project/hadoop-hdfs/target"
        )
        container_user_args=(--user "$(id -u):$(id -g)")
        isolated_test_properties=(
            -Dtest.build.data="${replay_work_in_container}/test-build-data"
            -Dtest.build.dir="${replay_work_in_container}/test-build-dir"
            -Dtest.build.shared.data="${replay_work_in_container}/shared-data"
            -Dhadoop.tmp.dir="${replay_work_in_container}/hadoop-tmp"
            -Djava.io.tmpdir="${replay_work_in_container}/java-tmp"
        )
    fi
    # Keep the Causynth identity pinned to the original HDFS test.  A caller
    # may select a harness-only wrapper for Surefire (for example, one that
    # removes JUnit's 60-second wall-clock deadline on the interpreted custom
    # JVM) without changing activation matching or recorded result identity.
    surefire_test_selector="${CAUSYNTH_SUREFIRE_TEST_SELECTOR:-${test_name}}"
    test_classes_overlay="${CAUSYNTH_TEST_CLASSES_OVERLAY:-}"
    if [[ -n "${test_classes_overlay}" ]]; then
        if [[ ! -d "${test_classes_overlay}" ]]; then
            echo "[ERROR] Test-classes overlay not found: ${test_classes_overlay}" >&2
            exit 1
        fi
        test_classes_overlay=$(realpath "${test_classes_overlay}")
        test_classes_mount=(
            -v "${test_classes_overlay}:/hadoop/hadoop-hdfs-project/hadoop-hdfs/target/test-classes:ro"
        )
    fi
    arg_line="-Dcausynth.trace.test=${test_name} -Dcausynth.concolic.activation.plan=${plan_in_container} -Dcausynth.concolic.activation.id=${activation_id} -Dcausynth.concolic.results=${result_in_container}"
    if [[ -n "${replay_work_in_container:-}" ]]; then
        arg_line+=" -Dtest.build.data=${replay_work_in_container}/test-build-data -Dtest.build.dir=${replay_work_in_container}/test-build-dir -Dtest.build.shared.data=${replay_work_in_container}/shared-data -Dhadoop.tmp.dir=${replay_work_in_container}/hadoop-tmp -Djava.io.tmpdir=${replay_work_in_container}/java-tmp -Duser.home=/tmp -Duser.name=$(id -un)"
    fi

    local discovery_trace_dir=""
    if [[ -n "${CAUSYNTH_CAMPAIGN_DISCOVERED_ACTIVATIONS:-}" \
            || -n "${CAUSYNTH_CAMPAIGN_DISCOVERED_EDGES:-}" ]]; then
        if [[ -z "${CAUSYNTH_CAMPAIGN_DISCOVERED_ACTIVATIONS:-}" \
                || -z "${CAUSYNTH_CAMPAIGN_DISCOVERED_EDGES:-}" ]]; then
            echo "[ERROR] Campaign discovery requires both activation and edge output paths"
            exit 1
        fi
        local discovery_parent trace_in_container static_graph_in_container
        local regions_in_container region_edges_in_container
        local discovery_max_events discovery_max_graph_edges
        local discovery_max_context_pairs discovery_streaming_only
        local static_graph_file regions_file region_edges_file
        local static_graph_lines static_region_lines static_region_edge_lines
        local static_graph_sha static_regions_sha static_region_edges_sha
        static_graph_file="${causynth_output_dir}/static_dataflow_edges.jsonl"
        regions_file="${causynth_output_dir}/symbolic_regions.jsonl"
        region_edges_file="${causynth_output_dir}/symbolic_region_edges.jsonl"
        for required_static in "${static_graph_file}" "${regions_file}" \
                "${region_edges_file}"; do
            if [[ ! -s "${required_static}" ]]; then
                echo "[ERROR] Campaign static discovery input is missing or empty: ${required_static}" >&2
                exit 1
            fi
        done
        static_graph_lines=$(wc -l < "${static_graph_file}" | tr -d '[:space:]')
        static_region_lines=$(wc -l < "${regions_file}" | tr -d '[:space:]')
        static_region_edge_lines=$(wc -l < "${region_edges_file}" | tr -d '[:space:]')
        static_graph_sha=$(shasum -a 256 "${static_graph_file}" | awk '{print $1}')
        static_regions_sha=$(shasum -a 256 "${regions_file}" | awk '{print $1}')
        static_region_edges_sha=$(shasum -a 256 "${region_edges_file}" | awk '{print $1}')
        discovery_parent=$(dirname "$(realpath -m \
            "${CAUSYNTH_CAMPAIGN_DISCOVERED_ACTIVATIONS}")")
        mkdir -p "${discovery_parent}" \
            "$(dirname "$(realpath -m \
                "${CAUSYNTH_CAMPAIGN_DISCOVERED_EDGES}")")"
        rm -f "${CAUSYNTH_CAMPAIGN_DISCOVERED_ACTIVATIONS}" \
            "${CAUSYNTH_CAMPAIGN_DISCOVERED_EDGES}"
        discovery_trace_dir="${discovery_parent}/discovered-runtime-trace"
        mkdir -p "${discovery_trace_dir}"
        # Only remove files owned by this deterministic campaign execution;
        # historical v3/v4/v5 artifact directories are never touched.
        rm -f "${discovery_trace_dir}/runtime_trace.jsonl" \
            "${discovery_trace_dir}/concolic_activation_plan.jsonl" \
            "${discovery_trace_dir}/runtime_region_edge_validation.jsonl" \
            "${discovery_trace_dir}/runtime_region_instances.jsonl" \
            "${discovery_trace_dir}/runtime_region_validation.jsonl" \
            "${discovery_trace_dir}/runtime_region_summary.json" \
            "${discovery_trace_dir}/summary.json" \
            "${discovery_trace_dir}/streaming_trace_manifest.json" \
            "${discovery_trace_dir}/offline_aggregation_provenance.json"
        discovery_max_events="${CAUSYNTH_CAMPAIGN_TRACE_MAX_EVENTS:-${causynth_campaign_trace_max_events:-2000000}}"
        discovery_max_graph_edges="${CAUSYNTH_CAMPAIGN_TRACE_MAX_GRAPH_EDGES:-${causynth_campaign_trace_max_graph_edges:-250000}}"
        discovery_max_context_pairs="${CAUSYNTH_CAMPAIGN_TRACE_MAX_CONTEXT_PAIRS_PER_EDGE:-${causynth_campaign_trace_max_context_pairs_per_edge:-10000}}"
        discovery_streaming_only="${CAUSYNTH_CAMPAIGN_TRACE_STREAMING_ONLY:-true}"
        trace_in_container=$(workspace_container_path "${discovery_trace_dir}")
        static_graph_in_container=$(workspace_container_path \
            "${static_graph_file}")
        regions_in_container=$(workspace_container_path "${regions_file}")
        region_edges_in_container=$(workspace_container_path \
            "${region_edges_file}")
        discovery_properties=(
            -Dcausynth.trace.output.dir="${trace_in_container}"
            -Dcausynth.static.graph="${static_graph_in_container}"
            -Dcausynth.symbolic.regions="${regions_in_container}"
            -Dcausynth.symbolic.region.edges="${region_edges_in_container}"
            -Dcausynth.trace.max.events="${discovery_max_events}"
            -Dcausynth.trace.max.graph.edges="${discovery_max_graph_edges}"
            -Dcausynth.trace.max.context.pairs.per.edge="${discovery_max_context_pairs}"
        )
        if [[ "${discovery_streaming_only}" == "true" ]]; then
            discovery_properties+=(
                -Dcausynth.trace.streaming.only=true
                -Dcausynth.trace.aggregate.on.shutdown=false
            )
            arg_line+=" -Dcausynth.trace.streaming.only=true -Dcausynth.trace.aggregate.on.shutdown=false"
        else
            discovery_properties+=(
                -Dcausynth.trace.streaming.only=false
                -Dcausynth.trace.aggregate.on.shutdown=true
            )
            arg_line+=" -Dcausynth.trace.streaming.only=false -Dcausynth.trace.aggregate.on.shutdown=true"
        fi
        arg_line+=" -Dcausynth.trace.output.dir=${trace_in_container} -Dcausynth.static.graph=${static_graph_in_container} -Dcausynth.symbolic.regions=${regions_in_container} -Dcausynth.symbolic.region.edges=${region_edges_in_container} -Dcausynth.trace.max.events=${discovery_max_events} -Dcausynth.trace.max.graph.edges=${discovery_max_graph_edges} -Dcausynth.trace.max.context.pairs.per.edge=${discovery_max_context_pairs}"
    fi

    run_container run --rm --platform linux/amd64 \
        ${container_user_args[@]+"${container_user_args[@]}"} \
        -e HOME=/tmp \
        -e USER="$(id -un)" \
        -e LOGNAME="$(id -un)" \
        -e MAVEN_OPTS=-Duser.home=/tmp \
        -e JAVA_HOME=/openjdk/build/linux-x86_64-normal-zero-release/images/j2sdk-image \
        -e PATH=/openjdk/build/linux-x86_64-normal-zero-release/images/j2sdk-image/bin:/maven/bin:/usr/bin:/bin \
        -v "${HOME}/.m2:/tmp/.m2:ro" \
        -v "${concolic_maven_dir}:/maven:ro" \
        -v "${concolic_maven_java_lib_dir}:/java:ro" \
        -v "${concolic_maven_etc_dir}:/etc/maven:ro" \
        -v "${concolic_openjdk_dir}:/openjdk:ro" \
        -v "${hadoop_repo_mount}" \
        ${isolated_target_mount[@]+"${isolated_target_mount[@]}"} \
        -v "${concolic_classes_path}:/hadoop/hadoop-hdfs-project/hadoop-hdfs/target/classes:ro" \
        ${test_classes_mount[@]+"${test_classes_mount[@]}"} \
        -v "${gc_dir}:/graphchecker" \
        -w /hadoop/hadoop-hdfs-project/hadoop-hdfs \
        "${concolic_docker_image}" \
        "${concolic_maven_command:-mvn}" -o \
        -Dmaven.repo.local=/tmp/.m2/repository \
        surefire:test \
        -Dtest="${surefire_test_selector}" \
        -DfailIfNoTests=false \
        -Dhadoop.log.dir="${log_dir}" \
        -Dcausynth.trace.test="${test_name}" \
        -Dcausynth.concolic.activation.plan="${plan_in_container}" \
        -Dcausynth.concolic.activation.id="${activation_id}" \
        -Dcausynth.concolic.results="${result_in_container}" \
        ${isolated_test_properties[@]+"${isolated_test_properties[@]}"} \
        ${discovery_properties[@]+"${discovery_properties[@]}"} \
        -DargLine="${arg_line}" \
        -Dmaven-surefire-plugin.argLine="${arg_line}" || replay_status=$?

    if [[ -n "${discovery_trace_dir}" ]]; then
        local trace_summary="${discovery_trace_dir}/summary.json"
        local region_summary="${discovery_trace_dir}/runtime_region_summary.json"
        local discovered_activations="${discovery_trace_dir}/concolic_activation_plan.jsonl"
        local discovered_edges="${discovery_trace_dir}/runtime_region_edge_validation.jsonl"
        local streaming_manifest="${discovery_trace_dir}/streaming_trace_manifest.json"
        local offline_provenance="${discovery_trace_dir}/offline_aggregation_provenance.json"
        local raw_trace="${discovery_trace_dir}/runtime_trace.jsonl"
        local offline_status=0 raw_lines=0 raw_sha=""
        if [[ "${discovery_streaming_only}" == "true" ]]; then
            if [[ -s "${raw_trace}" && -f "${streaming_manifest}" ]]; then
                raw_lines=$(wc -l < "${raw_trace}" | tr -d '[:space:]')
                if ! jq -e --argjson rows "${raw_lines}" \
                        '.status == "CLOSED" and .complete == true
                         and .truncated == false and .writeFailure == false
                         and .attemptedEventCount == $rows' \
                        "${streaming_manifest}" >/dev/null; then
                    echo "[ERROR] Streaming campaign trace did not close completely" >&2
                    offline_status=1
                fi
            else
                echo "[ERROR] Streaming campaign trace or close manifest is missing" >&2
                offline_status=1
            fi
            if [[ "${offline_status}" -eq 0 ]]; then
                "${graphchecker_java_bin}" -Xmx"${CAUSYNTH_CAMPAIGN_OFFLINE_AGGREGATION_HEAP:-${causynth_campaign_offline_aggregation_heap:-6g}}" \
                    -cp "${gc_jar}" \
                    edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder \
                    --trace-dir "${discovery_trace_dir}" \
                    --static-graph "${static_graph_file}" \
                    --regions "${regions_file}" \
                    --region-edges "${region_edges_file}" \
                    --test "${test_name}" \
                    --max-graph-edges "${discovery_max_graph_edges}" \
                    --max-context-pairs-per-edge \
                    "${discovery_max_context_pairs}" || offline_status=$?
            fi
            if [[ "${offline_status}" -eq 0 ]] \
                    && { [[ ! -f "${region_summary}" ]] \
                    || ! jq -e \
                        --argjson regions "${static_region_lines}" \
                        --argjson edges "${static_region_edge_lines}" \
                        '.truncated == false
                         and .staticRegionCount == $regions
                         and .staticRegionEdgeCount == $edges' \
                        "${region_summary}" >/dev/null; }; then
                echo "[ERROR] Campaign offline aggregation did not consume the exact static region catalogs" >&2
                offline_status=1
            fi
            if [[ "${offline_status}" -eq 0 ]]; then
                raw_sha=$(shasum -a 256 "${raw_trace}" | awk '{print $1}')
                jq -n \
                    --arg mode "FRESH_JVM_OFFLINE_AGGREGATION_OF_SAME_EXECUTION_STREAM" \
                    --arg rawTrace "${raw_trace}" \
                    --arg rawTraceSha256 "${raw_sha}" \
                    --argjson rawTraceLineCount "${raw_lines}" \
                    --arg graphCheckerJar "$(realpath "${gc_jar}")" \
                    --arg graphCheckerJarSha256 "${graphchecker_jar_sha256}" \
                    --arg staticGraph "$(realpath "${static_graph_file}")" \
                    --arg staticGraphSha256 "${static_graph_sha}" \
                    --argjson staticGraphLineCount "${static_graph_lines}" \
                    --arg symbolicRegions "$(realpath "${regions_file}")" \
                    --arg symbolicRegionsSha256 "${static_regions_sha}" \
                    --argjson symbolicRegionCount "${static_region_lines}" \
                    --arg symbolicRegionEdges "$(realpath "${region_edges_file}")" \
                    --arg symbolicRegionEdgesSha256 "${static_region_edges_sha}" \
                    --argjson symbolicRegionEdgeCount "${static_region_edge_lines}" \
                    --arg concolicOpenJdkDir \
                    "$(realpath "${concolic_openjdk_dir}")" \
                    --arg javaSha256 "${concolic_java_sha256}" \
                    --arg libjvmSha256 "${concolic_libjvm_sha256}" \
                    --arg rtJarSha256 "${concolic_rt_sha256}" \
                    '{schemaVersion:1, mode:$mode, rawTrace:$rawTrace,
                      rawTraceSha256:$rawTraceSha256,
                      rawTraceLineCount:$rawTraceLineCount,
                      graphCheckerJar:$graphCheckerJar,
                      graphCheckerJarSha256:$graphCheckerJarSha256,
                      staticGraph:$staticGraph,
                      staticGraphSha256:$staticGraphSha256,
                      staticGraphLineCount:$staticGraphLineCount,
                      symbolicRegions:$symbolicRegions,
                      symbolicRegionsSha256:$symbolicRegionsSha256,
                      symbolicRegionCount:$symbolicRegionCount,
                      symbolicRegionEdges:$symbolicRegionEdges,
                      symbolicRegionEdgesSha256:$symbolicRegionEdgesSha256,
                      symbolicRegionEdgeCount:$symbolicRegionEdgeCount,
                      concolicOpenJdkDir:$concolicOpenJdkDir,
                      javaSha256:$javaSha256,
                      libjvmSha256:$libjvmSha256,
                      rtJarSha256:$rtJarSha256,
                      sameExecutionEvidence:true,
                      replayJvmAggregation:false,
                      complete:true}' > "${offline_provenance}"
            elif [[ "${replay_status}" -eq 0 ]]; then
                replay_status=87
            fi
        fi
        if [[ -f "${trace_summary}" \
                && -f "${region_summary}" \
                && -f "${discovered_activations}" \
                && -f "${discovered_edges}" ]] \
                && jq -e '(.status // "") != "shutdown_failure"
                    and .truncated == false
                    and .roleTruncated == false' "${trace_summary}" >/dev/null \
                && jq -e --argjson regions "${static_region_lines}" \
                    --argjson edges "${static_region_edge_lines}" \
                    '.truncated == false
                     and .staticRegionCount == $regions
                     and .staticRegionEdgeCount == $edges' \
                    "${region_summary}" >/dev/null \
                && jq -e --argjson rows "$(wc -l < "${raw_trace}" | tr -d '[:space:]')" \
                    '(.traceEventCount + .fieldEventCount
                      + .executionEventCount) == $rows' \
                    "${trace_summary}" >/dev/null; then
            # Empty JSONL files are valid evidence that this accepted JVM
            # execution discovered no new rows.  File existence, not size,
            # distinguishes that result from a failed shutdown aggregation.
            cp -f "${discovered_activations}" \
                "${CAUSYNTH_CAMPAIGN_DISCOVERED_ACTIVATIONS}"
            cp -f "${discovered_edges}" \
                "${CAUSYNTH_CAMPAIGN_DISCOVERED_EDGES}"
        else
            echo "[ERROR] Campaign runtime discovery is missing, failed, or truncated" >&2
            if [[ "${replay_status}" -eq 0 ]]; then
                replay_status=86
            fi
        fi
    fi
    local runtime_provenance
    runtime_provenance="$(dirname "$(realpath "${activation_plan}")")/concolic_runtime_provenance.json"
    jq -n \
        --arg test "${test_name}" \
        --arg activationId "${activation_id}" \
        --arg concolicOpenJdkDir "$(realpath "${concolic_openjdk_dir}")" \
        --arg javaSha256 "${concolic_java_sha256}" \
        --arg libjvmSha256 "${concolic_libjvm_sha256}" \
        --arg rtJarSha256 "${concolic_rt_sha256}" \
        --arg graphCheckerJar "$(realpath "${gc_jar}")" \
        --arg graphCheckerJarSha256 "${graphchecker_jar_sha256}" \
        --argjson replayStatus "${replay_status}" \
        '{schemaVersion:1, test:$test, activationId:$activationId,
          concolicOpenJdkDir:$concolicOpenJdkDir,
          javaSha256:$javaSha256, libjvmSha256:$libjvmSha256,
          rtJarSha256:$rtJarSha256,
          graphCheckerJar:$graphCheckerJar,
          graphCheckerJarSha256:$graphCheckerJarSha256,
          replayStatus:$replayStatus,
          complete:($replayStatus == 0)}' > "${runtime_provenance}"
    echo "[Concolic] raw result: ${result_file}"
    return "${replay_status}"
}

do_import_concolic() {
    local activation_plan="${1:-}"
    local results="${2:-}"
    local regions="${3:-${causynth_output_dir}/symbolic_regions.jsonl}"
    local expected_regions_sha256="${4:-}"
    if [[ ! -f "${activation_plan}" || ! -f "${results}" ]]; then
        echo "[ERROR] Usage: import-concolic <scheduled-plan> <raw-results> [regions] [regions-sha256]"
        return 1
    fi
    if [[ ! -s "${regions}" ]]; then
        echo "[ERROR] Concolic import region catalog is missing or empty: ${regions}" >&2
        return 1
    fi
    regions=$(realpath "${regions}")
    local output_dir actual_regions_sha256
    actual_regions_sha256=$(shasum -a 256 "${regions}" | awk '{print $1}')
    if [[ -n "${expected_regions_sha256}" \
            && "${actual_regions_sha256}" != "${expected_regions_sha256}" ]]; then
        echo "[ERROR] Concolic import region catalog changed after batch preflight" >&2
        echo "[ERROR] Expected: ${expected_regions_sha256}" >&2
        echo "[ERROR] Actual:   ${actual_regions_sha256}" >&2
        return 1
    fi
    output_dir=$(dirname "$(realpath "${results}")")
    "${graphchecker_java_bin}" -cp "${gc_jar}" \
        edu.uva.liftlab.graphchecker.concolic.ConcolicSummaryImporter \
        --results "${results}" \
        --activation-plan "${activation_plan}" \
        --regions "${regions}" \
        --output "${output_dir}/concolic_region_summaries.jsonl" \
        --diagnostics "${output_dir}/concolic_import_diagnostics.jsonl" \
        --cache-dir "${output_dir}/concolic-summary-cache"
}

batch_paths_overlap() {
    local left=$1 right=$2
    [[ "${left}" == "${right}" \
        || "${left}" == "${right}/"* \
        || "${right}" == "${left}/"* ]]
}

verify_batch_schedule_binding() {
    local plan=$1 regions=$2 regions_sha256=$3 provenance=$4
    local expected_plan_sha256="${5:-}" expected_provenance_sha256="${6:-}"
    local actual_plan_sha256 actual_provenance_sha256
    if [[ ! -s "${plan}" || ! -s "${regions}" \
            || ! -s "${provenance}" || -L "${provenance}" ]]; then
        echo "[ERROR] Batch schedule binding input is missing or invalid: ${provenance}" >&2
        return 1
    fi
    actual_plan_sha256=$(shasum -a 256 "${plan}" | awk '{print $1}')
    actual_provenance_sha256=$(shasum -a 256 "${provenance}" | awk '{print $1}')
    if [[ -n "${expected_plan_sha256}" \
            && "${actual_plan_sha256}" != "${expected_plan_sha256}" ]]; then
        echo "[ERROR] Batch scheduled activation plan changed after preflight" >&2
        return 1
    fi
    if [[ -n "${expected_provenance_sha256}" \
            && "${actual_provenance_sha256}" != "${expected_provenance_sha256}" ]]; then
        echo "[ERROR] Batch schedule provenance changed after preflight" >&2
        return 1
    fi
    if ! jq -e --arg plan "${plan}" \
            --arg planSha256 "${actual_plan_sha256}" \
            --arg regions "${regions}" --arg regionsSha256 "${regions_sha256}" '
            .complete == true
            and .scheduledActivationPlan == $plan
            and .scheduledActivationPlanSha256 == $planSha256
            and .regions == $regions
            and .regionsSha256 == $regionsSha256' \
            "${provenance}" >/dev/null; then
        echo "[ERROR] Batch plan/region catalog is not bound by schedule provenance: ${provenance}" >&2
        return 1
    fi
}

batch_ownership_marker() {
    local spec=$1
    printf '%s/.causynth-hdfs-concolic-batch-owner.json\n' \
        "$(jq -r '.outputDir' "${spec}")"
}

ensure_batch_job_ownership() {
    local spec=$1 marker temporary output_dir path
    output_dir=$(jq -r '.outputDir' "${spec}")
    marker=$(batch_ownership_marker "${spec}")
    if [[ -L "${marker}" ]]; then
        echo "[ERROR] Batch ownership marker must not be a symbolic link: ${marker}" >&2
        return 1
    fi
    if [[ -f "${marker}" ]]; then
        if ! jq -e --slurpfile expected "${spec}" '
                .schemaVersion == 1
                and .kind == "HDFS_CONCOLIC_BATCH_OWNERSHIP"
                and .job == ($expected[0] | {
                    jobId, outputDir, classesDir, staticOutputDir,
                    hadoopTargetDir, workDir})' "${marker}" >/dev/null; then
            echo "[ERROR] Batch ownership marker does not match job paths: ${marker}" >&2
            return 1
        fi
        return 0
    fi
    if [[ -e "${marker}" || -L "${marker}" ]]; then
        echo "[ERROR] Batch ownership marker is not a regular file: ${marker}" >&2
        return 1
    fi
    for path in \
            "$(jq -r '.classesDir' "${spec}")" \
            "$(jq -r '.staticOutputDir' "${spec}")" \
            "$(jq -r '.hadoopTargetDir' "${spec}")" \
            "$(jq -r '.workDir' "${spec}")" \
            "${output_dir}/concolic_region_results.jsonl" \
            "${output_dir}/concolic_region_summaries.jsonl" \
            "${output_dir}/concolic_import_diagnostics.jsonl" \
            "${output_dir}/concolic_runtime_provenance.json" \
            "${output_dir}/concolic-summary-cache"; do
        if [[ -e "${path}" || -L "${path}" ]]; then
            echo "[ERROR] Refusing to claim pre-existing unowned batch artifact: ${path}" >&2
            return 1
        fi
    done
    temporary="${marker}.tmp.$$"
    if ! jq -n --slurpfile expected "${spec}" '
        {schemaVersion:1, kind:"HDFS_CONCOLIC_BATCH_OWNERSHIP",
         job:($expected[0] | {
            jobId, outputDir, classesDir, staticOutputDir,
            hadoopTargetDir, workDir})}' > "${temporary}"; then
        rm -f -- "${temporary}"
        return 1
    fi
    mv "${temporary}" "${marker}" || return $?
}

reset_batch_job_paths() {
    local spec=$1 path work_dir
    ensure_batch_job_ownership "${spec}" || return $?
    for path in \
            "$(jq -r '.classesDir' "${spec}")" \
            "$(jq -r '.staticOutputDir' "${spec}")" \
            "$(jq -r '.hadoopTargetDir' "${spec}")" \
            "$(jq -r '.workDir' "${spec}")"; do
        require_no_symlink_components "batch-owned reset path" "${path}" \
            || return $?
        if [[ -e "${path}" ]]; then
            rm -rf -- "${path}" || return $?
        fi
    done
    rm -f -- \
        "$(jq -r '.outputDir' "${spec}")/concolic_region_results.jsonl" \
        "$(jq -r '.outputDir' "${spec}")/concolic_region_summaries.jsonl" \
        "$(jq -r '.outputDir' "${spec}")/concolic_import_diagnostics.jsonl" \
        "$(jq -r '.outputDir' "${spec}")/concolic_runtime_provenance.json" \
        || return $?
    rm -rf -- \
        "$(jq -r '.outputDir' "${spec}")/concolic-summary-cache" \
        || return $?
    work_dir=$(jq -r '.workDir' "${spec}")
    mkdir -p "${work_dir}"
}

prepare_batch_hdfs_target() {
    local spec=$1 base_target target_dir output_dir copy_binary mode
    local staging_dir
    base_target="${CAUSYNTH_HDFS_CONCOLIC_BASE_TARGET:-${causynth_hdfs_concolic_base_target:-${hdfs_dir}/target}}"
    if [[ ! -d "${base_target}" ]]; then
        echo "[ERROR] Configured base HDFS target is missing: ${base_target}" >&2
        return 1
    fi
    base_target=$(realpath "${base_target}")
    target_dir=$(jq -r '.hadoopTargetDir' "${spec}")
    output_dir=$(jq -r '.outputDir' "${spec}")
    case "${target_dir}" in
        "${output_dir}"/*) ;;
        *)
            echo "[ERROR] Batch HDFS target must be owned by its output directory: ${target_dir}" >&2
            return 1
            ;;
    esac
    require_no_symlink_components "batch HDFS target snapshot" "${target_dir}" \
        || return $?
    copy_binary=$(configured_tool_path \
        "${CAUSYNTH_SNAPSHOT_COPY_BIN:-${snapshot_copy_bin:-cp}}") \
        || return $?
    mode="${CAUSYNTH_HDFS_TARGET_SNAPSHOT_MODE:-${causynth_hdfs_target_snapshot_mode:-auto}}"
    case "${mode}" in
        auto|always|copy) ;;
        *)
            echo "[ERROR] Unsupported HDFS target snapshot mode: ${mode}" >&2
            return 1
            ;;
    esac

    # A replay must never inherit Surefire/MiniDFSCluster writes from an
    # earlier attempt.  Both paths are statically proven children of the
    # manifest-owned output directory before this bounded cleanup.
    if [[ -e "${target_dir}" ]]; then
        rm -rf -- "${target_dir}" || return $?
    fi
    mkdir -p "$(dirname "${target_dir}")" || return $?
    staging_dir=$(mktemp -d "${target_dir}.tmp.XXXXXX") || return $?
    local copy_status=0
    case "${mode}" in
        auto)
            "${copy_binary}" -a --reflink=auto \
                "${base_target}/." "${staging_dir}/" || copy_status=$?
            ;;
        always)
            "${copy_binary}" -a --reflink=always \
                "${base_target}/." "${staging_dir}/" || copy_status=$?
            ;;
        copy)
            "${copy_binary}" -a \
                "${base_target}/." "${staging_dir}/" || copy_status=$?
            ;;
    esac
    if [[ "${copy_status}" -ne 0 ]]; then
        rm -rf -- "${staging_dir}"
        return "${copy_status}"
    fi
    rm -rf -- "${staging_dir}/surefire-reports" \
        "${staging_dir}/test-dir" "${staging_dir}/test-logs" \
        "${staging_dir}/log" || return $?
    mv "${staging_dir}" "${target_dir}" || return $?
}

run_concolic_batch_job() {
    local spec=$1 plan activation classes_dir static_dir output_dir
    local target_dir work_dir test_name fixture_worker step_status
    output_dir=$(jq -r '.outputDir' "${spec}")
    reset_batch_job_paths "${spec}" || return $?
    if [[ "${CAUSYNTH_HDFS_CONCOLIC_BATCH_FIXTURE_MODE:-false}" == "true" ]]; then
        fixture_worker="${CAUSYNTH_HDFS_CONCOLIC_BATCH_FIXTURE_WORKER:-}"
        if [[ -z "${fixture_worker}" || ! -x "${fixture_worker}" ]]; then
            echo "[ERROR] Batch fixture mode requires an executable fixture worker" >&2
            return 1
        fi
        CAUSYNTH_CAMPAIGN_DISCOVERED_ACTIVATIONS= \
        CAUSYNTH_CAMPAIGN_DISCOVERED_EDGES= \
        CAUSYNTH_SUREFIRE_TEST_SELECTOR= \
        CAUSYNTH_TEST_CLASSES_OVERLAY= \
            "${fixture_worker}" "${spec}" || return $?
        if [[ ! -s "${output_dir}/concolic_region_results.jsonl" ]]; then
            echo "[ERROR] Batch fixture produced no region result: ${output_dir}" >&2
            return 88
        fi
        return
    fi

    plan=$(jq -r '.plan' "${spec}")
    activation=$(jq -r '.activationId' "${spec}")
    classes_dir=$(jq -r '.classesDir' "${spec}")
    static_dir=$(jq -r '.staticOutputDir' "${spec}")
    target_dir=$(jq -r '.hadoopTargetDir' "${spec}")
    work_dir=$(jq -r '.workDir' "${spec}")
    test_name=$(jq -r '.test' "${spec}")

    CAUSYNTH_CAMPAIGN_DISCOVERED_ACTIVATIONS= \
    CAUSYNTH_CAMPAIGN_DISCOVERED_EDGES= \
    CAUSYNTH_SUREFIRE_TEST_SELECTOR= \
    CAUSYNTH_TEST_CLASSES_OVERLAY= \
    CAUSYNTH_CONCOLIC_CLASSES_PATH="${classes_dir}" \
    CAUSYNTH_CONCOLIC_STATIC_OUTPUT_DIR="${static_dir}" \
        "${script_dir}/run_hdfs.sh" process-concolic \
            "${plan}" "${activation}" \
        || { step_status=$?; return "${step_status}"; }
    prepare_batch_hdfs_target "${spec}" \
        || { step_status=$?; return "${step_status}"; }
    CAUSYNTH_CAMPAIGN_DISCOVERED_ACTIVATIONS= \
    CAUSYNTH_CAMPAIGN_DISCOVERED_EDGES= \
    CAUSYNTH_SUREFIRE_TEST_SELECTOR= \
    CAUSYNTH_TEST_CLASSES_OVERLAY= \
    CAUSYNTH_CONCOLIC_CLASSES_PATH="${classes_dir}" \
    CAUSYNTH_REPLAY_HDFS_TARGET_DIR="${target_dir}" \
    CAUSYNTH_REPLAY_WORK_DIR="${work_dir}" \
        "${script_dir}/run_hdfs.sh" replay-concolic \
            "${plan}" "${activation}" "${test_name}" \
        || { step_status=$?; return "${step_status}"; }
    if [[ ! -s "${output_dir}/concolic_region_results.jsonl" ]]; then
        echo "[ERROR] Batch replay produced no region result: ${output_dir}" >&2
        return 88
    fi
}

run_concolic_batch_job_with_status() {
    local spec=$1 status_file=$2 start_time finish_time result_file
    local status=0 temporary_status
    start_time=$(date -u +%Y-%m-%dT%H:%M:%SZ)
    if run_concolic_batch_job "${spec}"; then
        status=0
    else
        status=$?
    fi
    finish_time=$(date -u +%Y-%m-%dT%H:%M:%SZ)
    result_file="$(jq -r '.outputDir' "${spec}")/concolic_region_results.jsonl"
    temporary_status="${status_file}.tmp.$$"
    jq -n --slurpfile job "${spec}" \
        --arg startedAt "${start_time}" --arg finishedAt "${finish_time}" \
        --arg result "${result_file}" --argjson workerStatus "${status}" \
        '{schemaVersion:1, kind:"HDFS_CONCOLIC_BATCH_JOB_STATUS",
          job:$job[0], startedAt:$startedAt, finishedAt:$finishedAt,
          result:$result, workerStatus:$workerStatus, importStatus:null,
          complete:false}' > "${temporary_status}"
    mv "${temporary_status}" "${status_file}"
    return "${status}"
}

write_concolic_batch_summary() {
    local manifest=$1 run_dir=$2 parallelism=$3
    shift 3
    local -a statuses=("$@")
    local summary="${run_dir}/batch_summary.json" temporary
    temporary="${summary}.tmp.$$"
    jq -s --arg manifest "${manifest}" --arg runDirectory "${run_dir}" \
        --argjson parallelism "${parallelism}" \
        '{schemaVersion:1, kind:"HDFS_CONCOLIC_BATCH_STATUS",
          manifest:$manifest, runDirectory:$runDirectory,
          parallelism:$parallelism, jobs:.,
          workerFailureCount:([.[] | select(.workerStatus != 0)] | length),
          importFailureCount:([.[] | select(.importStatus != null
              and .importStatus != 0)] | length),
          complete:(length > 0 and all(.[];
              .workerStatus == 0 and .importStatus == 0
              and .complete == true))}' \
        "${statuses[@]}" > "${temporary}"
    mv "${temporary}" "${summary}"
    echo "[Concolic batch] status: ${summary}"
}

do_replay_concolic_batch() {
    local manifest="${1:-}" parallelism status_base run_dir row
    local job_id plan activation output_dir classes_dir static_dir target_dir
    local work_dir test_name regions regions_sha256 actual_regions_sha256
    local schedule_provenance plan_sha256 schedule_provenance_sha256
    local base_target batch_workload_test candidate existing readonly
    local spec status_file index=0 worker_failed=0
    local finished_pid import_failed=0 result temporary_status status
    local -a specs=() statuses=() all_writable_paths=()
    local -a read_only_inputs=() current_writable=() current_children=()
    local -A active_pids=()

    require_nonempty_input "HDFS concolic batch manifest" "${manifest}"
    manifest=$(realpath "${manifest}")
    require_workspace_output_path "HDFS concolic batch manifest" "${manifest}"
    read_only_inputs=("${manifest}")
    parallelism="${CAUSYNTH_HDFS_CONCOLIC_PARALLELISM:-${causynth_hdfs_concolic_parallelism:-1}}"
    if [[ ! "${parallelism}" =~ ^[1-9][0-9]*$ ]]; then
        echo "[ERROR] HDFS concolic parallelism must be a positive integer: ${parallelism}" >&2
        return 1
    fi
    batch_workload_test="${configured_causynth_workload_test}"
    if ! jq -e -s --arg workload "${batch_workload_test}" '
            length > 0
            and all(.[];
              type == "object"
              and ((keys_unsorted - ["schemaVersion", "jobId", "plan",
                    "activationId", "classesDir", "staticOutputDir",
                    "outputDir", "hadoopTargetDir", "workDir", "test",
                    "regions", "regionsSha256"])
                   | length) == 0
              and .schemaVersion == 2
              and (.jobId | type == "string"
                   and test("^[A-Za-z0-9][A-Za-z0-9._-]*$"))
              and (.plan | type == "string" and startswith("/")
                   and (test("[[:space:]]") | not))
              and (.activationId | type == "string" and length > 0
                   and (test("[[:space:]]") | not))
              and (.regions | type == "string" and startswith("/")
                   and (test("[[:space:]]") | not))
              and (.regionsSha256 | type == "string"
                   and test("^[0-9a-f]{64}$"))
              and (.classesDir | type == "string" and startswith("/")
                   and (test("[[:space:]]") | not))
              and (.staticOutputDir | type == "string" and startswith("/")
                   and (test("[[:space:]]") | not))
              and (.outputDir | type == "string" and startswith("/")
                   and (test("[[:space:]]") | not))
              and ((has("hadoopTargetDir") | not)
                   or (.hadoopTargetDir | type == "string"
                       and startswith("/")
                       and (test("[[:space:]]") | not)))
              and ((has("workDir") | not)
                   or (.workDir | type == "string" and startswith("/")
                       and (test("[[:space:]]") | not)))
              and ((.test // $workload) == $workload))
            and ([.[].jobId] | unique | length) == length' \
            "${manifest}" >/dev/null; then
        echo "[ERROR] Invalid HDFS concolic batch manifest schema or workload" >&2
        return 1
    fi

    status_base="${CAUSYNTH_HDFS_CONCOLIC_BATCH_STATUS_DIR:-${causynth_output_dir}/${causynth_hdfs_concolic_batch_status_subdir:-concolic-batch-status}}"
    status_base=$(realpath -m "${status_base}")
    require_workspace_output_path "HDFS concolic batch status directory" \
        "${status_base}"
    base_target="${CAUSYNTH_HDFS_CONCOLIC_BASE_TARGET:-${causynth_hdfs_concolic_base_target:-${hdfs_dir}/target}}"
    if [[ ! -d "${base_target}" ]]; then
        echo "[ERROR] Configured base HDFS target is missing: ${base_target}" >&2
        return 1
    fi
    base_target=$(realpath "${base_target}")
    if batch_paths_overlap "${status_base}" "${base_target}"; then
        echo "[ERROR] Batch status directory overlaps the base HDFS target" >&2
        return 1
    fi
    mkdir -p "${status_base}"
    run_dir=$(mktemp -d "${status_base}/run.XXXXXX")
    mkdir -p "${run_dir}/specs" "${run_dir}/jobs"

    while IFS= read -r row; do
        job_id=$(jq -r '.jobId' <<< "${row}")
        plan=$(realpath -m "$(jq -r '.plan' <<< "${row}")")
        activation=$(jq -r '.activationId' <<< "${row}")
        output_dir=$(realpath -m "$(jq -r '.outputDir' <<< "${row}")")
        classes_dir=$(realpath -m "$(jq -r '.classesDir' <<< "${row}")")
        static_dir=$(realpath -m "$(jq -r '.staticOutputDir' <<< "${row}")")
        regions=$(realpath -m "$(jq -r '.regions' <<< "${row}")")
        regions_sha256=$(jq -r '.regionsSha256' <<< "${row}")
        schedule_provenance="${output_dir}/schedule_input_provenance.json"
        target_dir=$(jq -r '.hadoopTargetDir // empty' <<< "${row}")
        work_dir=$(jq -r '.workDir // empty' <<< "${row}")
        test_name=$(jq -r --arg workload "${batch_workload_test}" \
            '.test // $workload' <<< "${row}")
        target_dir=$(realpath -m \
            "${target_dir:-${output_dir}/hadoop-target-snapshot}")
        work_dir=$(realpath -m "${work_dir:-${output_dir}/replay-work}")

        if [[ ! -f "${plan}" || "$(dirname "${plan}")" != "${output_dir}" ]]; then
            echo "[ERROR] Batch plan must exist directly in its explicit outputDir: ${plan}" >&2
            return 1
        fi
        if [[ ! -s "${regions}" ]]; then
            echo "[ERROR] Batch region catalog is missing or empty: ${regions}" >&2
            return 1
        fi
        actual_regions_sha256=$(shasum -a 256 "${regions}" | awk '{print $1}')
        if [[ "${actual_regions_sha256}" != "${regions_sha256}" ]]; then
            echo "[ERROR] Batch region catalog SHA-256 mismatch: ${regions}" >&2
            echo "[ERROR] Expected: ${regions_sha256}" >&2
            echo "[ERROR] Actual:   ${actual_regions_sha256}" >&2
            return 1
        fi
        verify_batch_schedule_binding "${plan}" "${regions}" \
            "${regions_sha256}" "${schedule_provenance}"
        plan_sha256=$(shasum -a 256 "${plan}" | awk '{print $1}')
        schedule_provenance_sha256=$(shasum -a 256 \
            "${schedule_provenance}" | awk '{print $1}')
        require_workspace_output_path "batch output directory" "${output_dir}"
        require_workspace_output_path "batch region catalog" "${regions}"
        require_workspace_output_path "batch schedule provenance" \
            "${schedule_provenance}"
        for row in "${classes_dir}" "${static_dir}" "${target_dir}" \
                "${work_dir}"; do
            require_workspace_output_path "batch job-owned path" "${row}"
            case "${row}" in
                "${output_dir}"/*) ;;
                *)
                    echo "[ERROR] Batch job path escapes outputDir: ${row}" >&2
                    return 1
                    ;;
            esac
        done
        if batch_paths_overlap "${classes_dir}" "${static_dir}" \
                || batch_paths_overlap "${classes_dir}" "${target_dir}" \
                || batch_paths_overlap "${classes_dir}" "${work_dir}" \
                || batch_paths_overlap "${static_dir}" "${target_dir}" \
                || batch_paths_overlap "${static_dir}" "${work_dir}" \
                || batch_paths_overlap "${target_dir}" "${work_dir}"; then
            echo "[ERROR] Batch classes/static/target/work paths must not overlap: ${job_id}" >&2
            return 1
        fi
        current_writable=("${output_dir}" "${classes_dir}" "${static_dir}"
            "${target_dir}" "${work_dir}")
        current_children=("${classes_dir}" "${static_dir}" "${target_dir}"
            "${work_dir}")
        for candidate in "${current_writable[@]}"; do
            if batch_paths_overlap "${candidate}" "${status_base}" \
                    || batch_paths_overlap "${candidate}" "${base_target}"; then
                echo "[ERROR] Batch writable path overlaps status/base target: ${candidate}" >&2
                return 1
            fi
            for existing in "${all_writable_paths[@]}"; do
                if batch_paths_overlap "${candidate}" "${existing}"; then
                    echo "[ERROR] Batch jobs have nested or cross-role writable paths: ${candidate} <> ${existing}" >&2
                    return 1
                fi
            done
            for readonly in "${read_only_inputs[@]}"; do
                if batch_paths_overlap "${candidate}" "${readonly}"; then
                    echo "[ERROR] Batch writable path overlaps another job input: ${candidate} <> ${readonly}" >&2
                    return 1
                fi
            done
        done
        for readonly in "${plan}" "${regions}" "${schedule_provenance}"; do
            for candidate in "${current_children[@]}"; do
                if batch_paths_overlap "${readonly}" "${candidate}"; then
                    echo "[ERROR] Batch reset path overlaps plan/region input: ${candidate} <> ${readonly}" >&2
                    return 1
                fi
            done
            for existing in "${all_writable_paths[@]}"; do
                if batch_paths_overlap "${readonly}" "${existing}"; then
                    echo "[ERROR] Batch input overlaps another job writable path: ${readonly} <> ${existing}" >&2
                    return 1
                fi
            done
        done
        for readonly in "${plan}" "${regions}" "${schedule_provenance}"; do
            for candidate in \
                    "${output_dir}/concolic_region_results.jsonl" \
                    "${output_dir}/concolic_region_summaries.jsonl" \
                    "${output_dir}/concolic_import_diagnostics.jsonl" \
                    "${output_dir}/runtime_provenance.json" \
                    "${output_dir}/.causynth-hdfs-concolic-batch-owner.json"; do
                if [[ "${readonly}" == "${candidate}" ]]; then
                    echo "[ERROR] Batch input collides with a reset/output artifact: ${readonly}" >&2
                    return 1
                fi
            done
        done
        all_writable_paths+=("${current_writable[@]}")
        read_only_inputs+=("${plan}" "${regions}" "${schedule_provenance}")
        spec=$(printf '%s/%04d-%s.json' "${run_dir}/specs" \
            "${index}" "${job_id}")
        jq -n --arg jobId "${job_id}" --arg plan "${plan}" \
            --arg activationId "${activation}" --arg outputDir "${output_dir}" \
            --arg classesDir "${classes_dir}" --arg staticOutputDir "${static_dir}" \
            --arg hadoopTargetDir "${target_dir}" --arg workDir "${work_dir}" \
            --arg test "${test_name}" --arg regions "${regions}" \
            --arg regionsSha256 "${regions_sha256}" \
            --arg planSha256 "${plan_sha256}" \
            --arg scheduleProvenance "${schedule_provenance}" \
            --arg scheduleProvenanceSha256 \
                "${schedule_provenance_sha256}" \
            '{schemaVersion:2, jobId:$jobId, plan:$plan,
              activationId:$activationId, outputDir:$outputDir,
              classesDir:$classesDir, staticOutputDir:$staticOutputDir,
              hadoopTargetDir:$hadoopTargetDir, workDir:$workDir, test:$test,
              regions:$regions, regionsSha256:$regionsSha256,
              planSha256:$planSha256,
              scheduleProvenance:$scheduleProvenance,
              scheduleProvenanceSha256:$scheduleProvenanceSha256}' \
            > "${spec}"
        status_file=$(printf '%s/%04d-%s.json' "${run_dir}/jobs" \
            "${index}" "${job_id}")
        specs+=("${spec}")
        statuses+=("${status_file}")
        index=$((index + 1))
    done < <(jq -c '.' "${manifest}")

    # Keep the pool full: as soon as any custom-JDK process finishes, the next
    # activation starts.  Job-owned mounts make completion order irrelevant.
    for index in "${!specs[@]}"; do
        run_concolic_batch_job_with_status "${specs[${index}]}" \
            "${statuses[${index}]}" &
        active_pids[$!]="${index}"
        if [[ "${#active_pids[@]}" -ge "${parallelism}" ]]; then
            if wait -n -p finished_pid "${!active_pids[@]}"; then
                :
            else
                worker_failed=1
            fi
            unset 'active_pids['"${finished_pid}"']'
        fi
    done
    while [[ "${#active_pids[@]}" -gt 0 ]]; do
        if wait -n -p finished_pid "${!active_pids[@]}"; then
            :
        else
            worker_failed=1
        fi
        unset 'active_pids['"${finished_pid}"']'
    done
    for index in "${!statuses[@]}"; do
        status_file="${statuses[${index}]}"
        if [[ ! -s "${status_file}" ]]; then
            jq -n --slurpfile job "${specs[${index}]}" \
                '{schemaVersion:1, kind:"HDFS_CONCOLIC_BATCH_JOB_STATUS",
                  job:$job[0], startedAt:null, finishedAt:null,
                  result:($job[0].outputDir + "/concolic_region_results.jsonl"),
                  workerStatus:90, importStatus:null, complete:false}' \
                > "${status_file}"
        fi
        if [[ ! -s "${status_file}" ]] \
                || ! jq -e '.workerStatus == 0' "${status_file}" >/dev/null; then
            worker_failed=1
        fi
    done
    if [[ "${worker_failed}" -ne 0 ]]; then
        write_concolic_batch_summary "${manifest}" "${run_dir}" \
            "${parallelism}" "${statuses[@]}"
        echo "[ERROR] At least one batch replay failed; import phase was not started" >&2
        return 1
    fi

    # Import is deliberately a barrier phase.  No partial set of concrete
    # runs can be mistaken for a completed symbolic-summary generation.
    for index in "${!specs[@]}"; do
        plan=$(jq -r '.plan' "${specs[${index}]}")
        output_dir=$(jq -r '.outputDir' "${specs[${index}]}")
        regions=$(jq -r '.regions' "${specs[${index}]}")
        regions_sha256=$(jq -r '.regionsSha256' "${specs[${index}]}")
        plan_sha256=$(jq -r '.planSha256' "${specs[${index}]}")
        schedule_provenance=$(jq -r '.scheduleProvenance' \
            "${specs[${index}]}")
        schedule_provenance_sha256=$(jq -r \
            '.scheduleProvenanceSha256' "${specs[${index}]}")
        result="${output_dir}/concolic_region_results.jsonl"
        rm -f -- "${output_dir}/concolic_region_summaries.jsonl" \
            "${output_dir}/concolic_import_diagnostics.jsonl"
        rm -rf -- "${output_dir}/concolic-summary-cache"
        if verify_batch_schedule_binding "${plan}" "${regions}" \
                "${regions_sha256}" "${schedule_provenance}" \
                "${plan_sha256}" "${schedule_provenance_sha256}" \
                && do_import_concolic "${plan}" "${result}" \
                "${regions}" "${regions_sha256}" \
                && [[ -s "${output_dir}/concolic_region_summaries.jsonl" ]]; then
            status=0
        else
            status=$?
            [[ "${status}" -ne 0 ]] || status=89
            import_failed=1
        fi
        status_file="${statuses[${index}]}"
        temporary_status="${status_file}.tmp.$$"
        jq --argjson importStatus "${status}" \
            '.importStatus=$importStatus
             | .complete=(.workerStatus == 0 and $importStatus == 0)' \
            "${status_file}" > "${temporary_status}"
        mv "${temporary_status}" "${status_file}"
    done
    write_concolic_batch_summary "${manifest}" "${run_dir}" \
        "${parallelism}" "${statuses[@]}"
    if [[ "${import_failed}" -ne 0 ]]; then
        echo "[ERROR] At least one batch import failed" >&2
        return 1
    fi
}

do_campaign_capture() {
    local test_name="${1:-${causynth_workload_test}}"
    local activation_plan="${CAUSYNTH_CAMPAIGN_ACTIVATION_PLAN:-}"
    local activation_id="${CAUSYNTH_CAMPAIGN_ACTIVATION_ID:-}"
    if [[ -z "${activation_plan}" || -z "${activation_id}" ]]; then
        echo "[ERROR] campaign-capture is an internal command requiring campaign environment variables"
        exit 1
    fi
    # Each stable campaign execution owns both its replay classes and the
    # static analysis emitted while producing them.  This prevents a later
    # flip from overwriting the evidence for an earlier seed, and never falls
    # back to any checked-in historical v3/v4/v5 artifact directory.
    local execution_dir execution_static_output
    execution_dir=$(dirname "$(realpath "${activation_plan}")")
    concolic_classes_path="${execution_dir}/concolic_classes"
    execution_static_output="${execution_dir}/concolic-replay-static"
    CAUSYNTH_CONCOLIC_STATIC_OUTPUT_DIR="${execution_static_output}" \
        do_process_concolic "${activation_plan}" "${activation_id}"
    do_replay_concolic "${activation_plan}" "${activation_id}" "${test_name}"
    local actual_results
    actual_results="$(dirname "$(realpath "${activation_plan}")")/concolic_region_results.jsonl"
    if [[ "$(realpath "${actual_results}")" != "$(realpath "${CAUSYNTH_CAMPAIGN_RESULTS}")" ]]; then
        echo "[ERROR] campaign result path mismatch"
        exit 1
    fi
}

do_campaign_concolic() {
    verify_hadoop_source
    local test_name="${1:-${causynth_workload_test}}"
    local trace_dir schedule_dir campaign_dir campaign_summaries
    local campaign_state_manifest
    resolve_target_context "${test_name}"
    trace_dir="${target_trace_dir}"
    schedule_dir="${target_schedule_dir}"
    campaign_dir=$(realpath -m \
        "${CAUSYNTH_CAMPAIGN_OUTPUT_DIR:-${schedule_dir}/campaign}")
    require_workspace_output_path "campaign output directory" \
        "${campaign_dir}"
    mkdir -p "${campaign_dir}"
    local args=(
        --regions "${handoff_regions:-${causynth_output_dir}/symbolic_regions.jsonl}"
        --activations "${source_activations}"
        --edges "${source_edges}"
        --static-graph "${handoff_static_graph:-${causynth_output_dir}/static_dataflow_edges.jsonl}"
        --roots "${target_branch_queries}"
        --output-dir "${campaign_dir}"
        --z3 "$(configured_tool_path "${z3_bin}")"
        --runtime-discovery-mode \
            "${CAUSYNTH_CAMPAIGN_RUNTIME_DISCOVERY_MODE:-SAME_EXECUTION_REQUIRED}"
        --execution-timeout-ms "${CAUSYNTH_CAMPAIGN_EXECUTION_TIMEOUT_MS:-1200000}"
        --max-iterations "${CAUSYNTH_CAMPAIGN_MAX_ITERATIONS:-128}"
        --max-executions "${CAUSYNTH_CAMPAIGN_MAX_EXECUTIONS:-512}"
        --max-solver-queries "${CAUSYNTH_CAMPAIGN_MAX_SOLVER_QUERIES:-512}"
        --max-wall-clock-ms "${CAUSYNTH_CAMPAIGN_WALL_CLOCK_MS:-7200000}"
        --solver-timeout-ms "${CAUSYNTH_CAMPAIGN_SOLVER_TIMEOUT_MS:-20000}"
    )
    if [[ -n "${CAUSYNTH_CAMPAIGN_TRANSITION_FOCUS_EDGE:-}" ]]; then
        args+=(--transition-focus-edge
            "${CAUSYNTH_CAMPAIGN_TRANSITION_FOCUS_EDGE}")
    fi
    if [[ -n "${CAUSYNTH_CAMPAIGN_TRANSITION_FOCUS_ACTIVATION:-}" ]]; then
        args+=(--transition-focus-activation
            "${CAUSYNTH_CAMPAIGN_TRANSITION_FOCUS_ACTIVATION}")
    fi
    if [[ -n "${CAUSYNTH_CAMPAIGN_TRANSITION_FOCUS_GUARD:-}" ]]; then
        args+=(--transition-focus-guard
            "${CAUSYNTH_CAMPAIGN_TRANSITION_FOCUS_GUARD}")
    fi
    if [[ "${CAUSYNTH_CAMPAIGN_TRANSITION_FOCUS_ONLY:-false}" == "true" ]]; then
        args+=(--transition-focus-only true)
    fi
    campaign_summaries="${CAUSYNTH_CAMPAIGN_SUMMARIES:-${schedule_dir}/concolic_region_summaries.jsonl}"
    campaign_state_manifest="${campaign_dir}/campaign_state_manifest.json"
    if [[ -s "${campaign_state_manifest}" ]]; then
        # One immutable, hash-checked generation is the only resume
        # authority.  Never append attempt plans after it: attempt UUID path
        # order must not overwrite the refined campaign activation snapshot.
        args+=(--resume-state-manifest "${campaign_state_manifest}")
    else
        if [[ -e "${campaign_dir}/campaign_regions.jsonl" \
                || -e "${campaign_dir}/campaign_activations.jsonl" \
                || -e "${campaign_dir}/campaign_edge_validations.jsonl" \
                || -e "${campaign_dir}/campaign_roots.jsonl" \
                || -e "${campaign_dir}/campaign_summaries.jsonl" \
                || -e "${campaign_dir}/region_path_records.jsonl" \
                || -e "${campaign_dir}/campaign_static_graph.jsonl" \
                || -d "${campaign_dir}/state-generations" ]]; then
            echo "[ERROR] Partial campaign snapshot exists without an authoritative state manifest: ${campaign_dir}" >&2
            return 1
        fi
        require_nonempty_input "campaign seed summaries" \
            "${campaign_summaries}"
        args+=(--summaries "${campaign_summaries}")
        # Attempt-level recovery is allowed only before any authoritative
        # snapshot exists. Conflicting duplicate activation or summary ids
        # are rejected deterministically by the Java reader.
        local resume_plan resume_summary
        while IFS= read -r resume_plan; do
            resume_summary="$(dirname "${resume_plan}")/concolic_region_summaries.jsonl"
            [[ -s "${resume_summary}" ]] || continue
            args+=(--resume-activations "${resume_plan}")
            args+=(--summaries "${resume_summary}")
        done < <(find "${campaign_dir}/executions" -type f \
            -name activation_plan.jsonl -size +0c 2>/dev/null | sort)
    fi
    "${graphchecker_java_bin}" -cp "${gc_jar}" \
        edu.uva.liftlab.graphchecker.concolic.ConcolicCampaignRunner \
        "${args[@]}" -- "${script_dir}/run_hdfs.sh" campaign-capture "${test_name}"
    echo "[Concolic] campaign manifest: ${campaign_dir}/concolic_campaign_manifest.json"
    if jq -e '
            .complete == true
            and .postDiscoveryTargetRebaseCompleted == true
            and .postDiscoveryTargetRebaseRequired == false
            and .postDiscoveryTargetRebaseReady == true' \
            "${campaign_dir}/concolic_campaign_manifest.json" >/dev/null; then
        publish_campaign_handoff "${test_name}" "${campaign_dir}"
    elif jq -e '.complete == true' \
            "${campaign_dir}/concolic_campaign_manifest.json" >/dev/null; then
        echo "[ERROR] Campaign claims completion without a completed fresh target rebase" >&2
        return 1
    else
        echo "[Concolic] campaign checkpoint is incomplete; resume it before publishing a fresh handoff"
    fi
}

do_hdfs_port_map() {
    verify_hadoop_source
    local test_name="${1:-${causynth_workload_test}}"
    local trace_dir schedule_dir mapping_dir port_map contracts
    local -a scope_args=(
        --scope-repository "${causynth_repo}"
        --scope-commit "${causynth_expected_hadoop_commit}"
        --scope-workload "${causynth_workload_test}"
        --scope-patch "${causynth_hadoop_experiment_patch}"
        --scope-source-sha256 "${causynth_hadoop_pinned_source_sha256}"
    )
    resolve_target_context "${test_name}"
    trace_dir="${target_trace_dir}"
    schedule_dir="${target_schedule_dir}"
    mapping_dir=$(realpath -m \
        "${CAUSYNTH_HDFS_PORT_MAP_OUTPUT_DIR:-${schedule_dir}/hdfs-port-map}")
    prepare_fresh_output_directory "HDFS mapping output directory" \
        "${mapping_dir}"
    port_map="${mapping_dir}/hdfs_region_port_map.json"
    contracts="${mapping_dir}/hdfs_explicit_contracts.json"

    "${graphchecker_java_bin}" -cp "${gc_jar}" \
        edu.uva.liftlab.graphchecker.causynth.HdfsRegionPortMapper \
        --regions "${causynth_output_dir}/symbolic_regions.jsonl" \
        --runtime-report "${trace_dir}/runtime_region_summary.json" \
        --fatal-query "${schedule_dir}/branch_queries.jsonl" \
        --merge-plan "${schedule_dir}/symbolic_merge_plan.json" \
        --output "${port_map}" \
        "${scope_args[@]}"
    "${graphchecker_java_bin}" -cp "${gc_jar}" \
        edu.uva.liftlab.graphchecker.causynth.HdfsExplicitContracts \
        --output "${contracts}" \
        "${scope_args[@]}"
    echo "[Concolic] mapping-only HDFS port map: ${port_map}"
    echo "[Concolic] excluded explicit contracts: ${contracts}"
}

require_nonempty_input() {
    local label=$1 path=$2
    if [[ -z "${path}" || ! -s "${path}" ]]; then
        echo "[ERROR] ${label} is missing or empty: ${path}" >&2
        return 1
    fi
}

require_no_symlink_components() {
    local label=$1 path=$2 absolute probe="" part
    local -a components=()
    if [[ "${path}" == /* ]]; then
        absolute="${path}"
    else
        absolute="${PWD}/${path}"
    fi
    IFS='/' read -r -a components <<< "${absolute}"
    for part in "${components[@]}"; do
        [[ -n "${part}" ]] || continue
        probe="${probe}/${part}"
        if [[ -L "${probe}" ]]; then
            echo "[ERROR] ${label} contains a symbolic-link path component: ${probe}" >&2
            return 1
        fi
    done
}

require_workspace_output_path() {
    local label=$1 path=$2 canonical
    require_no_symlink_components "${label}" "${path}"
    canonical=$(realpath -m "${path}")
    case "${canonical}" in
        "${gc_dir}"/*) ;;
        *)
            echo "[ERROR] ${label} must be inside the GraphChecker workspace: ${canonical}" >&2
            return 1
            ;;
    esac
}

prepare_fresh_output_directory() {
    local label=$1 path=$2
    require_workspace_output_path "${label}" "${path}"
    if [[ -d "${path}" ]] \
            && [[ -n "$(find "${path}" -mindepth 1 -print -quit)" ]]; then
        echo "[ERROR] Refusing to overwrite non-empty ${label}: ${path}" >&2
        echo "[ERROR] Select a fresh versioned output directory." >&2
        return 1
    fi
    if [[ -e "${path}" && ! -d "${path}" ]]; then
        echo "[ERROR] ${label} is not a directory: ${path}" >&2
        return 1
    fi
    mkdir -p "${path}"
}

require_absent_output() {
    local label=$1 path=$2
    if [[ -e "${path}" || -L "${path}" ]]; then
        echo "[ERROR] Refusing to overwrite existing ${label}: ${path}" >&2
        return 1
    fi
}

sha256_file() {
    shasum -a 256 "$1" | awk '{print $1}'
}

jsonl_row_count() {
    jq -s 'length' "$1"
}

require_recorded_hash() {
    local label=$1 path=$2 expected=$3 actual
    if [[ -z "${path}" || "${path}" != /* || ! -f "${path}" ]]; then
        echo "[ERROR] ${label} is not an absolute regular file: ${path}" >&2
        return 1
    fi
    if [[ -z "${expected}" ]]; then
        echo "[ERROR] ${label} has no recorded SHA-256" >&2
        return 1
    fi
    actual=$(sha256_file "${path}")
    if [[ "${actual}" != "${expected}" ]]; then
        echo "[ERROR] ${label} SHA-256 mismatch" >&2
        echo "[ERROR] Expected: ${expected}" >&2
        echo "[ERROR] Actual:   ${actual}" >&2
        return 1
    fi
}

campaign_state_role_path() {
    local role=$1 file count
    count=$(jq -r --arg role "${role}" \
        '[.stateFiles[] | select(.role == $role)] | length' \
        "${campaign_generation_manifest}")
    if [[ "${count}" -ne 1 ]]; then
        echo "[ERROR] Campaign generation does not contain one ${role} file" >&2
        return 1
    fi
    file=$(jq -r --arg role "${role}" \
        '[.stateFiles[] | select(.role == $role)][0].file' \
        "${campaign_generation_manifest}")
    if [[ -z "${file}" || "$(basename "${file}")" != "${file}" ]]; then
        echo "[ERROR] Campaign ${role} filename escapes its immutable generation: ${file}" >&2
        return 1
    fi
    printf '%s/%s' "$(dirname "${campaign_generation_manifest}")" "${file}"
}

# Resolve only the immutable generation named by the atomic campaign pointer.
# Convenience copies in the campaign directory are intentionally ignored.
validate_campaign_generation() {
    local pointer=$1 manifest_relative expected actual role state_file
    local recorded_lines actual_lines recorded_sha
    local completion_relative completion_file completion_sha
    require_no_symlink_components "campaign state pointer" "${pointer}"
    campaign_state_pointer=$(realpath "${pointer}")
    require_nonempty_input "campaign state pointer" \
        "${campaign_state_pointer}"
    if ! jq -e '
            .schemaVersion == 2
            and .kind == "CONCOLIC_CAMPAIGN_STATE_POINTER"
            and .complete == true
            and ((.generation // "") | length) > 0
            and ((.manifest // "") | length) > 0
            and ((.manifestSha256 // "") | length) == 64
            and ((.campaignCompleteManifest // "") | length) > 0
            and ((.campaignCompleteManifestSha256 // "") | length) == 64' \
            "${campaign_state_pointer}" >/dev/null; then
        echo "[ERROR] Campaign state pointer is incomplete" >&2
        return 1
    fi
    campaign_generation=$(jq -r '.generation' "${campaign_state_pointer}")
    manifest_relative=$(jq -r '.manifest' "${campaign_state_pointer}")
    if [[ "${manifest_relative}" == /* ]]; then
        echo "[ERROR] Campaign generation manifest pointer must be relative" >&2
        return 1
    fi
    campaign_generation_manifest=$(realpath -m \
        "$(dirname "${campaign_state_pointer}")/${manifest_relative}")
    case "${campaign_generation_manifest}" in
        "$(dirname "${campaign_state_pointer}")/state-generations/${campaign_generation}/"*) ;;
        *)
            echo "[ERROR] Campaign pointer escapes its named immutable generation" >&2
            return 1
            ;;
    esac
    require_no_symlink_components "campaign generation manifest" \
        "${campaign_generation_manifest}"
    require_nonempty_input "campaign generation manifest" \
        "${campaign_generation_manifest}"
    expected=$(jq -r '.manifestSha256' "${campaign_state_pointer}")
    require_recorded_hash "campaign generation manifest" \
        "${campaign_generation_manifest}" "${expected}"
    if ! jq -e --arg generation "${campaign_generation}" '
            .schemaVersion == 2
            and .kind == "CONCOLIC_CAMPAIGN_STATE_GENERATION"
            and .complete == true
            and .generation == $generation
            and (.stateFiles | type == "array" and length == 7)
            and ([.stateFiles[].role] | sort)
                == (["ACTIVATIONS", "EDGES", "PATH_RECORDS", "REGIONS",
                     "ROOTS", "STATIC_GRAPH", "SUMMARIES"] | sort)
            and ([.stateFiles[].role] | unique | length) == 7
            and ((.campaignCompleteManifest // "") | length) > 0
            and ((.campaignCompleteManifestSha256 // "") | length) == 64
            and all(.stateFiles[];
                ((.file // "") | length) > 0
                and ((.sha256 // "") | length) == 64
                and ((.lineCount | type) == "number")
                and .lineCount >= 0)' \
            "${campaign_generation_manifest}" >/dev/null; then
        echo "[ERROR] Campaign generation manifest has an incomplete state ledger" >&2
            return 1
    fi
    completion_relative=$(jq -r '.campaignCompleteManifest' \
        "${campaign_state_pointer}")
    if [[ "${completion_relative}" == /* ]]; then
        echo "[ERROR] Campaign completion snapshot pointer must be relative" >&2
        return 1
    fi
    campaign_completion_manifest=$(realpath -m \
        "$(dirname "${campaign_state_pointer}")/${completion_relative}")
    completion_file=$(jq -r '.campaignCompleteManifest' \
        "${campaign_generation_manifest}")
    completion_sha=$(jq -r '.campaignCompleteManifestSha256' \
        "${campaign_generation_manifest}")
    if [[ "${campaign_completion_manifest}" \
                != "$(dirname "${campaign_generation_manifest}")/${completion_file}" \
            || "${completion_sha}" \
                != "$(jq -r '.campaignCompleteManifestSha256' \
                    "${campaign_state_pointer}")" ]]; then
        echo "[ERROR] Campaign completion snapshot is not bound to the named generation" >&2
        return 1
    fi
    require_no_symlink_components "campaign completion snapshot" \
        "${campaign_completion_manifest}"
    require_recorded_hash "campaign completion snapshot" \
        "${campaign_completion_manifest}" "${completion_sha}"
    if ! jq -e '.kind == "CONCOLIC_REGION_CAMPAIGN"' \
            "${campaign_completion_manifest}" >/dev/null; then
        echo "[ERROR] Campaign completion snapshot is not a campaign manifest" >&2
        return 1
    fi
    for role in REGIONS ACTIVATIONS EDGES ROOTS SUMMARIES PATH_RECORDS \
            STATIC_GRAPH; do
        state_file=$(campaign_state_role_path "${role}")
        require_no_symlink_components "campaign ${role}" "${state_file}"
        recorded_sha=$(jq -r --arg role "${role}" \
            '[.stateFiles[] | select(.role == $role)][0].sha256' \
            "${campaign_generation_manifest}")
        require_recorded_hash "campaign ${role}" \
            "${state_file}" "${recorded_sha}"
        if ! jq -e -s '.' "${state_file}" >/dev/null; then
            echo "[ERROR] Campaign ${role} is not valid JSONL" >&2
            return 1
        fi
        recorded_lines=$(jq -r --arg role "${role}" \
            '[.stateFiles[] | select(.role == $role)][0].lineCount' \
            "${campaign_generation_manifest}")
        actual_lines=$(jsonl_row_count "${state_file}")
        if [[ "${actual_lines}" -ne "${recorded_lines}" ]]; then
            echo "[ERROR] Campaign ${role} lineCount mismatch" >&2
            return 1
        fi
    done
    campaign_regions=$(campaign_state_role_path REGIONS)
    campaign_activations=$(campaign_state_role_path ACTIVATIONS)
    campaign_edges=$(campaign_state_role_path EDGES)
    campaign_roots=$(campaign_state_role_path ROOTS)
    campaign_summaries=$(campaign_state_role_path SUMMARIES)
    campaign_path_records=$(campaign_state_role_path PATH_RECORDS)
    campaign_static_graph=$(campaign_state_role_path STATIC_GRAPH)
    for state_file in "${campaign_regions}" "${campaign_activations}" \
            "${campaign_edges}" "${campaign_roots}" \
            "${campaign_summaries}" "${campaign_static_graph}"; do
        if [[ ! -s "${state_file}" ]]; then
            echo "[ERROR] Completed fresh handoff requires non-empty immutable state: ${state_file}" >&2
            return 1
        fi
    done
    actual=$(sha256_file "${campaign_state_pointer}")
    campaign_state_pointer_sha256="${actual}"
    campaign_generation_manifest_sha256="${expected}"
}

validate_schedule_provenance() {
    local provenance=$1 require_fresh=${2:-false}
    local path_field sha_field path expected
    require_nonempty_input "schedule input provenance" "${provenance}"
    if ! jq -e '
            .schemaVersion >= 2
            and .kind == "CONCOLIC_SCHEDULE_INPUT_PROVENANCE"
            and .complete == true
            and ((.activationId // "") | length) > 0
            and ((.regionId // "") | length) > 0
            and ((.regionInstanceId // "") | length) > 0' \
            "${provenance}" >/dev/null; then
        echo "[ERROR] Schedule provenance is not complete schema 2" >&2
        return 1
    fi
    if [[ "${require_fresh}" == "true" ]] && ! jq -e '
            .authority
                == "IMMUTABLE_CAMPAIGN_GENERATION_FRESH_TARGET_SCHEDULE"
            and ((.summaries // "") | length) > 0
            and ((.pathRecords // "") | length) > 0
            and ((.exactTargetRoot // "") | length) > 0' \
            "${provenance}" >/dev/null; then
        echo "[ERROR] Fresh schedule provenance lacks immutable campaign authority" >&2
        return 1
    fi
    while IFS=$'\t' read -r path_field sha_field; do
        path=$(jq -r --arg field "${path_field}" '.[$field] // ""' \
            "${provenance}")
        expected=$(jq -r --arg field "${sha_field}" '.[$field] // ""' \
            "${provenance}")
        if [[ -z "${path}" && "${path_field}" =~ ^(summaries|pathRecords|exactTargetRoot)$ \
                && "${require_fresh}" != "true" ]]; then
            continue
        fi
        require_recorded_hash "schedule provenance ${path_field}" \
            "${path}" "${expected}"
    done <<'EOF'
graphCheckerJar	graphCheckerJarSha256
activationPlan	activationPlanSha256
edgeValidations	edgeValidationsSha256
regions	regionsSha256
staticGraph	staticGraphSha256
summaries	summariesSha256
pathRecords	pathRecordsSha256
exactTargetRoot	exactTargetRootSha256
concolicSchedule	concolicScheduleSha256
scheduledActivationPlan	scheduledActivationPlanSha256
branchQueries	branchQueriesSha256
symbolicMergePlan	symbolicMergePlanSha256
schedulerSummary	schedulerSummarySha256
EOF
    schedule_provenance_activation_id=$(jq -r '.activationId' "${provenance}")
    schedule_provenance_region_id=$(jq -r '.regionId' "${provenance}")
    schedule_provenance_region_instance_id=$(jq -r '.regionInstanceId' \
        "${provenance}")
}

handoff_artifact_path() {
    local manifest=$1 role=$2 count
    count=$(jq -r --arg role "${role}" \
        '[.artifacts[] | select(.role == $role)] | length' "${manifest}")
    if [[ "${count}" -ne 1 ]]; then
        echo "[ERROR] Fresh handoff does not contain one ${role} artifact" >&2
        return 1
    fi
    jq -r --arg role "${role}" \
        '[.artifacts[] | select(.role == $role)][0].path' "${manifest}"
}

write_admitted_upstream_summaries() {
    local summaries=$1 target_summary_id=$2 output=$3
    jq -c --arg target "${target_summary_id}" '
        select((.summaryId // "") != $target
            and ((.summaryId // "") | length) > 0
            and ((.regionId // "") | length) > 0
            and .valid == true
            and (.discoveryOnly // false) == false
            and (.branchOverrideUsed // false) == false
            and (((.summaryCacheAdmission // "") | ascii_upcase
                    | contains("QUARANTINED")) | not)
            and .captureGoal.kind == "OUTPUT_CLOSURE"
            and ((.regionRelation.kind == "GUARDED_PATH_MERGE"
                    and .regionRelation.complete == true
                    and .relationallyComplete == true)
                or (.executionAdmission.valid == true
                    and (.executionAdmission.branchOverrideAccepted // false)
                        == false)))' "${summaries}" > "${output}"
}

require_exact_derived_campaign_rows() {
    local roots=$1 summaries=$2 exact_root=$3 exact_summary=$4 upstream=$5
    local activation=$6 region=$7 instance=$8 summary_id=$9
    local selected_root selected_summary
    selected_root=$(jq -S -c -s --arg activation "${activation}" \
        --arg region "${region}" --arg instance "${instance}" \
        --arg summary "${summary_id}" '
        [.[] | select(.activationId == $activation
            and .regionId == $region and .regionInstanceId == $instance
            and .validatedSummaryId == $summary)]
        | if length == 1 then .[0] else error("root-not-unique") end' \
        "${roots}") || {
        echo "[ERROR] Immutable campaign ROOTS lacks one exact fresh root" >&2
        return 1
    }
    if [[ "${selected_root}" != "$(jq -S -c -s '
            if length == 1 then .[0] else error("root-row-count") end' \
            "${exact_root}")" ]]; then
        echo "[ERROR] FRESH_TARGET_ROOT is not the exact ROOTS ledger row" >&2
        return 1
    fi
    selected_summary=$(jq -S -c -s --arg activation "${activation}" \
        --arg region "${region}" --arg instance "${instance}" \
        --arg summary "${summary_id}" '
        [.[] | select(.summaryId == $summary
            and .activationId == $activation and .regionId == $region
            and .regionInstanceId == $instance)]
        | if length == 1 then .[0] else error("summary-not-unique") end' \
        "${summaries}") || {
        echo "[ERROR] Immutable campaign SUMMARIES lacks one exact target summary" >&2
        return 1
    }
    if [[ "${selected_summary}" != "$(jq -S -c -s '
            if length == 1 then .[0] else error("summary-row-count") end' \
            "${exact_summary}")" ]]; then
        echo "[ERROR] FRESH_TARGET_SUMMARY is not the exact SUMMARIES ledger row" >&2
        return 1
    fi
    if ! cmp -s \
            <(jq -S -c --arg target "${summary_id}" '
                select((.summaryId // "") != $target
                    and ((.summaryId // "") | length) > 0
                    and ((.regionId // "") | length) > 0
                    and .valid == true
                    and (.discoveryOnly // false) == false
                    and (.branchOverrideUsed // false) == false
                    and (((.summaryCacheAdmission // "") | ascii_upcase
                            | contains("QUARANTINED")) | not)
                    and .captureGoal.kind == "OUTPUT_CLOSURE"
                    and ((.regionRelation.kind == "GUARDED_PATH_MERGE"
                            and .regionRelation.complete == true
                            and .relationallyComplete == true)
                        or (.executionAdmission.valid == true
                            and (.executionAdmission.branchOverrideAccepted
                                // false) == false)))' "${summaries}") \
            <(jq -S -c '.' "${upstream}"); then
        echo "[ERROR] UPSTREAM_SUMMARIES is not the exact admitted projection of SUMMARIES" >&2
        return 1
    fi
    if [[ "$(jsonl_row_count "${upstream}")" -lt 1 ]]; then
        echo "[ERROR] Fresh campaign handoff has no admitted upstream summary" >&2
        return 1
    fi
}

require_complete_campaign_authority() {
    local manifest=$1
    if ! jq -e '
            .schemaVersion == 1
            and .kind == "CONCOLIC_REGION_CAMPAIGN"
            and .complete == true
            and .postDiscoveryTargetRebaseCompleted == true
            and .postDiscoveryTargetRebaseRequired == false
            and .postDiscoveryTargetRebaseReady == true
            and .targetRootAdmissionComplete == true
            and .branchOverrideAccepted == false
            and .postDiscoveryTargetRebase.authority
                == "FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_TARGET_REPLAY"
            and (if (.transitionFocusOnly // false) then
                    .focusedTargetComplete == true
                    and .status == "COMPLETE_FOCUSED_TRANSITION_DISCOVERY"
                    and .transitionDiscovery.complete == true
                 else
                    .status == "COMPLETE_AUTOMATIC_REGION_CLOSURE"
                    and (.gapCount // -1) == 0
                    and .graphWorklist.complete == true
                    and .pathWorklist.complete == true
                    and .relationMerge.complete == true
                    and .transitionDiscovery.complete == true
                 end)' "${manifest}" >/dev/null; then
        echo "[ERROR] Campaign completion authority is incomplete or internally inconsistent" >&2
        return 1
    fi
}

validate_campaign_handoff_manifest() {
    local manifest=$1 role path expected recorded_lines actual_lines
    local pointer_snapshot generation_manifest complete_manifest
    local graphchecker_artifact root summary upstream branches plan provenance
    local state_path state_sha state_lines artifact_sha artifact_lines
    local root_formula branch_formula handoff_root canonical expected_state_path
    require_no_symlink_components "fresh campaign handoff manifest" \
        "${manifest}"
    manifest=$(realpath "${manifest}")
    handoff_root=$(dirname "${manifest}")
    require_nonempty_input "fresh campaign handoff" "${manifest}"
    if ! jq -e '
            .schemaVersion == 1
            and .kind == "CONCOLIC_CAMPAIGN_FRESH_TARGET_HANDOFF"
            and .complete == true
            and .authority
                == "IMMUTABLE_COMPLETE_CAMPAIGN_FRESH_TARGET_SCHEDULE"
            and ((.generation // "") | length) > 0
            and ((.identity.activationId // "") | length) > 0
            and ((.identity.regionId // "") | length) > 0
            and ((.identity.regionInstanceId // "") | length) > 0
            and ((.identity.summaryId // "") | length) > 0
            and (.artifacts | type == "array" and length == 20)
            and ([.artifacts[].role] | sort) == ([
                "ACTIVATIONS", "BRANCH_QUERIES", "CAMPAIGN_COMPLETE_MANIFEST",
                "CONCOLIC_SCHEDULE", "EDGES", "FRESH_TARGET_ROOT",
                "FRESH_TARGET_SUMMARY", "GENERATION_MANIFEST",
                "GRAPH_CHECKER_JAR", "PATH_RECORDS", "REGIONS", "ROOTS",
                "SCHEDULED_ACTIVATION_PLAN", "SCHEDULE_PROVENANCE",
                "SCHEDULER_SUMMARY", "STATE_POINTER_SNAPSHOT", "STATIC_GRAPH",
                "SUMMARIES", "SYMBOLIC_MERGE_PLAN", "UPSTREAM_SUMMARIES"]
                | sort)
            and ([.artifacts[].role] | unique | length) == 20' \
            "${manifest}" >/dev/null; then
        echo "[ERROR] Fresh campaign handoff schema/authority is incomplete" >&2
        return 1
    fi
    while IFS=$'\t' read -r role path expected recorded_lines; do
        canonical=$(realpath "${path}")
        require_no_symlink_components "handoff ${role}" "${path}"
        if [[ "${role}" != "GRAPH_CHECKER_JAR" ]]; then
            case "${canonical}" in
                "${handoff_root}"/*) ;;
                *)
                    echo "[ERROR] Handoff ${role} escapes its private artifact tree: ${canonical}" >&2
                    return 1
                    ;;
            esac
        fi
        require_recorded_hash "handoff ${role}" "${path}" "${expected}"
        if [[ "${recorded_lines}" != "" && "${recorded_lines}" != "null" ]]; then
            if ! jq -e -s '.' "${path}" >/dev/null; then
                echo "[ERROR] Handoff ${role} is not valid JSONL" >&2
                return 1
            fi
            actual_lines=$(jsonl_row_count "${path}")
            if [[ "${actual_lines}" -ne "${recorded_lines}" ]]; then
                echo "[ERROR] Handoff ${role} lineCount mismatch" >&2
                return 1
            fi
        fi
    done < <(jq -r '.artifacts[]
        | [.role, .path, .sha256, (.lineCount // "")] | @tsv' \
        "${manifest}")

    pointer_snapshot=$(handoff_artifact_path "${manifest}" \
        STATE_POINTER_SNAPSHOT)
    generation_manifest=$(handoff_artifact_path "${manifest}" \
        GENERATION_MANIFEST)
    complete_manifest=$(handoff_artifact_path "${manifest}" \
        CAMPAIGN_COMPLETE_MANIFEST)
    validate_campaign_generation "${pointer_snapshot}"
    if [[ "$(realpath "${generation_manifest}")" \
                != "$(realpath "${campaign_generation_manifest}")" \
            || "$(realpath "${complete_manifest}")" \
                != "$(realpath "${campaign_completion_manifest}")" \
            || "${campaign_generation}" \
                != "$(jq -r '.generation' "${manifest}")" ]]; then
        echo "[ERROR] Handoff private campaign snapshot paths/identity are inconsistent" >&2
        return 1
    fi
    require_complete_campaign_authority "${complete_manifest}"
    if ! jq -e \
            --arg pointerSha "$(sha256_file "${pointer_snapshot}")" \
            --arg campaignSha "$(sha256_file "${complete_manifest}")" '
            .source.campaignStatePointerSha256 == $pointerSha
            and .source.campaignCompleteManifestSha256 == $campaignSha
            and ((.source.campaignStatePointer // "") | startswith("/"))
            and ((.source.campaignCompleteManifest // "") | startswith("/"))' \
            "${manifest}" >/dev/null; then
        echo "[ERROR] Handoff source pointer/campaign hashes are not bound to their snapshots" >&2
        return 1
    fi
    if ! jq -e --arg generation "$(jq -r '.generation' "${manifest}")" \
            --arg sha "$(sha256_file "${generation_manifest}")" '
            .schemaVersion == 2
            and .kind == "CONCOLIC_CAMPAIGN_STATE_POINTER"
            and .complete == true
            and .generation == $generation
            and .manifestSha256 == $sha' "${pointer_snapshot}" >/dev/null; then
        echo "[ERROR] Handoff pointer snapshot does not bind its generation manifest" >&2
        return 1
    fi
    if ! jq -e --arg generation "$(jq -r '.generation' "${manifest}")" '
            .schemaVersion == 2
            and .kind == "CONCOLIC_CAMPAIGN_STATE_GENERATION"
            and .complete == true and .generation == $generation
            and (.stateFiles | type == "array" and length == 7)
            and ([.stateFiles[].role] | sort)
                == (["ACTIVATIONS", "EDGES", "PATH_RECORDS", "REGIONS",
                     "ROOTS", "STATIC_GRAPH", "SUMMARIES"] | sort)
            and ([.stateFiles[].role] | unique | length) == 7' \
            "${generation_manifest}" >/dev/null; then
        echo "[ERROR] Handoff generation identity mismatch" >&2
        return 1
    fi
    for role in REGIONS ACTIVATIONS EDGES ROOTS SUMMARIES PATH_RECORDS \
            STATIC_GRAPH; do
        state_path=$(handoff_artifact_path "${manifest}" "${role}")
        case "${role}" in
            REGIONS) expected_state_path="${campaign_regions}" ;;
            ACTIVATIONS) expected_state_path="${campaign_activations}" ;;
            EDGES) expected_state_path="${campaign_edges}" ;;
            ROOTS) expected_state_path="${campaign_roots}" ;;
            SUMMARIES) expected_state_path="${campaign_summaries}" ;;
            PATH_RECORDS) expected_state_path="${campaign_path_records}" ;;
            STATIC_GRAPH) expected_state_path="${campaign_static_graph}" ;;
        esac
        state_sha=$(jq -r --arg role "${role}" \
            '[.stateFiles[] | select(.role == $role)][0].sha256 // ""' \
            "${generation_manifest}")
        state_lines=$(jq -r --arg role "${role}" \
            '[.stateFiles[] | select(.role == $role)][0].lineCount // -1' \
            "${generation_manifest}")
        artifact_sha=$(jq -r --arg role "${role}" \
            '[.artifacts[] | select(.role == $role)][0].sha256' \
            "${manifest}")
        artifact_lines=$(jq -r --arg role "${role}" \
            '[.artifacts[] | select(.role == $role)][0].lineCount // -1' \
            "${manifest}")
        if [[ "$(realpath "${state_path}")" \
                    != "$(realpath "${expected_state_path}")" \
                || -z "${state_sha}" || "${state_sha}" != "${artifact_sha}" \
                || "${state_lines}" -ne "${artifact_lines}" \
                || "$(basename "${state_path}")" != "$(jq -r --arg role "${role}" \
                    '[.stateFiles[] | select(.role == $role)][0].file' \
                    "${generation_manifest}")" ]]; then
            echo "[ERROR] Handoff ${role} does not match the immutable generation ledger" >&2
            return 1
        fi
    done

    handoff_activation_id=$(jq -r '.identity.activationId' "${manifest}")
    handoff_region_id=$(jq -r '.identity.regionId' "${manifest}")
    handoff_region_instance_id=$(jq -r '.identity.regionInstanceId' \
        "${manifest}")
    handoff_summary_id=$(jq -r '.identity.summaryId' "${manifest}")
    if ! jq -e --arg activation "${handoff_activation_id}" \
            --arg region "${handoff_region_id}" \
            --arg instance "${handoff_region_instance_id}" '
            .complete == true
            and .postDiscoveryTargetRebaseCompleted == true
            and .postDiscoveryTargetRebaseRequired == false
            and .postDiscoveryTargetRebaseReady == true
            and .targetRootAdmissionComplete == true
            and .branchOverrideAccepted == false
            and .postDiscoveryTargetRebaseActivationId == $activation
            and .postDiscoveryTargetRebaseRegionInstanceId == $instance
            and .postDiscoveryTargetRebase.activationId == $activation
            and .postDiscoveryTargetRebase.regionId == $region
            and .postDiscoveryTargetRebase.regionInstanceId == $instance
            and .postDiscoveryTargetRebase.authority
                == "FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_TARGET_REPLAY"' \
            "${complete_manifest}" >/dev/null; then
        echo "[ERROR] Handoff campaign manifest does not authorize its fresh target" >&2
        return 1
    fi
    root=$(handoff_artifact_path "${manifest}" FRESH_TARGET_ROOT)
    summary=$(handoff_artifact_path "${manifest}" FRESH_TARGET_SUMMARY)
    branches=$(handoff_artifact_path "${manifest}" BRANCH_QUERIES)
    plan=$(handoff_artifact_path "${manifest}" SCHEDULED_ACTIVATION_PLAN)
    if ! jq -e -s --arg activation "${handoff_activation_id}" \
            --arg region "${handoff_region_id}" \
            --arg instance "${handoff_region_instance_id}" \
            --arg summary "${handoff_summary_id}" '
            length == 1
            and .[0].activationId == $activation
            and .[0].regionId == $region
            and .[0].regionInstanceId == $instance
            and .[0].validatedSummaryId == $summary
            and .[0].readyForSolver == true
            and .[0].replayAlreadyValidated == true
            and .[0].targetReplayValidated == true
            and .[0].replayValidationAuthority
                == "FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_TARGET_REPLAY"
            and .[0].targetRebaseProvenance.downstreamInjectionUsed == false
            and .[0].targetRebaseProvenance.branchOverrideUsed == false' \
            "${root}" >/dev/null; then
        echo "[ERROR] Handoff exact fresh root identity/authority is invalid" >&2
        return 1
    fi
    upstream=$(handoff_artifact_path "${manifest}" UPSTREAM_SUMMARIES)
    require_exact_derived_campaign_rows \
        "$(handoff_artifact_path "${manifest}" ROOTS)" \
        "$(handoff_artifact_path "${manifest}" SUMMARIES)" \
        "${root}" "${summary}" "${upstream}" \
        "${handoff_activation_id}" "${handoff_region_id}" \
        "${handoff_region_instance_id}" "${handoff_summary_id}"
    if ! jq -e -s --arg activation "${handoff_activation_id}" \
            --arg region "${handoff_region_id}" \
            --arg instance "${handoff_region_instance_id}" \
            --arg summary "${handoff_summary_id}" '
            length == 1
            and .[0].summaryId == $summary
            and .[0].activationId == $activation
            and .[0].regionId == $region
            and .[0].regionInstanceId == $instance
            and .[0].valid == true
            and .[0].targetReplayValidated == true
            and .[0].branchOverrideUsed == false
            and .[0].executionAdmission.required == true
            and .[0].executionAdmission.valid == true
            and .[0].executionAdmission.branchOverrideAccepted == false
            and .[0].executionAdmission.authority
                == "SOLVER_MODEL_PLUS_UNFORCED_BRANCH_AND_EXCEPTION_OBSERVATION"' \
            "${summary}" >/dev/null; then
        echo "[ERROR] Handoff exact fresh target summary admission is invalid" >&2
        return 1
    fi
    if ! jq -e -s --arg activation "${handoff_activation_id}" \
            --arg region "${handoff_region_id}" \
            --arg instance "${handoff_region_instance_id}" \
            --arg summary "${handoff_summary_id}" '
            length == 1
            and .[0].activationId == $activation
            and .[0].regionId == $region
            and .[0].regionInstanceId == $instance
            and .[0].validatedSummaryId == $summary
            and .[0].readyForSolver == true
            and .[0].replayAlreadyValidated == true
            and .[0].targetReplayValidated == true
            and .[0].replayValidationAuthority
                == "FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_TARGET_REPLAY"' \
            "${branches}" >/dev/null; then
        echo "[ERROR] Handoff fresh scheduled branch query identity is invalid" >&2
        return 1
    fi
    root_formula=$(jq -S -c '{activationId,regionId,regionInstanceId,
        siteId,occurrence,desiredOutcome,conditionIndex,constraints,
        freshObservedTargetCondition,negatedTargetCondition,
        engineArrayInputBindings,symbolicContext,formulaAuthority,
        targetPolicy,freshQueryRebuildProvenance}' "${root}")
    branch_formula=$(jq -S -c '{activationId,regionId,regionInstanceId,
        siteId,occurrence,desiredOutcome,conditionIndex,constraints,
        freshObservedTargetCondition,negatedTargetCondition,
        engineArrayInputBindings,symbolicContext,formulaAuthority,
        targetPolicy,freshQueryRebuildProvenance}' "${branches}")
    if [[ "${root_formula}" != "${branch_formula}" ]]; then
        echo "[ERROR] Fresh scheduled query formula differs from the immutable campaign root" >&2
        return 1
    fi
    if [[ "$(jq -r -s --arg activation "${handoff_activation_id}" \
            --arg region "${handoff_region_id}" \
            --arg instance "${handoff_region_instance_id}" \
            '[.[] | select(.activationId == $activation
                and .regionId == $region and .regionInstanceId == $instance
                and ((.activationBundleMemberRole // "PRIMARY") == "PRIMARY"))]
            | length' "${plan}")" -ne 1 ]]; then
        echo "[ERROR] Handoff scheduled plan lacks one exact primary target" >&2
        return 1
    fi
    provenance=$(handoff_artifact_path "${manifest}" SCHEDULE_PROVENANCE)
    validate_schedule_provenance "${provenance}" true
    if [[ "${schedule_provenance_activation_id}" != "${handoff_activation_id}" \
            || "${schedule_provenance_region_id}" != "${handoff_region_id}" \
            || "${schedule_provenance_region_instance_id}" \
                != "${handoff_region_instance_id}" ]]; then
        echo "[ERROR] Handoff schedule provenance target identity mismatch" >&2
        return 1
    fi
    if [[ "$(realpath "$(jq -r '.activationPlan' "${provenance}")")" \
                != "$(realpath "$(handoff_artifact_path \
                    "${manifest}" ACTIVATIONS)")" \
            || "$(realpath "$(jq -r '.edgeValidations' "${provenance}")")" \
                != "$(realpath "$(handoff_artifact_path \
                    "${manifest}" EDGES)")" \
            || "$(realpath "$(jq -r '.regions' "${provenance}")")" \
                != "$(realpath "$(handoff_artifact_path \
                    "${manifest}" REGIONS)")" \
            || "$(realpath "$(jq -r '.staticGraph' "${provenance}")")" \
                != "$(realpath "$(handoff_artifact_path \
                    "${manifest}" STATIC_GRAPH)")" \
            || "$(realpath "$(jq -r '.summaries' "${provenance}")")" \
                != "$(realpath "$(handoff_artifact_path \
                    "${manifest}" SUMMARIES)")" \
            || "$(realpath "$(jq -r '.pathRecords' "${provenance}")")" \
                != "$(realpath "$(handoff_artifact_path \
                    "${manifest}" PATH_RECORDS)")" \
            || "$(realpath "$(jq -r '.exactTargetRoot' "${provenance}")")" \
                != "$(realpath "${root}")" \
            || "$(realpath "$(jq -r '.branchQueries' "${provenance}")")" \
                != "$(realpath "${branches}")" \
            || "$(realpath "$(jq -r '.scheduledActivationPlan' \
                    "${provenance}")")" != "$(realpath "${plan}")" \
            || "$(realpath "$(jq -r '.symbolicMergePlan' \
                    "${provenance}")")" != "$(realpath \
                    "$(handoff_artifact_path "${manifest}" \
                        SYMBOLIC_MERGE_PLAN)")" ]]; then
        echo "[ERROR] Handoff schedule provenance does not use the exact immutable campaign inputs/outputs" >&2
        return 1
    fi
    graphchecker_artifact=$(handoff_artifact_path "${manifest}" \
        GRAPH_CHECKER_JAR)
    if [[ "$(realpath "${gc_jar}")" != "$(realpath "${graphchecker_artifact}")" ]]; then
        echo "[ERROR] Current GraphChecker jar path differs from fresh handoff" >&2
        return 1
    fi

    handoff_manifest="${manifest}"
    handoff_target_schedule_dir=$(dirname "${branches}")
    handoff_target_summary="${summary}"
    handoff_composition_summaries=$(handoff_artifact_path "${manifest}" \
        UPSTREAM_SUMMARIES)
    handoff_regions=$(handoff_artifact_path "${manifest}" REGIONS)
    handoff_static_graph=$(handoff_artifact_path "${manifest}" STATIC_GRAPH)
    handoff_activations=$(handoff_artifact_path "${manifest}" ACTIVATIONS)
    handoff_edges=$(handoff_artifact_path "${manifest}" EDGES)
    handoff_all_summaries=$(handoff_artifact_path "${manifest}" SUMMARIES)
    handoff_root="${root}"
    handoff_complete_manifest="${complete_manifest}"
    echo "[Concolic] verified fresh campaign handoff: ${manifest}"
}

handoff_artifact_json() {
    local role=$1 path=$2 line_count=${3:-}
    local sha
    path=$(realpath "${path}")
    sha=$(sha256_file "${path}")
    if [[ -n "${line_count}" ]]; then
        jq -nc --arg role "${role}" --arg path "${path}" \
            --arg sha "${sha}" --argjson lines "${line_count}" \
            '{role:$role, path:$path, sha256:$sha, lineCount:$lines}'
    else
        jq -nc --arg role "${role}" --arg path "${path}" \
            --arg sha "${sha}" \
            '{role:$role, path:$path, sha256:$sha}'
    fi
}

publish_campaign_handoff() {
    local test_name=$1 campaign_dir=$2 campaign_manifest
    local activation_id region_id region_instance_id summary_id
    local jar_sha generation_key handoff_dir schedule_dir final_manifest
    local publish_lock
    local pointer_snapshot complete_snapshot exact_root exact_summary
    local upstream_summaries artifacts_json manifest_tmp
    local original_pointer_sha original_generation_sha original_campaign_sha
    local source_pointer source_generation_manifest source_completion_manifest
    local source_regions source_activations source_edges source_roots
    local source_summaries source_path_records source_static_graph
    local snapshot_generation_dir
    local schedule_provenance
    local root_formula branch_formula
    campaign_dir=$(realpath "${campaign_dir}")
    validate_campaign_generation \
        "${campaign_dir}/campaign_state_manifest.json"
    campaign_manifest="${campaign_completion_manifest}"
    require_nonempty_input "campaign completion manifest" \
        "${campaign_manifest}"
    require_complete_campaign_authority "${campaign_manifest}"
    activation_id=$(jq -r '.postDiscoveryTargetRebaseActivationId' \
        "${campaign_manifest}")
    region_id=$(jq -r '.postDiscoveryTargetRebase.regionId' \
        "${campaign_manifest}")
    region_instance_id=$(jq -r \
        '.postDiscoveryTargetRebaseRegionInstanceId' \
        "${campaign_manifest}")
    if [[ -z "${activation_id}" || -z "${region_id}" \
            || -z "${region_instance_id}" ]]; then
        echo "[ERROR] Completed campaign lacks one exact fresh target identity" >&2
        return 1
    fi
    if ! jq -e -s --arg activation "${activation_id}" \
            --arg region "${region_id}" \
            --arg instance "${region_instance_id}" '
            [.[] | select(.activationId == $activation
                and .regionId == $region
                and .regionInstanceId == $instance)] | length == 1' \
            "${campaign_activations}" >/dev/null; then
        echo "[ERROR] Immutable campaign activations lack one exact fresh target" >&2
        return 1
    fi
    require_nonempty_input "GraphChecker jar" "${gc_jar}"
    source_pointer="${campaign_state_pointer}"
    source_generation_manifest="${campaign_generation_manifest}"
    source_completion_manifest="${campaign_completion_manifest}"
    source_regions="${campaign_regions}"
    source_activations="${campaign_activations}"
    source_edges="${campaign_edges}"
    source_roots="${campaign_roots}"
    source_summaries="${campaign_summaries}"
    source_path_records="${campaign_path_records}"
    source_static_graph="${campaign_static_graph}"
    original_pointer_sha="${campaign_state_pointer_sha256}"
    original_generation_sha="${campaign_generation_manifest_sha256}"
    original_campaign_sha=$(sha256_file "${campaign_manifest}")
    jar_sha=$(sha256_file "${gc_jar}")
    generation_key="${campaign_generation}-${campaign_generation_manifest_sha256:0:12}-${jar_sha:0:12}"
    handoff_dir="${campaign_dir}/fresh-handoffs/${generation_key}"
    require_workspace_output_path "fresh campaign handoff directory" \
        "${handoff_dir}"
    handoff_dir=$(realpath -m "${handoff_dir}")
    final_manifest="${handoff_dir}/campaign_handoff_manifest.json"
    publish_lock="${handoff_dir}.publish-lock"
    if [[ -s "${final_manifest}" ]]; then
        validate_campaign_handoff_manifest "${final_manifest}"
        if ! jq -e --arg generation "${campaign_generation}" \
                --arg pointer "${source_pointer}" \
                --arg pointerSha "${original_pointer_sha}" \
                --arg completion "${source_completion_manifest}" \
                --arg completionSha "${original_campaign_sha}" '
                .generation == $generation
                and .source.campaignStatePointer == $pointer
                and .source.campaignStatePointerSha256 == $pointerSha
                and .source.campaignCompleteManifest == $completion
                and .source.campaignCompleteManifestSha256 == $completionSha' \
                "${final_manifest}" >/dev/null; then
            echo "[ERROR] Existing handoff does not match the current atomic campaign source" >&2
            return 1
        fi
        echo "[Concolic] reusing immutable fresh handoff: ${final_manifest}"
        echo "[Concolic] fresh handoff manifest: ${final_manifest}"
        return 0
    fi
    if [[ -d "${handoff_dir}" \
            && -n "$(find "${handoff_dir}" -mindepth 1 -print -quit)" ]]; then
        echo "[ERROR] Partial fresh handoff exists without a complete manifest: ${handoff_dir}" >&2
        echo "[ERROR] It is retained for audit and will not be overwritten." >&2
        return 1
    fi
    if [[ -e "${publish_lock}" ]]; then
        echo "[ERROR] A partial or concurrent fresh handoff publication is retained: ${publish_lock}" >&2
        return 1
    fi
    mkdir -p "$(dirname "${handoff_dir}")"
    if ! mkdir "${publish_lock}"; then
        echo "[ERROR] Another publisher won the fresh handoff lock: ${publish_lock}" >&2
        return 1
    fi
    mkdir -p "${handoff_dir}"
    pointer_snapshot="${handoff_dir}/campaign_state_manifest.json"
    snapshot_generation_dir="${handoff_dir}/state-generations/${campaign_generation}"
    complete_snapshot="${snapshot_generation_dir}/campaign_complete_manifest.json"
    exact_root="${handoff_dir}/fresh_target_root.jsonl"
    exact_summary="${handoff_dir}/fresh_target_summary.jsonl"
    upstream_summaries="${handoff_dir}/upstream_summaries.jsonl"
    schedule_dir="${handoff_dir}/fresh-target-schedule"
    mkdir -p "${snapshot_generation_dir}"
    cp "${source_pointer}" "${pointer_snapshot}"
    cp "${source_generation_manifest}" \
        "${snapshot_generation_dir}/state_manifest.json"
    cp "${source_completion_manifest}" "${complete_snapshot}"
    cp "${source_regions}" \
        "${snapshot_generation_dir}/$(basename "${source_regions}")"
    cp "${source_activations}" \
        "${snapshot_generation_dir}/$(basename "${source_activations}")"
    cp "${source_edges}" \
        "${snapshot_generation_dir}/$(basename "${source_edges}")"
    cp "${source_roots}" \
        "${snapshot_generation_dir}/$(basename "${source_roots}")"
    cp "${source_summaries}" \
        "${snapshot_generation_dir}/$(basename "${source_summaries}")"
    cp "${source_path_records}" \
        "${snapshot_generation_dir}/$(basename "${source_path_records}")"
    cp "${source_static_graph}" \
        "${snapshot_generation_dir}/$(basename "${source_static_graph}")"
    validate_campaign_generation "${pointer_snapshot}"
    if [[ "${campaign_state_pointer_sha256}" != "${original_pointer_sha}" \
            || "${campaign_generation_manifest_sha256}" \
                != "${original_generation_sha}" \
            || "$(sha256_file "${campaign_completion_manifest}")" \
                != "${original_campaign_sha}" ]]; then
        echo "[ERROR] Private campaign snapshot does not match its atomic source pointer" >&2
        return 1
    fi
    chmod a-w "${pointer_snapshot}" "${campaign_generation_manifest}" \
        "${campaign_completion_manifest}" "${campaign_regions}" \
        "${campaign_activations}" "${campaign_edges}" "${campaign_roots}" \
        "${campaign_summaries}" "${campaign_path_records}" \
        "${campaign_static_graph}"
    chmod a-w "${snapshot_generation_dir}" \
        "${handoff_dir}/state-generations"

    if ! jq -c -s --arg activation "${activation_id}" \
            --arg region "${region_id}" \
            --arg instance "${region_instance_id}" '
            [.[] | select(.activationId == $activation
                and .regionId == $region
                and .regionInstanceId == $instance
                and .replayValidationAuthority
                    == "FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_TARGET_REPLAY")]
            | if length == 1 then .[0]
              else error("fresh target root is not unique") end' \
            "${campaign_roots}" > "${exact_root}"; then
        echo "[ERROR] Immutable campaign roots do not contain one authoritative fresh target" >&2
        return 1
    fi
    summary_id=$(jq -r '.validatedSummaryId // ""' "${exact_root}")
    if [[ -z "${summary_id}" ]]; then
        echo "[ERROR] Fresh target root does not name its validated summary" >&2
        return 1
    fi
    if ! jq -c -s --arg summary "${summary_id}" \
            --arg activation "${activation_id}" --arg region "${region_id}" \
            --arg instance "${region_instance_id}" '
            [.[] | select(.summaryId == $summary
                and .activationId == $activation and .regionId == $region
                and .regionInstanceId == $instance)]
            | if length == 1 then .[0]
              else error("fresh target summary is not unique") end' \
            "${campaign_summaries}" > "${exact_summary}"; then
        echo "[ERROR] Immutable campaign summaries do not contain the root's exact summary" >&2
        return 1
    fi
    write_admitted_upstream_summaries "${campaign_summaries}" \
        "${summary_id}" "${upstream_summaries}"
    require_exact_derived_campaign_rows "${campaign_roots}" \
        "${campaign_summaries}" "${exact_root}" "${exact_summary}" \
        "${upstream_summaries}" "${activation_id}" "${region_id}" \
        "${region_instance_id}" "${summary_id}"
    require_absent_output "fresh target schedule" "${schedule_dir}"
    CAUSYNTH_SCHEDULE_OUTPUT_DIR="${schedule_dir}" \
    CAUSYNTH_SCHEDULE_ACTIVATION_PLAN="${campaign_activations}" \
    CAUSYNTH_SCHEDULE_EDGE_VALIDATIONS="${campaign_edges}" \
    CAUSYNTH_SCHEDULE_REGIONS="${campaign_regions}" \
    CAUSYNTH_SCHEDULE_STATIC_GRAPH="${campaign_static_graph}" \
    CAUSYNTH_SCHEDULE_SUMMARIES="${campaign_summaries}" \
    CAUSYNTH_SCHEDULE_PATH_RECORDS="${campaign_path_records}" \
    CAUSYNTH_SCHEDULE_ROOT="${exact_root}" \
        do_schedule_concolic "${test_name}" "${region_id}" \
            "${activation_id}"
    schedule_provenance="${schedule_dir}/schedule_input_provenance.json"
    validate_schedule_provenance "${schedule_provenance}" true
    if [[ "${schedule_provenance_activation_id}" != "${activation_id}" \
            || "${schedule_provenance_region_id}" != "${region_id}" \
            || "${schedule_provenance_region_instance_id}" \
                != "${region_instance_id}" ]]; then
        echo "[ERROR] Fresh scheduler selected a different target identity" >&2
        return 1
    fi
    if ! jq -e -s --arg activation "${activation_id}" \
            --arg region "${region_id}" --arg instance "${region_instance_id}" \
            --arg summary "${summary_id}" '
            length == 1
            and .[0].activationId == $activation
            and .[0].regionId == $region
            and .[0].regionInstanceId == $instance
            and .[0].validatedSummaryId == $summary
            and .[0].readyForSolver == true
            and .[0].replayAlreadyValidated == true
            and .[0].targetReplayValidated == true
            and .[0].replayValidationAuthority
                == "FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_TARGET_REPLAY"' \
            "${schedule_dir}/branch_queries.jsonl" >/dev/null; then
        echo "[ERROR] Fresh scheduler did not emit the exact replay-validated query" >&2
        return 1
    fi
    root_formula=$(jq -S -c '{activationId,regionId,regionInstanceId,
        siteId,occurrence,desiredOutcome,conditionIndex,constraints,
        freshObservedTargetCondition,negatedTargetCondition,
        engineArrayInputBindings,symbolicContext,formulaAuthority,
        targetPolicy,freshQueryRebuildProvenance}' "${exact_root}")
    branch_formula=$(jq -S -c '{activationId,regionId,regionInstanceId,
        siteId,occurrence,desiredOutcome,conditionIndex,constraints,
        freshObservedTargetCondition,negatedTargetCondition,
        engineArrayInputBindings,symbolicContext,formulaAuthority,
        targetPolicy,freshQueryRebuildProvenance}' \
        "${schedule_dir}/branch_queries.jsonl")
    if [[ "${root_formula}" != "${branch_formula}" ]]; then
        echo "[ERROR] Fresh scheduler changed the immutable campaign target formula" >&2
        return 1
    fi

    # Recheck the publication sources after the scheduler has consumed them.
    # A concurrent campaign generation cannot silently create a mixed handoff.
    if [[ "$(sha256_file "${source_pointer}")" \
                != "${original_pointer_sha}" \
            || "$(sha256_file "${source_generation_manifest}")" \
                != "${original_generation_sha}" \
            || "$(sha256_file "${source_completion_manifest}")" \
                != "${original_campaign_sha}" ]]; then
        echo "[ERROR] Campaign authority changed while publishing the fresh handoff" >&2
        return 1
    fi
    validate_campaign_generation "${source_pointer}"
    if [[ "${campaign_generation_manifest_sha256}" \
            != "${original_generation_sha}" ]]; then
        echo "[ERROR] Campaign generation changed during fresh scheduling" >&2
        return 1
    fi
    validate_campaign_generation "${pointer_snapshot}"

    artifacts_json=$({
        handoff_artifact_json STATE_POINTER_SNAPSHOT "${pointer_snapshot}"
        handoff_artifact_json GENERATION_MANIFEST \
            "${campaign_generation_manifest}"
        handoff_artifact_json CAMPAIGN_COMPLETE_MANIFEST \
            "${complete_snapshot}"
        handoff_artifact_json REGIONS "${campaign_regions}" \
            "$(jsonl_row_count "${campaign_regions}")"
        handoff_artifact_json ACTIVATIONS "${campaign_activations}" \
            "$(jsonl_row_count "${campaign_activations}")"
        handoff_artifact_json EDGES "${campaign_edges}" \
            "$(jsonl_row_count "${campaign_edges}")"
        handoff_artifact_json ROOTS "${campaign_roots}" \
            "$(jsonl_row_count "${campaign_roots}")"
        handoff_artifact_json SUMMARIES "${campaign_summaries}" \
            "$(jsonl_row_count "${campaign_summaries}")"
        handoff_artifact_json PATH_RECORDS "${campaign_path_records}" \
            "$(jsonl_row_count "${campaign_path_records}")"
        handoff_artifact_json STATIC_GRAPH "${campaign_static_graph}" \
            "$(jsonl_row_count "${campaign_static_graph}")"
        handoff_artifact_json FRESH_TARGET_ROOT "${exact_root}" 1
        handoff_artifact_json FRESH_TARGET_SUMMARY "${exact_summary}" 1
        handoff_artifact_json UPSTREAM_SUMMARIES "${upstream_summaries}" \
            "$(jsonl_row_count "${upstream_summaries}")"
        handoff_artifact_json CONCOLIC_SCHEDULE \
            "${schedule_dir}/concolic_schedule.jsonl" \
            "$(jsonl_row_count "${schedule_dir}/concolic_schedule.jsonl")"
        handoff_artifact_json SCHEDULED_ACTIVATION_PLAN \
            "${schedule_dir}/scheduled_activation_plan.jsonl" \
            "$(jsonl_row_count "${schedule_dir}/scheduled_activation_plan.jsonl")"
        handoff_artifact_json BRANCH_QUERIES \
            "${schedule_dir}/branch_queries.jsonl" 1
        handoff_artifact_json SYMBOLIC_MERGE_PLAN \
            "${schedule_dir}/symbolic_merge_plan.json"
        handoff_artifact_json SCHEDULER_SUMMARY \
            "${schedule_dir}/concolic_scheduler_summary.json"
        handoff_artifact_json SCHEDULE_PROVENANCE "${schedule_provenance}"
        handoff_artifact_json GRAPH_CHECKER_JAR "${gc_jar}"
    } | jq -s '.')
    manifest_tmp="${final_manifest}.tmp.$$"
    jq -n --arg generation "${campaign_generation}" \
        --arg activation "${activation_id}" --arg region "${region_id}" \
        --arg instance "${region_instance_id}" --arg summary "${summary_id}" \
        --arg sourcePointer "${source_pointer}" \
        --arg sourcePointerSha "${original_pointer_sha}" \
        --arg sourceCampaignManifest "$(realpath "${source_completion_manifest}")" \
        --arg sourceCampaignManifestSha "${original_campaign_sha}" \
        --arg scheduleDirectory "$(realpath "${schedule_dir}")" \
        --argjson artifacts "${artifacts_json}" '
        {schemaVersion:1,
         kind:"CONCOLIC_CAMPAIGN_FRESH_TARGET_HANDOFF",
         authority:"IMMUTABLE_COMPLETE_CAMPAIGN_FRESH_TARGET_SCHEDULE",
         complete:true, generation:$generation,
         identity:{activationId:$activation, regionId:$region,
                   regionInstanceId:$instance, summaryId:$summary},
         source:{campaignStatePointer:$sourcePointer,
                 campaignStatePointerSha256:$sourcePointerSha,
                 campaignCompleteManifest:$sourceCampaignManifest,
                 campaignCompleteManifestSha256:$sourceCampaignManifestSha},
         targetScheduleDirectory:$scheduleDirectory,
         compositionPolicy:
             "EXACT_FRESH_TARGET_SUMMARY_PLUS_DISTINCT_UPSTREAM_SUMMARIES",
         artifacts:$artifacts}' > "${manifest_tmp}"
    mv "${manifest_tmp}" "${final_manifest}"
    validate_campaign_handoff_manifest "${final_manifest}"
    chmod a-w "${pointer_snapshot}" "${complete_snapshot}" \
        "${exact_root}" "${exact_summary}" "${upstream_summaries}" \
        "${schedule_dir}"/* "${final_manifest}"
    rmdir "${publish_lock}"
    echo "[Concolic] immutable fresh campaign handoff: ${final_manifest}"
    echo "[Concolic] fresh handoff manifest: ${final_manifest}"
}

do_publish_campaign_handoff() {
    verify_hadoop_source
    local test_name="${1:-${causynth_workload_test}}"
    local campaign_dir="${2:-${CAUSYNTH_CAMPAIGN_OUTPUT_DIR:-}}"
    if [[ -z "${campaign_dir}" ]]; then
        echo "[ERROR] publish-campaign-handoff requires campaign-dir or CAUSYNTH_CAMPAIGN_OUTPUT_DIR" >&2
        return 1
    fi
    publish_campaign_handoff "${test_name}" "${campaign_dir}"
}

do_verify_campaign_handoff() {
    local manifest=${1:-}
    if [[ -z "${manifest}" ]]; then
        echo "[ERROR] verify-campaign-handoff requires one manifest" >&2
        return 1
    fi
    validate_campaign_handoff_manifest "${manifest}"
}

# Resolve one exact, already validated rebased fatal target.  Directory-name
# conventions and activation ordinals carry no authority: the branch query,
# scheduled activation row, and scheduler input provenance must all identify
# the same activation, region, and runtime instance.
resolve_target_context() {
    local test_name=$1 safe_name candidate identity_count matching_plan_count
    local expected_hash actual_hash
    local fresh_handoff_configured=false handoff_schedule
    local -a candidates=()
    safe_name=$(safe_test_name "${test_name}")
    target_trace_dir="${causynth_output_dir}/unit-test-graphs/${safe_name}"
    if [[ ! -d "${target_trace_dir}" ]]; then
        echo "[ERROR] Runtime trace directory is missing: ${target_trace_dir}" >&2
        return 1
    fi

    if [[ -n "${CAUSYNTH_CAMPAIGN_HANDOFF_MANIFEST:-}" ]]; then
        fresh_handoff_configured=true
        validate_campaign_handoff_manifest \
            "${CAUSYNTH_CAMPAIGN_HANDOFF_MANIFEST}"
        handoff_schedule="${handoff_target_schedule_dir}"
        if [[ -n "${CAUSYNTH_TARGET_SCHEDULE_DIR:-}" \
                && "$(realpath "${CAUSYNTH_TARGET_SCHEDULE_DIR}")" \
                    != "$(realpath "${handoff_schedule}")" ]]; then
            echo "[ERROR] Explicit target schedule conflicts with the fresh campaign handoff" >&2
            return 1
        fi
        candidates+=("$(realpath "${handoff_schedule}")")
    elif [[ -n "${CAUSYNTH_TARGET_SCHEDULE_DIR:-}" ]]; then
        if [[ ! -d "${CAUSYNTH_TARGET_SCHEDULE_DIR}" ]]; then
            echo "[ERROR] Requested target schedule is missing: ${CAUSYNTH_TARGET_SCHEDULE_DIR}" >&2
            return 1
        fi
        candidates+=("$(realpath "${CAUSYNTH_TARGET_SCHEDULE_DIR}")")
    else
        while IFS= read -r candidate; do
            candidate=$(dirname "${candidate}")
            [[ -s "${candidate}/scheduled_activation_plan.jsonl" ]] || continue
            [[ -s "${candidate}/symbolic_merge_plan.json" ]] || continue
            [[ -s "${candidate}/schedule_input_provenance.json" ]] || continue
            candidates+=("$(realpath "${candidate}")")
        done < <(find "${target_trace_dir}" -mindepth 2 -maxdepth 2 \
            -type f -name branch_queries.jsonl -size +0c | sort)
    fi
    if [[ "${#candidates[@]}" -ne 1 ]]; then
        echo "[ERROR] Expected exactly one rebased target schedule, found ${#candidates[@]} under ${target_trace_dir}" >&2
        echo "[ERROR] Set CAUSYNTH_TARGET_SCHEDULE_DIR to the exact validated schedule." >&2
        return 1
    fi

    target_schedule_dir="${candidates[0]}"
    target_branch_queries="${target_schedule_dir}/branch_queries.jsonl"
    target_activation_plan="${target_schedule_dir}/scheduled_activation_plan.jsonl"
    target_merge_plan="${target_schedule_dir}/symbolic_merge_plan.json"
    target_schedule_provenance="${target_schedule_dir}/schedule_input_provenance.json"
    require_nonempty_input "fatal branch query" "${target_branch_queries}"
    require_nonempty_input "target activation plan" "${target_activation_plan}"
    require_nonempty_input "target symbolic merge plan" "${target_merge_plan}"
    require_nonempty_input "target schedule provenance" "${target_schedule_provenance}"

    # A multi-row file is deliberately rejected even when rows share an
    # activation: the composer otherwise selects its first solver-ready row.
    if ! jq -e -s '
            length == 1
            and .[0].readyForSolver == true
            and .[0].replayAlreadyValidated == true
            and .[0].targetReplayValidated == true
            and ((.[0].activationId // "") | length) > 0
            and ((.[0].regionId // "") | length) > 0
            and ((.[0].regionInstanceId // "") | length) > 0' \
            "${target_branch_queries}" >/dev/null; then
        echo "[ERROR] Target schedule must contain exactly one solver-ready, replay-validated fatal query" >&2
        return 1
    fi
    target_activation_id=$(jq -r -s '.[0].activationId' \
        "${target_branch_queries}")
    target_region_id=$(jq -r -s '.[0].regionId' \
        "${target_branch_queries}")
    target_region_instance_id=$(jq -r -s '.[0].regionInstanceId' \
        "${target_branch_queries}")

    matching_plan_count=$(jq -r -s \
        --arg activation "${target_activation_id}" \
        --arg region "${target_region_id}" \
        --arg instance "${target_region_instance_id}" '
        [.[] | select(.activationId == $activation
            and .regionId == $region
            and .regionInstanceId == $instance)] | length' \
        "${target_activation_plan}")
    identity_count=$(jq -r -s --arg activation "${target_activation_id}" '
        [.[] | select(.activationId == $activation)] | length' \
        "${target_activation_plan}")
    if [[ "${matching_plan_count}" -ne 1 || "${identity_count}" -ne 1 ]]; then
        echo "[ERROR] Target activation plan does not contain one exact query identity: ${target_activation_id} ${target_region_instance_id}" >&2
        return 1
    fi
    if ! jq -e \
            --arg activation "${target_activation_id}" \
            --arg region "${target_region_id}" \
            --arg instance "${target_region_instance_id}" '
            .complete == true
            and .activationId == $activation
            and .regionId == $region
            and .regionInstanceId == $instance' \
            "${target_schedule_provenance}" >/dev/null; then
        echo "[ERROR] Scheduler provenance does not match the exact fatal query identity" >&2
        return 1
    fi
    source_activations=$(jq -r '.activationPlan // ""' \
        "${target_schedule_provenance}")
    source_edges=$(jq -r '.edgeValidations // ""' \
        "${target_schedule_provenance}")
    require_nonempty_input "scheduler source activations" \
        "${source_activations}"
    require_nonempty_input "scheduler source edge validations" \
        "${source_edges}"
    expected_hash=$(jq -r '.activationPlanSha256 // ""' \
        "${target_schedule_provenance}")
    actual_hash=$(shasum -a 256 "${source_activations}" | awk '{print $1}')
    if [[ -z "${expected_hash}" || "${actual_hash}" != "${expected_hash}" ]]; then
        echo "[ERROR] Scheduler source activation catalog no longer matches its provenance" >&2
        return 1
    fi
    expected_hash=$(jq -r '.edgeValidationsSha256 // ""' \
        "${target_schedule_provenance}")
    actual_hash=$(shasum -a 256 "${source_edges}" | awk '{print $1}')
    if [[ -z "${expected_hash}" || "${actual_hash}" != "${expected_hash}" ]]; then
        echo "[ERROR] Scheduler source edge catalog no longer matches its provenance" >&2
        return 1
    fi
    require_nonempty_input "GraphChecker jar" "${gc_jar}"
    expected_hash=$(jq -r '.graphCheckerJarSha256 // ""' \
        "${target_schedule_provenance}")
    actual_hash=$(shasum -a 256 "${gc_jar}" | awk '{print $1}')
    if [[ -z "${expected_hash}" || "${actual_hash}" != "${expected_hash}" ]]; then
        echo "[ERROR] Current GraphChecker jar differs from the jar that produced the target schedule" >&2
        return 1
    fi

    if [[ "$(jq -r '.schemaVersion // 0' \
            "${target_schedule_provenance}")" -ge 2 ]]; then
        validate_schedule_provenance "${target_schedule_provenance}" \
            "${fresh_handoff_configured}"
        if [[ "${schedule_provenance_activation_id}" \
                    != "${target_activation_id}" \
                || "${schedule_provenance_region_id}" \
                    != "${target_region_id}" \
                || "${schedule_provenance_region_instance_id}" \
                    != "${target_region_instance_id}" ]]; then
            echo "[ERROR] Schema-2 schedule provenance identity differs from the fatal query" >&2
            return 1
        fi
    elif [[ "${fresh_handoff_configured}" == "true" ]]; then
        echo "[ERROR] Fresh campaign handoff cannot use legacy schedule provenance" >&2
        return 1
    fi

    if [[ "${fresh_handoff_configured}" == "true" ]]; then
        if [[ "$(realpath "${target_branch_queries}")" \
                    != "$(realpath "$(handoff_artifact_path \
                        "${handoff_manifest}" BRANCH_QUERIES)")" \
                || "$(realpath "${target_activation_plan}")" \
                    != "$(realpath "$(handoff_artifact_path \
                        "${handoff_manifest}" SCHEDULED_ACTIVATION_PLAN)")" \
                || "$(realpath "${target_merge_plan}")" \
                    != "$(realpath "$(handoff_artifact_path \
                        "${handoff_manifest}" SYMBOLIC_MERGE_PLAN)")" \
                || "$(realpath "${source_activations}")" \
                    != "$(realpath "${handoff_activations}")" \
                || "$(realpath "${source_edges}")" \
                    != "$(realpath "${handoff_edges}")" \
                || "${target_activation_id}" != "${handoff_activation_id}" \
                || "${target_region_id}" != "${handoff_region_id}" \
                || "${target_region_instance_id}" \
                    != "${handoff_region_instance_id}" ]]; then
            echo "[ERROR] Resolved target inputs are not the exact hashed fresh handoff artifacts" >&2
            return 1
        fi
    fi

    if [[ "${fresh_handoff_configured}" == "true" \
            && -n "${CAUSYNTH_REBASE_CAMPAIGN_MANIFEST:-}" \
            && "$(realpath "${CAUSYNTH_REBASE_CAMPAIGN_MANIFEST}")" \
                != "$(realpath "${handoff_complete_manifest}")" ]]; then
        echo "[ERROR] Rebase manifest conflicts with the handoff's immutable campaign snapshot" >&2
        return 1
    fi
    if [[ -n "${CAUSYNTH_REBASE_CAMPAIGN_MANIFEST:-}" ]]; then
        require_nonempty_input "rebase campaign manifest" \
            "${CAUSYNTH_REBASE_CAMPAIGN_MANIFEST}"
        if ! jq -e \
                --arg activation "${target_activation_id}" \
                --arg region "${target_region_id}" \
                --arg instance "${target_region_instance_id}" '
                .postDiscoveryTargetRebaseCompleted == true
                and .postDiscoveryTargetRebaseRequired == false
                and .postDiscoveryTargetRebaseReady == true
                and .postDiscoveryTargetRebaseActivationId == $activation
                and .postDiscoveryTargetRebaseRegionInstanceId == $instance
                and .postDiscoveryTargetRebase.activationId == $activation
                and .postDiscoveryTargetRebase.regionId == $region
                and .postDiscoveryTargetRebase.regionInstanceId == $instance
                and .postDiscoveryTargetRebase.authority
                    == "FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_TARGET_REPLAY"' \
                "${CAUSYNTH_REBASE_CAMPAIGN_MANIFEST}" >/dev/null; then
            echo "[ERROR] Campaign rebase manifest does not authorize the exact scheduled fatal target" >&2
            return 1
        fi
    fi
    echo "[Concolic] exact target: ${target_activation_id} ${target_region_instance_id}"
}

# Validate the immutable source-artifact ledger emitted by the automatic
# producer planner.  The Java projector independently repeats the semantic
# witness checks; this shell-side pass prevents a stale or edited artifact
# from even reaching that verifier.
validate_schema2_producer_catalog() {
    local catalog=$1 artifact_path artifact_sha actual_sha role
    require_nonempty_input "schema-2 producer-groups catalog" "${catalog}"
    catalog=$(realpath "${catalog}")
    if ! jq -e '
            .schemaVersion == 2
            and .kind == "CONCOLIC_PRODUCER_GROUP_CATALOG"
            and .complete == true
            and .roleSelectionIsDerived == true
            and (.sourceArtifacts | type == "array" and length == 7)
            and ([.sourceArtifacts[].role] | sort)
                == (["COMPOSITION_MANIFEST", "COMPOSED_SMT",
                     "ORIGINAL_SUMMARIES", "PRODUCER_ACTIVATIONS",
                     "TARGET_ACTIVATIONS", "FATAL_QUERIES",
                     "RUNTIME_EDGE_VALIDATION"] | sort)
            and (.enrichedSummaries.role == "ENRICHED_SUMMARIES")
            and (.witnessSidecar.role == "PRODUCER_WITNESSES")
            and (.producerGroups | type == "array" and length >= 2)
            and .producerGroupCount == (.producerGroups | length)
            and ([.producerGroups[].producerGroupId] | unique | length)
                == (.producerGroups | length)
            and ([.producerGroups[].upstreamRegion] | unique | length)
                == (.producerGroups | length)
            and ([.producerGroups[]
                | select(.projectionRole == "TARGET_MAP_STATE")]
                | length) == 1
            and ([.producerGroups[]
                | select(.projectionRole == "LOOKUP_KEY_PRODUCER")]
                | length) >= 1
            and all(.producerGroups[];
                .projectionRoleDerived == true
                and ((.expectedBroadcastCandidates | type) == "number")
                and .expectedBroadcastCandidates >= 1
                and (.witnessIds | type == "array" and length >= 1)
                and .witnessCount == (.witnessIds | length)
                and ((.upstreamActivations // "") | length) > 0
                and ((.broadcastActivations // "") | length) > 0)' \
            "${catalog}" >/dev/null; then
        echo "[ERROR] Producer-groups catalog is not a complete derived schema-2 catalog" >&2
        return 1
    fi

    while IFS=$'\t' read -r role artifact_path artifact_sha; do
        if [[ "${artifact_path}" != /* || -z "${artifact_sha}" ]]; then
            echo "[ERROR] Producer catalog artifact is not absolute and hashed: ${role}" >&2
            return 1
        fi
        require_nonempty_input "producer catalog artifact ${role}" \
            "${artifact_path}"
        actual_sha=$(shasum -a 256 "${artifact_path}" | awk '{print $1}')
        if [[ "${actual_sha}" != "${artifact_sha}" ]]; then
            echo "[ERROR] Producer catalog artifact hash mismatch: ${role}" >&2
            echo "[ERROR] Expected: ${artifact_sha}" >&2
            echo "[ERROR] Actual:   ${actual_sha}" >&2
            return 1
        fi
    done < <(jq -r '
        (.sourceArtifacts
         + [.witnessSidecar, .enrichedSummaries])[]
        | [.role, .path, .sha256] | @tsv' "${catalog}")

    producer_enriched_summaries=$(jq -r '.enrichedSummaries.path' \
        "${catalog}")
    producer_runtime_edges=$(jq -r '
        [.sourceArtifacts[]
         | select(.role == "RUNTIME_EDGE_VALIDATION")][0].path' \
        "${catalog}")
    producer_original_summaries=$(jq -r '
        [.sourceArtifacts[]
         | select(.role == "ORIGINAL_SUMMARIES")][0].path' \
        "${catalog}")
    producer_activations=$(jq -r '
        [.sourceArtifacts[]
         | select(.role == "PRODUCER_ACTIVATIONS")][0].path' \
        "${catalog}")

    local expected_role expected_path recorded_path
    for expected_role in COMPOSITION_MANIFEST COMPOSED_SMT \
            PRODUCER_ACTIVATIONS TARGET_ACTIVATIONS FATAL_QUERIES \
            RUNTIME_EDGE_VALIDATION; do
        case "${expected_role}" in
            COMPOSITION_MANIFEST) expected_path="${composition_manifest}" ;;
            COMPOSED_SMT) expected_path="${composed_smt}" ;;
            PRODUCER_ACTIVATIONS) expected_path="${source_activations}" ;;
            TARGET_ACTIVATIONS) expected_path="${target_activation_plan}" ;;
            FATAL_QUERIES) expected_path="${target_branch_queries}" ;;
            RUNTIME_EDGE_VALIDATION) expected_path="${source_edges}" ;;
        esac
        recorded_path=$(jq -r --arg role "${expected_role}" '
            [.sourceArtifacts[] | select(.role == $role)][0].path' \
            "${catalog}")
        if [[ "$(realpath "${recorded_path}")" \
                != "$(realpath "${expected_path}")" ]]; then
            echo "[ERROR] Producer catalog ${expected_role} does not match the exact target composition" >&2
            return 1
        fi
    done
    if [[ -n "${CAUSYNTH_PRODUCER_RUNTIME_EDGES:-}" \
            && "$(realpath "${CAUSYNTH_PRODUCER_RUNTIME_EDGES}")" \
                != "$(realpath "${producer_runtime_edges}")" ]]; then
        echo "[ERROR] Explicit producer runtime edges differ from the catalog's hashed source" >&2
        return 1
    fi
    if [[ -n "${CAUSYNTH_PROJECTION_SUMMARIES:-}" \
            && "$(realpath "${CAUSYNTH_PROJECTION_SUMMARIES}")" \
                != "$(realpath "${producer_enriched_summaries}")" ]]; then
        echo "[ERROR] Multi-producer projection cannot replace the catalog's enriched summaries" >&2
        return 1
    fi
    producer_groups_catalog="${catalog}"
}

# Multi-producer mode consumes only the automatically derived schema-2
# catalog.  The explicit single-group form remains available for old focused
# experiments, but it cannot masquerade as multi-producer evidence.
resolve_producer_configuration() {
    local require_projection_inputs=${1:-false}
    local nested expected
    producer_group_regions=()
    producer_groups_catalog="${producer_groups_catalog:-${CAUSYNTH_PRODUCER_GROUPS_CATALOG:-}}"
    if [[ -n "${producer_groups_catalog}" ]]; then
        validate_schema2_producer_catalog "${producer_groups_catalog}"
        while IFS= read -r nested; do
            require_nonempty_input "producer-groups activation catalog" \
                "${nested}"
            if [[ "$(realpath "${nested}")" \
                    != "$(realpath "${producer_activations}")" ]]; then
                echo "[ERROR] Producer-group activation path is not the catalog's hashed activation source" >&2
                return 1
            fi
        done < <(jq -r '.producerGroups[]
            | .upstreamActivations, .broadcastActivations' \
            "${producer_groups_catalog}" | sort -u)
        while IFS= read -r nested; do
            producer_group_regions+=("${nested}")
        done < <(jq -r '.producerGroups[].upstreamRegion' \
            "${producer_groups_catalog}")
        producer_mode="MULTI_GROUP"
        return 0
    fi

    producer_mode="SINGLE_GROUP"
    single_upstream_region="${CAUSYNTH_UPSTREAM_REGION:-}"
    if [[ -z "${single_upstream_region}" ]]; then
        echo "[ERROR] Single-producer mode requires CAUSYNTH_UPSTREAM_REGION" >&2
        return 1
    fi
    producer_group_regions+=("${single_upstream_region}")
    if [[ "${require_projection_inputs}" != "true" ]]; then
        return 0
    fi
    single_upstream_activations="${CAUSYNTH_UPSTREAM_ACTIVATIONS:-}"
    single_broadcast_activations="${CAUSYNTH_BROADCAST_ACTIVATIONS:-${target_trace_dir}/concolic_activation_plan.jsonl}"
    expected="${CAUSYNTH_EXPECTED_BROADCAST_CANDIDATES:-}"
    require_nonempty_input "single-group upstream activations" \
        "${single_upstream_activations}"
    require_nonempty_input "single-group broadcast activations" \
        "${single_broadcast_activations}"
    if [[ ! "${expected}" =~ ^[1-9][0-9]*$ ]]; then
        echo "[ERROR] Single-producer mode requires positive CAUSYNTH_EXPECTED_BROADCAST_CANDIDATES" >&2
        return 1
    fi
    single_expected_broadcast_candidates="${expected}"
}

resolve_composition_paths() {
    composition_dir=$(realpath -m \
        "${CAUSYNTH_COMPOSITION_OUTPUT_DIR:-${target_schedule_dir}/bounded-composition}")
    if [[ "${composition_dir}" == "${target_schedule_dir}" ]]; then
        echo "[ERROR] Composition output must not be the target schedule directory" >&2
        return 1
    fi
    composed_smt="${composition_dir}/composed_fatal.smt2"
    composition_manifest="${composition_dir}/composed_fatal_manifest.json"
    relationship_candidates="${composition_dir}/symbolic_relationship_candidates.json"
    relationship_proofs="${composition_dir}/symbolic_relationship_proofs.json"
}

resolve_producer_group_paths() {
    producer_group_dir=$(realpath -m \
        "${CAUSYNTH_PRODUCER_GROUP_OUTPUT_DIR:-${composition_dir}/producer-groups}")
    require_workspace_output_path "producer-group output directory" \
        "${producer_group_dir}"
    if [[ "${producer_group_dir}" == "${composition_dir}" \
            || "${producer_group_dir}" == "${target_schedule_dir}" ]]; then
        echo "[ERROR] Producer-group outputs must own a distinct directory" >&2
        return 1
    fi
    derived_producer_catalog="${producer_group_dir}/producer_groups.json"
    producer_witnesses="${producer_group_dir}/producer_group_witnesses.json"
    producer_enriched_output="${producer_group_dir}/enriched_summaries.jsonl"
}

derive_producer_groups_resolved() {
    local planner_summaries planner_activations planner_edges z3_binary
    require_nonempty_input "complete composition manifest" \
        "${composition_manifest}"
    require_nonempty_input "composed SMT" "${composed_smt}"
    if ! jq -e '
            .complete == true
            and .boundedComposition == true
            and .fatalReplayValidated == true
            and .caseProjectionCatalogComplete == true
            and (.boundedUpstreamRegions | type == "array"
                 and length >= 1)' "${composition_manifest}" >/dev/null; then
        echo "[ERROR] Automatic producer derivation requires a complete bounded composition" >&2
        return 1
    fi
    planner_summaries="${CAUSYNTH_PRODUCER_SUMMARIES:-${CAUSYNTH_COMPOSITION_SUMMARIES:-${handoff_composition_summaries:-}}}"
    if [[ -n "${CAUSYNTH_CAMPAIGN_HANDOFF_MANIFEST:-}" \
            && "$(realpath "${planner_summaries}")" \
                != "$(realpath "${handoff_composition_summaries}")" ]]; then
        echo "[ERROR] Fresh handoff producer planner cannot replace its hashed upstream summaries" >&2
        return 1
    fi
    if [[ -n "${CAUSYNTH_PRODUCER_ACTIVATIONS:-}" \
            && "$(realpath "${CAUSYNTH_PRODUCER_ACTIVATIONS}")" \
                != "$(realpath "${source_activations}")" ]]; then
        echo "[ERROR] Producer activations must match the target schedule's hashed source" >&2
        return 1
    fi
    if [[ -n "${CAUSYNTH_PRODUCER_RUNTIME_EDGES:-}" \
            && "$(realpath "${CAUSYNTH_PRODUCER_RUNTIME_EDGES}")" \
                != "$(realpath "${source_edges}")" ]]; then
        echo "[ERROR] Producer runtime edges must match the target schedule's hashed source" >&2
        return 1
    fi
    planner_activations="${source_activations}"
    planner_edges="${source_edges}"
    require_nonempty_input "original merged producer summaries" \
        "${planner_summaries}"
    require_nonempty_input "exact producer activation catalog" \
        "${planner_activations}"
    require_nonempty_input "exact producer runtime edge catalog" \
        "${planner_edges}"
    require_nonempty_input "exact target activation plan" \
        "${target_activation_plan}"
    require_nonempty_input "exact fatal query" "${target_branch_queries}"
    require_nonempty_input "GraphChecker jar" "${gc_jar}"
    z3_binary=$(configured_tool_path "${z3_bin}" || true)
    if [[ -z "${z3_binary}" || ! -x "${z3_binary}" ]]; then
        echo "[ERROR] z3 executable is unavailable" >&2
        return 1
    fi

    resolve_producer_group_paths
    prepare_fresh_output_directory "producer-group output directory" \
        "${producer_group_dir}"
    require_absent_output "producer-group catalog" \
        "${derived_producer_catalog}"
    require_absent_output "producer witness sidecar" \
        "${producer_witnesses}"
    require_absent_output "enriched producer summaries" \
        "${producer_enriched_output}"
    "${graphchecker_java_bin}" -cp "${gc_jar}" \
        edu.uva.liftlab.graphchecker.concolic.ConcolicProducerGroupPlanner \
        --composition-manifest "${composition_manifest}" \
        --smt "${composed_smt}" \
        --summaries "${planner_summaries}" \
        --activations "${planner_activations}" \
        --target-activations "${target_activation_plan}" \
        --fatal-query "${target_branch_queries}" \
        --runtime-edges "${planner_edges}" \
        --z3 "${z3_binary}" \
        --target-activation-id "${target_activation_id}" \
        --output-catalog "${derived_producer_catalog}" \
        --output-witnesses "${producer_witnesses}" \
        --output-summaries "${producer_enriched_output}" \
        --timeout-ms "${CAUSYNTH_PRODUCER_PLANNER_TIMEOUT_MS:-30000}"
    producer_groups_catalog="${derived_producer_catalog}"
    validate_schema2_producer_catalog "${producer_groups_catalog}"
    echo "[Concolic] derived schema-2 producer catalog: ${producer_groups_catalog}"
    echo "[Concolic] enriched producer summaries: ${producer_enriched_summaries}"
}

ensure_schema2_producer_catalog() {
    resolve_producer_group_paths
    if [[ -n "${CAUSYNTH_PRODUCER_GROUPS_CATALOG:-}" ]]; then
        producer_groups_catalog=$(realpath \
            "${CAUSYNTH_PRODUCER_GROUPS_CATALOG}")
    elif [[ -s "${derived_producer_catalog}" ]]; then
        producer_groups_catalog=$(realpath "${derived_producer_catalog}")
    else
        derive_producer_groups_resolved
        return
    fi
    validate_schema2_producer_catalog "${producer_groups_catalog}"
}

do_derive_producer_groups() {
    verify_hadoop_source
    local test_name="${1:-${causynth_workload_test}}"
    resolve_target_context "${test_name}"
    resolve_composition_paths
    derive_producer_groups_resolved
}

resolve_natural_replay_paths() {
    natural_dir=$(realpath -m \
        "${CAUSYNTH_NATURAL_REPLAY_OUTPUT_DIR:-${target_schedule_dir}/natural-propagation-bounded-producer-groups}")
    require_workspace_output_path "natural replay output directory" \
        "${natural_dir}"
    if [[ "${natural_dir}" == "${target_schedule_dir}" \
            || "${natural_dir}" == "${composition_dir}" ]]; then
        echo "[ERROR] Natural replay output must own a distinct fresh directory" >&2
        return 1
    fi
    natural_plan="${natural_dir}/activation_plan.jsonl"
    projection_manifest="${natural_dir}/model_projection_manifest.json"
    natural_results="${natural_dir}/concolic_region_results.jsonl"
    natural_validation="${natural_dir}/natural_replay_validation.json"
}

# A schema-2 producer catalog is derived from the final composition, so it
# cannot be used to bootstrap that same composition.  When no explicit bound
# is supplied, first run the composer in its complete instance-scoped mode and
# take only its runtime-selected relevant region set (minus the fatal region)
# into a separate final bounded run.
discover_composition_scope() {
    local target_summary=$1 upstream_summaries=$2 regions_file=$3
    local discovery_dir discovery_smt discovery_manifest
    local discovery_relationships region
    discovery_dir=$(realpath -m \
        "${CAUSYNTH_COMPOSITION_SCOPE_OUTPUT_DIR:-${target_schedule_dir}/scope-discovery-$(basename "${composition_dir}")}")
    require_workspace_output_path "composition scope-discovery output" \
        "${discovery_dir}"
    if [[ "${discovery_dir}" == "${composition_dir}" \
            || "${discovery_dir}" == "${target_schedule_dir}" ]]; then
        echo "[ERROR] Scope discovery must use a distinct fresh directory" >&2
        return 1
    fi
    discovery_smt="${discovery_dir}/full_context.smt2"
    discovery_manifest="${discovery_dir}/full_context_manifest.json"
    discovery_relationships="${discovery_dir}/relationship_candidates.json"
    prepare_fresh_output_directory "composition scope-discovery output" \
        "${discovery_dir}"
    "${graphchecker_java_bin}" -cp "${gc_jar}" \
        edu.uva.liftlab.graphchecker.concolic.ConcolicSmtComposer \
        --fatal-query "${target_branch_queries}" \
        --summaries "${target_summary}" \
        --summaries "${upstream_summaries}" \
        --regions "${regions_file}" \
        --merge-plan "${target_merge_plan}" \
        --output "${discovery_smt}" \
        --manifest "${discovery_manifest}" \
        --relationships "${discovery_relationships}" \
        --fatal-region "${target_region_id}" \
        --activation-id "${target_activation_id}"
    require_nonempty_input "full-context discovery SMT" "${discovery_smt}"
    require_nonempty_input "full-context discovery manifest" \
        "${discovery_manifest}"
    if ! jq -e \
            --arg activation "${target_activation_id}" \
            --arg fatal "${target_region_id}" '
            .complete == true
            and .boundedComposition == false
            and .compositionScope == "FULL_INSTANCE_SCOPED_CONTEXT"
            and .instanceScopedSymbolicContext == true
            and .symbolicContextAuthority
                == "SCHEDULER_SELECTED_RUNTIME_BINDINGS_FOR_FATAL_INSTANCE"
            and .fatalReplayValidated == true
            and .caseProjectionCatalogComplete == true
            and .soundnessScope
                == "SELECTED_REGION_PATHS_AND_RUNTIME_VALIDATED_BINDINGS"
            and .fatalRegion == $fatal
            and .fatalActivation == $activation
            and (.relevantRegions | type == "array" and length >= 2)
            and (.relevantRegions | length)
                == (.relevantRegions | unique | length)
            and (.relevantRegions | index($fatal)) != null
            and ([.relevantRegions[] | select(. != $fatal)] | length) >= 1' \
            "${discovery_manifest}" >/dev/null; then
        echo "[ERROR] Composer did not produce a complete runtime-selected full-context scope" >&2
        return 1
    fi
    producer_group_regions=()
    while IFS= read -r region; do
        producer_group_regions+=("${region}")
    done < <(jq -r --arg fatal "${target_region_id}" \
        '.relevantRegions | map(select(. != $fatal)) | sort | .[]' \
        "${discovery_manifest}")
    if [[ "${#producer_group_regions[@]}" -lt 1 ]]; then
        echo "[ERROR] Full-context discovery found no upstream region" >&2
        return 1
    fi
    echo "[Concolic] scope discovery: ${discovery_manifest}"
    echo "[Concolic] runtime-selected bounded regions: ${producer_group_regions[*]}"
}

do_compose_smt() {
    verify_hadoop_source
    local test_name="${1:-${causynth_workload_test}}"
    local target_summary upstream_summaries region proof_status=0
    local bounded_regions_json
    local regions_file
    local -a bounded_args=()
    resolve_target_context "${test_name}"
    resolve_composition_paths

    target_summary="${CAUSYNTH_TARGET_SUMMARIES:-${handoff_target_summary:-${target_schedule_dir}/concolic_region_summaries.jsonl}}"
    upstream_summaries="${CAUSYNTH_COMPOSITION_SUMMARIES:-${handoff_composition_summaries:-}}"
    regions_file="${handoff_regions:-${causynth_output_dir}/symbolic_regions.jsonl}"
    if [[ -n "${CAUSYNTH_CAMPAIGN_HANDOFF_MANIFEST:-}" ]]; then
        if [[ "$(realpath "${target_summary}")" \
                    != "$(realpath "${handoff_target_summary}")" \
                || "$(realpath "${upstream_summaries}")" \
                    != "$(realpath "${handoff_composition_summaries}")" \
                || "$(realpath "${regions_file}")" \
                    != "$(realpath "${handoff_regions}")" ]]; then
            echo "[ERROR] Fresh handoff composition inputs cannot be replaced by stale summaries or regions" >&2
            return 1
        fi
    fi
    require_nonempty_input "validated target summaries" "${target_summary}"
    require_nonempty_input "merged composition summaries" "${upstream_summaries}"
    require_nonempty_input "symbolic region catalog" "${regions_file}"
    require_nonempty_input "GraphChecker jar" "${gc_jar}"
    if [[ "$(realpath "${target_summary}")" == "$(realpath "${upstream_summaries}")" ]]; then
        echo "[ERROR] Target and upstream composition summaries must be distinct inputs" >&2
        return 1
    fi
    producer_group_regions=()
    if [[ -n "${CAUSYNTH_BOUNDED_UPSTREAM_REGIONS:-}" ]]; then
        while IFS= read -r region; do
            [[ -n "${region}" ]] && producer_group_regions+=("${region}")
        done < <(printf '%s\n' "${CAUSYNTH_BOUNDED_UPSTREAM_REGIONS}" \
            | tr ',[:space:]' '\n' | sed '/^$/d' | sort -u)
    elif [[ -n "${CAUSYNTH_UPSTREAM_REGION:-}" ]]; then
        producer_group_regions+=("${CAUSYNTH_UPSTREAM_REGION}")
    else
        discover_composition_scope "${target_summary}" \
            "${upstream_summaries}" "${regions_file}"
    fi
    if [[ "${#producer_group_regions[@]}" -lt 1 ]]; then
        echo "[ERROR] Bounded composition has no upstream region" >&2
        return 1
    fi
    for region in "${producer_group_regions[@]}"; do
        bounded_args+=(--bounded-upstream-region "${region}")
    done
    bounded_regions_json=$(printf '%s\n' "${producer_group_regions[@]}" \
        | jq -R . | jq -s .)
    prepare_fresh_output_directory "composition output directory" \
        "${composition_dir}"

    "${graphchecker_java_bin}" -cp "${gc_jar}" \
        edu.uva.liftlab.graphchecker.concolic.ConcolicSmtComposer \
        --fatal-query "${target_branch_queries}" \
        --summaries "${target_summary}" \
        --summaries "${upstream_summaries}" \
        --regions "${regions_file}" \
        --merge-plan "${target_merge_plan}" \
        --output "${composed_smt}" \
        --manifest "${composition_manifest}" \
        --relationships "${relationship_candidates}" \
        --fatal-region "${target_region_id}" \
        --activation-id "${target_activation_id}" \
        "${bounded_args[@]}"
    require_nonempty_input "composed SMT" "${composed_smt}"
    require_nonempty_input "composition manifest" "${composition_manifest}"
    require_nonempty_input "relationship candidates" \
        "${relationship_candidates}"
    if ! jq -e \
            --arg activation "${target_activation_id}" \
            --arg region "${target_region_id}" \
            --argjson bounded "${bounded_regions_json}" '
            .complete == true
            and .boundedComposition == true
            and .fatalReplayValidated == true
            and .fatalRegion == $region
            and .fatalActivation == $activation
            and ((.boundedUpstreamRegions | sort) == ($bounded | sort))' \
            "${composition_manifest}" >/dev/null; then
        echo "[ERROR] Composer did not produce one complete SMT bounded to the exact producer regions and fatal target" >&2
        return 1
    fi
    "${graphchecker_java_bin}" -cp "${gc_jar}" \
        edu.uva.liftlab.graphchecker.concolic.SymbolicRelationshipVerifier \
        --smt "${composed_smt}" \
        --candidates "${relationship_candidates}" \
        --output "${relationship_proofs}" \
        --z3 "$(configured_tool_path "${z3_bin}")" \
        --timeout-ms "${CAUSYNTH_RELATIONSHIP_TIMEOUT_MS:-20000}" \
        || proof_status=$?
    echo "[Concolic] composed SMT: ${composed_smt}"
    echo "[Concolic] manifest: ${composition_manifest}"
    echo "[Concolic] relationship proofs: ${relationship_proofs}"
    return "${proof_status}"
}

do_verify_relationships() {
    verify_hadoop_source
    local test_name="${1:-${causynth_workload_test}}"
    local proof_output proof_status=0
    resolve_target_context "${test_name}"
    resolve_composition_paths
    require_nonempty_input "composed SMT" "${composed_smt}"
    require_nonempty_input "relationship candidates" \
        "${relationship_candidates}"
    require_nonempty_input "GraphChecker jar" "${gc_jar}"
    proof_output="${CAUSYNTH_RELATIONSHIP_PROOFS_OUTPUT:-${composition_dir}/symbolic_relationship_proofs.recheck.json}"
    require_absent_output "relationship proof output" "${proof_output}"
    "${graphchecker_java_bin}" -cp "${gc_jar}" \
        edu.uva.liftlab.graphchecker.concolic.SymbolicRelationshipVerifier \
        --smt "${composed_smt}" \
        --candidates "${relationship_candidates}" \
        --output "${proof_output}" \
        --z3 "$(configured_tool_path "${z3_bin}")" \
        --timeout-ms "${CAUSYNTH_RELATIONSHIP_TIMEOUT_MS:-20000}" \
        || proof_status=$?
    echo "[Concolic] relationship proofs: ${proof_output}"
    return "${proof_status}"
}

do_project_composed_model() {
    verify_hadoop_source
    local test_name="${1:-${causynth_workload_test}}"
    local projection_summaries static_graph z3_binary
    local -a producer_args=()
    resolve_target_context "${test_name}"
    resolve_composition_paths
    resolve_natural_replay_paths

    producer_groups_catalog=""
    resolve_producer_group_paths
    if [[ -n "${CAUSYNTH_PRODUCER_GROUPS_CATALOG:-}" \
            || -s "${derived_producer_catalog}" \
            || -z "${CAUSYNTH_UPSTREAM_REGION:-}" ]]; then
        ensure_schema2_producer_catalog
    fi
    resolve_producer_configuration true

    if [[ "${producer_mode}" == "MULTI_GROUP" ]]; then
        projection_summaries="${producer_enriched_summaries}"
    else
        projection_summaries="${CAUSYNTH_PROJECTION_SUMMARIES:-}"
    fi
    static_graph="${handoff_static_graph:-${causynth_output_dir}/static_dataflow_edges.jsonl}"
    if [[ -n "${CAUSYNTH_CAMPAIGN_HANDOFF_MANIFEST:-}" \
            && "$(realpath "${static_graph}")" \
                != "$(realpath "${handoff_static_graph}")" ]]; then
        echo "[ERROR] Fresh handoff projection cannot replace its hashed static graph" >&2
        return 1
    fi
    require_nonempty_input "composed SMT" "${composed_smt}"
    require_nonempty_input "composition manifest" "${composition_manifest}"
    require_nonempty_input "projection summaries" "${projection_summaries}"
    require_nonempty_input "static dataflow graph" "${static_graph}"
    require_nonempty_input "GraphChecker jar" "${gc_jar}"
    z3_binary=$(configured_tool_path "${z3_bin}" || true)
    if [[ -z "${z3_binary}" || ! -x "${z3_binary}" ]]; then
        echo "[ERROR] z3 executable is unavailable" >&2
        return 1
    fi
    if [[ "${producer_mode}" == "MULTI_GROUP" ]]; then
        producer_args+=(
            --producer-groups "${producer_groups_catalog}"
            --runtime-edges "${producer_runtime_edges}"
        )
    else
        producer_args+=(
            --upstream-activations "${single_upstream_activations}"
            --broadcast-activations "${single_broadcast_activations}"
            --expected-broadcast-candidates \
                "${single_expected_broadcast_candidates}"
            --upstream-region "${single_upstream_region}"
        )
    fi
    prepare_fresh_output_directory "natural replay output directory" \
        "${natural_dir}"

    "${graphchecker_java_bin}" -cp "${gc_jar}" \
        edu.uva.liftlab.graphchecker.concolic.ConcolicComposedModelProjector \
        --smt "${composed_smt}" \
        --composition-manifest "${composition_manifest}" \
        --upstream-summaries "${projection_summaries}" \
        --static-graph "${static_graph}" \
        "${producer_args[@]}" \
        --target-activations "${target_activation_plan}" \
        --fatal-query "${target_branch_queries}" \
        --target-activation-id "${target_activation_id}" \
        --z3 "${z3_binary}" \
        --output "${natural_plan}" \
        --manifest "${projection_manifest}"
    require_nonempty_input "projected natural replay plan" "${natural_plan}"
    require_nonempty_input "model projection manifest" \
        "${projection_manifest}"
    if ! jq -e --arg activation "${target_activation_id}" '
            .projectionComplete == true
            and .downstreamInjectionForbidden == true
            and .targetObservationActivation == $activation' \
            "${projection_manifest}" >/dev/null; then
        echo "[ERROR] Projector did not produce a complete upstream-only plan for the exact target" >&2
        return 1
    fi
    echo "[Concolic] producer mode: ${producer_mode}"
    echo "[Concolic] upstream-only model plan: ${natural_plan}"
}

do_validate_natural_replay() {
    local test_name="${1:-${causynth_workload_test}}"
    resolve_target_context "${test_name}"
    resolve_composition_paths
    resolve_natural_replay_paths
    require_nonempty_input "natural replay activation plan" "${natural_plan}"
    require_nonempty_input "natural replay results" "${natural_results}"
    require_nonempty_input "model projection manifest" \
        "${projection_manifest}"
    require_nonempty_input "GraphChecker jar" "${gc_jar}"
    require_absent_output "natural replay validation" "${natural_validation}"
    "${graphchecker_java_bin}" -cp "${gc_jar}" \
        edu.uva.liftlab.graphchecker.concolic.ConcolicNaturalReplayValidator \
        --plan "${natural_plan}" \
        --results "${natural_results}" \
        --projection-manifest "${projection_manifest}" \
        --output "${natural_validation}" \
        --expected-exception javax.security.sasl.SaslException \
        --expected-exception org.apache.hadoop.hdfs.protocol.datatransfer.InvalidEncryptionKeyException
    echo "[Concolic] natural replay validation: ${natural_validation}"
}

do_run_natural_replay() {
    local test_name="${1:-${causynth_workload_test}}"
    local replay_classes replay_static replay_status=0
    do_project_composed_model "${test_name}"
    # do_project_composed_model resolved and created this turn's fresh natural
    # directory.  Replay classes and replay-static output must be new children
    # of that directory, so do_process_concolic's rm -rf cannot reach any
    # historical v3/v4/v5 class snapshot or a campaign execution directory.
    replay_classes=$(realpath -m \
        "${CAUSYNTH_NATURAL_REPLAY_CLASSES_PATH:-${natural_dir}/concolic_classes}")
    replay_static=$(realpath -m \
        "${CAUSYNTH_NATURAL_REPLAY_STATIC_OUTPUT_DIR:-${natural_dir}/concolic-replay-static}")
    case "${replay_classes}" in
        "${natural_dir}"/*) ;;
        *)
            echo "[ERROR] Natural replay classes must be below ${natural_dir}: ${replay_classes}" >&2
            return 1
            ;;
    esac
    case "${replay_static}" in
        "${natural_dir}"/*) ;;
        *)
            echo "[ERROR] Natural replay static output must be below ${natural_dir}: ${replay_static}" >&2
            return 1
            ;;
    esac
    if [[ "${replay_classes}" == "${replay_static}" ]] \
            || [[ "${replay_classes}" == "${replay_static}"/* ]] \
            || [[ "${replay_static}" == "${replay_classes}"/* ]]; then
        echo "[ERROR] Natural replay classes and static output must be disjoint directories" >&2
        return 1
    fi
    require_absent_output "natural replay classes" "${replay_classes}"
    require_absent_output "natural replay static output" "${replay_static}"
    require_absent_output "natural replay results" "${natural_results}"
    concolic_classes_path="${replay_classes}"
    CAUSYNTH_CONCOLIC_STATIC_OUTPUT_DIR="${replay_static}" \
        do_process_concolic "${natural_plan}" ALL
    # A target exception can make Surefire exit non-zero.  Validation, not the
    # process status, decides success and requires every bounded producer,
    # the exact target observation, and zero downstream shortcuts.
    do_replay_concolic "${natural_plan}" ALL "${test_name}" \
        || replay_status=$?
    if [[ "${replay_status}" -ne 0 ]]; then
        echo "[Concolic] replay test exited ${replay_status}; validating the captured target failure"
    fi
    do_validate_natural_replay "${test_name}"
}

do_test() {
    verify_hadoop_source
    local test_name="${1:-${causynth_workload_test}}"
    local test_arg=""
    if [[ -n "${test_name}" ]]; then
        test_arg="-Dtest=${test_name}"
    fi
    local trace_test_name="${test_name:-all}"
    local safe_test_name
    safe_test_name=$(printf "%s" "${trace_test_name}" | tr -c 'A-Za-z0-9._-' '_')
    local -a isolated_test_data_args=()
    if [[ -n "${CAUSYNTH_TEST_BUILD_DATA:-}" ]]; then
        isolated_test_data_args+=(
            -Dtest.build.data="${CAUSYNTH_TEST_BUILD_DATA}"
            -Dtest.build.shared.data="${CAUSYNTH_TEST_BUILD_SHARED_DATA:-${CAUSYNTH_TEST_BUILD_DATA}-shared}"
            -Dhadoop.tmp.dir="${CAUSYNTH_HADOOP_TMP_DIR:-${CAUSYNTH_TEST_BUILD_DATA}-hadoop-tmp}"
        )
    fi
    local trace_dir="${causynth_output_dir}/unit-test-graphs/${safe_test_name}"
    if [[ -d "${trace_dir}" ]] \
            && [[ -n "$(find "${trace_dir}" -mindepth 1 -print -quit)" ]]; then
        echo "[ERROR] Refusing to delete or overwrite a non-empty runtime trace directory: ${trace_dir}" >&2
        echo "[ERROR] Select a fresh CAUSYNTH_OUTPUT_DIR for this immutable run." >&2
        exit 1
    fi
    mkdir -p "${trace_dir}"
    local static_graph_file="${causynth_output_dir}/static_dataflow_edges.jsonl"
    local regions_file="${causynth_output_dir}/symbolic_regions.jsonl"
    local region_edges_file="${causynth_output_dir}/symbolic_region_edges.jsonl"
    local required_static
    for required_static in "${static_graph_file}" "${regions_file}" \
            "${region_edges_file}"; do
        if [[ ! -s "${required_static}" ]]; then
            echo "[ERROR] Native static trace input is missing or empty: ${required_static}" >&2
            exit 1
        fi
    done
    local static_graph_lines static_region_lines static_region_edge_lines
    local static_graph_sha static_regions_sha static_region_edges_sha
    local graphchecker_jar_sha256
    static_graph_lines=$(wc -l < "${static_graph_file}" | tr -d '[:space:]')
    static_region_lines=$(wc -l < "${regions_file}" | tr -d '[:space:]')
    static_region_edge_lines=$(wc -l < "${region_edges_file}" | tr -d '[:space:]')
    static_graph_sha=$(shasum -a 256 "${static_graph_file}" | awk '{print $1}')
    static_regions_sha=$(shasum -a 256 "${regions_file}" | awk '{print $1}')
    static_region_edges_sha=$(shasum -a 256 "${region_edges_file}" | awk '{print $1}')
    graphchecker_jar_sha256=$(shasum -a 256 "${gc_jar}" | awk '{print $1}')
    local max_events="${CAUSYNTH_TRACE_MAX_EVENTS:-${causynth_trace_max_events:-2000000}}"
    local max_graph_edges="${CAUSYNTH_TRACE_MAX_GRAPH_EDGES:-${causynth_trace_max_graph_edges:-200000}}"
    local max_context_pairs="${CAUSYNTH_TRACE_MAX_CONTEXT_PAIRS_PER_EDGE:-${causynth_trace_max_context_pairs_per_edge:-2000}}"
    local trace_arg_line="-Dcausynth.trace.output.dir=${trace_dir} -Dcausynth.static.graph=${static_graph_file} -Dcausynth.trace.test=${trace_test_name} -Dcausynth.trace.max.events=${max_events} -Dcausynth.trace.max.graph.edges=${max_graph_edges} -Dcausynth.trace.max.context.pairs.per.edge=${max_context_pairs} -Dcausynth.trace.streaming.only=true -Dcausynth.trace.aggregate.on.shutdown=false"

    cd "${hdfs_dir}"
    "${hadoop_maven_bin}" surefire:test \
        ${test_arg} \
        ${isolated_test_data_args[@]+"${isolated_test_data_args[@]}"} \
        -DfailIfNoTests=false \
        -Dhadoop.log.dir="${hdfs_dir}/target/test-logs" \
        -Dcausynth.trace.output.dir="${trace_dir}" \
        -Dcausynth.static.graph="${static_graph_file}" \
        -Dcausynth.trace.test="${trace_test_name}" \
        -Dcausynth.trace.max.events="${max_events}" \
        -Dcausynth.trace.max.graph.edges="${max_graph_edges}" \
        -Dcausynth.trace.max.context.pairs.per.edge="${max_context_pairs}" \
        -Dcausynth.trace.streaming.only=true \
        -Dcausynth.trace.aggregate.on.shutdown=false \
        -DargLine="${trace_arg_line}"

    if [[ -s "${trace_dir}/runtime_trace.jsonl" ]]; then
        local raw_lines streaming_manifest
        raw_lines=$(wc -l < "${trace_dir}/runtime_trace.jsonl" \
            | tr -d '[:space:]')
        streaming_manifest="${trace_dir}/streaming_trace_manifest.json"
        if [[ ! -f "${streaming_manifest}" ]] \
                || ! jq -e --argjson rows "${raw_lines}" \
                    '.status == "CLOSED" and .complete == true
                     and .truncated == false and .writeFailure == false
                     and .attemptedEventCount == $rows' \
                    "${streaming_manifest}" >/dev/null; then
            echo "[ERROR] Native runtime trace did not close completely" >&2
            exit 1
        fi
        "${graphchecker_java_bin}" -Xmx"${CAUSYNTH_TRACE_OFFLINE_AGGREGATION_HEAP:-${causynth_trace_offline_aggregation_heap:-6g}}" \
            -cp "${gc_jar}" \
            edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder \
            --trace-dir "${trace_dir}" \
            --static-graph "${static_graph_file}" \
            --regions "${regions_file}" \
            --region-edges "${region_edges_file}" \
            --test "${trace_test_name}" \
            --max-graph-edges "${max_graph_edges}" \
            --max-context-pairs-per-edge "${max_context_pairs}"
        if ! jq -e --argjson rows "${raw_lines}" \
                '(.traceEventCount + .fieldEventCount
                  + .executionEventCount) == $rows
                 and .truncated == false and .roleTruncated == false' \
                "${trace_dir}/summary.json" >/dev/null; then
            echo "[ERROR] Native offline trace aggregation is incomplete" >&2
            exit 1
        fi
        if [[ ! -f "${trace_dir}/runtime_region_summary.json" ]] \
                || ! jq -e --argjson regions "${static_region_lines}" \
                    --argjson edges "${static_region_edge_lines}" \
                    '.truncated == false
                     and .staticRegionCount == $regions
                     and .staticRegionEdgeCount == $edges' \
                    "${trace_dir}/runtime_region_summary.json" >/dev/null; then
            echo "[ERROR] Native offline aggregation did not consume the exact static region catalogs" >&2
            exit 1
        fi
        local raw_sha
        raw_sha=$(shasum -a 256 "${trace_dir}/runtime_trace.jsonl" \
            | awk '{print $1}')
        jq -n \
            --arg mode "FRESH_JVM_OFFLINE_AGGREGATION_OF_NATIVE_STREAM" \
            --arg rawTrace "$(realpath "${trace_dir}/runtime_trace.jsonl")" \
            --arg rawTraceSha256 "${raw_sha}" \
            --argjson rawTraceLineCount "${raw_lines}" \
            --arg graphCheckerJar "$(realpath "${gc_jar}")" \
            --arg graphCheckerJarSha256 "${graphchecker_jar_sha256}" \
            --arg staticGraph "$(realpath "${static_graph_file}")" \
            --arg staticGraphSha256 "${static_graph_sha}" \
            --argjson staticGraphLineCount "${static_graph_lines}" \
            --arg symbolicRegions "$(realpath "${regions_file}")" \
            --arg symbolicRegionsSha256 "${static_regions_sha}" \
            --argjson symbolicRegionCount "${static_region_lines}" \
            --arg symbolicRegionEdges "$(realpath "${region_edges_file}")" \
            --arg symbolicRegionEdgesSha256 "${static_region_edges_sha}" \
            --argjson symbolicRegionEdgeCount "${static_region_edge_lines}" \
            '{schemaVersion:1, mode:$mode, rawTrace:$rawTrace,
              rawTraceSha256:$rawTraceSha256,
              rawTraceLineCount:$rawTraceLineCount,
              graphCheckerJar:$graphCheckerJar,
              graphCheckerJarSha256:$graphCheckerJarSha256,
              staticGraph:$staticGraph,
              staticGraphSha256:$staticGraphSha256,
              staticGraphLineCount:$staticGraphLineCount,
              symbolicRegions:$symbolicRegions,
              symbolicRegionsSha256:$symbolicRegionsSha256,
              symbolicRegionCount:$symbolicRegionCount,
              symbolicRegionEdges:$symbolicRegionEdges,
              symbolicRegionEdgesSha256:$symbolicRegionEdgesSha256,
              symbolicRegionEdgeCount:$symbolicRegionEdgeCount,
              replayJvmAggregation:false, complete:true}' \
            > "${trace_dir}/offline_aggregation_provenance.json"
    else
        cat > "${trace_dir}/summary.json" <<EOF
{"test":"${trace_test_name}","status":"no_runtime_trace","message":"No instrumented selected method executed; the requested test may not exist or may not touch the selected static graph."}
EOF
    fi
}

do_restore() {
    verify_hadoop_source
    "${hadoop_maven_bin}" -f "${hdfs_dir}/pom.xml" clean compile -DskipTests
}

cmd="${1:-help}"
shift || true

case "${cmd}" in
    build)
        timing "build" do_build
        ;;
    build-hadoop)
        timing "build-hadoop" do_build_hadoop
        ;;
    compile)
        timing "compile" do_compile
        ;;
    process|instrument)
        timing "process" do_process
        ;;
    verify-region-roots)
        timing "verify-region-roots" verify_hdfs_region_roots "${1:-}"
        ;;
    test)
        timing "test" do_test "${1:-}"
        ;;
    run)
        timing "process" do_process
        timing "test" do_test "${1:-}"
        ;;
    schedule-concolic)
        timing "schedule-concolic" do_schedule_concolic \
            "${1:-}" "${2:-}" "${3:-}"
        ;;
    schedule-concolic-capture)
        CAUSYNTH_CAPTURE_ONLY=true timing "schedule-concolic-capture" \
            do_schedule_concolic "${1:-}" "${2:-}" "${3:-}"
        ;;
    process-concolic)
        timing "process-concolic" do_process_concolic \
            "${1:-}" "${2:-}"
        ;;
    replay-concolic)
        timing "replay-concolic" do_replay_concolic \
            "${1:-}" "${2:-}" "${3:-}"
        ;;
    replay-concolic-batch)
        timing "replay-concolic-batch" do_replay_concolic_batch "${1:-}"
        ;;
    import-concolic)
        timing "import-concolic" do_import_concolic \
            "${1:-}" "${2:-}" "${3:-}" "${4:-}"
        ;;
    campaign-concolic)
        timing "campaign-concolic" do_campaign_concolic "${1:-}"
        ;;
    publish-campaign-handoff)
        timing "publish-campaign-handoff" do_publish_campaign_handoff \
            "${1:-}" "${2:-}"
        ;;
    verify-campaign-handoff)
        timing "verify-campaign-handoff" do_verify_campaign_handoff \
            "${1:-}"
        ;;
    campaign-capture)
        timing "campaign-capture" do_campaign_capture "${1:-}"
        ;;
    hdfs-port-map)
        timing "hdfs-port-map" do_hdfs_port_map "${1:-}"
        ;;
    compose-smt)
        timing "compose-smt" do_compose_smt "${1:-}"
        ;;
    derive-producer-groups)
        timing "derive-producer-groups" do_derive_producer_groups "${1:-}"
        ;;
    verify-relationships)
        timing "verify-relationships" do_verify_relationships "${1:-}"
        ;;
    project-composed-model)
        timing "project-composed-model" do_project_composed_model "${1:-}"
        ;;
    validate-natural-replay)
        timing "validate-natural-replay" do_validate_natural_replay "${1:-}"
        ;;
    run-natural-replay)
        timing "run-natural-replay" do_run_natural_replay "${1:-}"
        ;;
    restore)
        timing "restore" do_restore
        ;;
    help|--help|-h)
        usage
        ;;
    *)
        echo "[ERROR] Unknown command: ${cmd}"
        usage
        exit 1
        ;;
esac

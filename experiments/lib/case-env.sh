# case-env.sh -- sourced by every lib script: one case's declarations.
#
#   source case-env.sh <case-dir> <case-id>
#
# A case directory, experiments/<system>/<case>, holds DECLARATIONS only
# (case.sh, workflow.properties, target.yaml and the *.jsonl the campaign
# reads); everything executable is here, one copy for every case of every
# system.  What a system's trees are -- how they build, where their classes
# and test reports are, what every workload JVM of theirs needs -- is its
# experiments/<system>/system.sh, sourced before the case.  case.sh sets,
# for the case id it is given:
#   repo          the system's worktree the case runs
#   test_class    the workload's JUnit class
#   test_method   its test method m, or one invocation m[k] of a parameterized
#                 test or class (m[i][j] for both; runtime/JUnitInvocation)
#   scope         the analysis scope, one "<root>:<class path>" per entry,
#                 root one the system names (system_root); "=" after the root
#                 copies exactly that class and its nested classes (no prefix
#                 glob)
# and optionally
#   target_occurrence   the declared target (empty keeps every observed one)
#   loop_bounds         default: <case-dir>/loop-bounds.jsonl
#   target_spec         default: <case-dir>/target.yaml; when there is none,
#                       run.sh derives it from the tree's marker of the case
#                       (tools/lib/annotated.py)
#   recording_window    where the recorded window opens, the same in every
#                       workload JVM of the run (execute.sh): empty, once the
#                       cluster is up; "startup", before the cluster starts,
#                       for a bug whose fatal value is set while it starts
#                       (owner-approved opt-in for that class of bug only;
#                       the system's cluster adapter must support it)
# system.sh defines, after the case is read,
#   system_paths        sets module, report, test_classes, lineage_roots
#   system_root <name>  a compiled class root the scope names
#   system_classpath    prints the workload's classpath
#   system_build        builds the tree and runs the workload once natively
#   system_jvm_properties <tmpdir> <datadir>
#                       sets jvm_properties, what every workload JVM needs
#   system_jar_first    whether GraphChecker's jar precedes the workload's
#                       classpath (true) or follows it (false)
case_dir=${1:?missing case directory}
case_id=${2-}
case_dir=$(cd "${case_dir}" && pwd -P)
case_name=$(basename "${case_dir}")
system_dir=$(dirname "${case_dir}")
here=${case_dir}
loop_bounds=${case_dir}/loop-bounds.jsonl
target_spec=${case_dir}/target.yaml
target_occurrence=
recording_window=
scope=()
# shellcheck source=/dev/null
source "${system_dir}/system.sh"
# shellcheck source=/dev/null
source "${case_dir}/case.sh" "${case_id}"
# The discovery hook, for every case alike: set but EMPTY, PLAN refuses with
# DECLARED_TARGET_OCCURRENCE_MISSING and lists every observed target
# occurrence -- the one honest way to re-read an address after an identity
# change.
target_occurrence=${CAUSYNTH_TARGET_OCCURRENCE_OVERRIDE-${target_occurrence}}
case "${recording_window}" in
  ""|startup) ;;
  *) echo "unknown recording_window: '${recording_window}'" >&2; return 2 ;;
esac
system_paths
tag=${case_name}${case_id:+-${case_id}}
# The run's output directory (run.sh exports it): where every artifact goes.
output_dir=${CAUSYNTH_OUTPUT_DIR:-/tmp/graphchecker-${tag}}
# The run's own copy of the case's scope, inside its output directory:
# prepare-analysis.sh empties and fills it, every static pass reads it, and
# FREEZE digests what EMIT checks it still is.  A campaign's output
# directory is on the filesystem every host of its pool mounts (its sessions
# are), so a pass placed on any host reads these classes (run_engine.sh
# campaign_head_charged), and it is the run's alone: no two runs share it.
analysis=${CAUSYNTH_ANALYSIS_CLASSES_DIR:-${output_dir}/declared-classes}
test_name=${test_class}#${test_method}

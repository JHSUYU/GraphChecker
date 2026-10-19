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
system_scope=()
# shellcheck source=../../tools/lib/gc-env.sh
source "$(dirname "${BASH_SOURCE[0]}")/../../tools/lib/gc-env.sh"
# shellcheck source=/dev/null
source "${system_dir}/system.sh"
# shellcheck source=/dev/null
source "${case_dir}/case.sh" "${case_id}"
target_occurrence=${CAUSYNTH_TARGET_OCCURRENCE_OVERRIDE-${target_occurrence}}
case "${recording_window}" in
  ""|startup) ;;
  *) echo "unknown recording_window: '${recording_window}'" >&2; return 2 ;;
esac
system_paths
tag=${case_name}${case_id:+-${case_id}}
output_dir=${CAUSYNTH_OUTPUT_DIR:-/tmp/graphchecker-${tag}}
analysis=${CAUSYNTH_ANALYSIS_CLASSES_DIR:-${output_dir}/declared-classes}
test_name=${test_class}#${test_method}

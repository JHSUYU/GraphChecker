#!/usr/bin/env bash

set -euo pipefail

selector_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
schema="${selector_dir}/selector-response.schema.json"
codex_bin=${GRAPH_CHECKER_CODEX_BIN:-codex}
temporary=$(mktemp -d /tmp/graphchecker-symbol-selector.XXXXXX)
request="${temporary}/request.json"
response="${temporary}/response.json"
trap 'rm -rf -- "${temporary}"' EXIT

command -v "${codex_bin}" >/dev/null 2>&1 \
  || { echo "codex command not found: ${codex_bin}" >&2; exit 1; }
command -v jq >/dev/null 2>&1 \
  || { echo "jq is required" >&2; exit 1; }
cat >"${request}"
jq -e '
  .schemaVersion == 1 and
  .kind == "GRAPH_CHECKER_SYMBOLIC_INPUT_SELECTION_REQUEST" and
  (.decisionId | type == "string") and
  (.candidateSetSha256 | type == "string") and
  (.candidates | type == "array" and length > 0)
' "${request}" >/dev/null

model_args=()
if [[ -n "${GRAPH_CHECKER_LLM_MODEL:-}" ]]; then
  model_args=(-m "${GRAPH_CHECKER_LLM_MODEL}")
fi
reasoning_effort=${GRAPH_CHECKER_LLM_REASONING_EFFORT:-medium}
case "${reasoning_effort}" in
  low|medium|high|xhigh) ;;
  *) echo "invalid GRAPH_CHECKER_LLM_REASONING_EFFORT: ${reasoning_effort}" >&2; exit 1 ;;
esac

{
  cat <<'EOF'
You are selecting symbolic input variables for one bounded software program-analysis task.

The JSON request is the complete authority. Its candidates have already passed the engine's deterministic type, trace, data-flow, and materialization checks. Select a minimal sufficient subset that can change the demanded branch or demanded producer outputs on a path toward the stated target. Use the supplied source/workload context to follow causal state across regions. Prefer configuration and persistent-state values that directly control relevant branches; omit incidental logging, formatting, buffer, and unrelated library values. Every candidate with required=true must be selected.

You may only return candidateId strings present in candidates. Do not invent program facts, variables, edges, formulas, or IDs. Do not run tools or inspect files. Echo decisionId and candidateSetSha256 exactly. Return only the JSON object required by the output schema. Keep rationale to one short sentence.

REQUEST:
EOF
  cat "${request}"
} | (
  cd "${temporary}"
  "${codex_bin}" exec --ephemeral --sandbox read-only \
    --skip-git-repo-check --ignore-rules \
    -c "model_reasoning_effort=\"${reasoning_effort}\"" \
    "${model_args[@]}" \
    --output-schema "${schema}" \
    --output-last-message "${response}" - >/dev/null
)

jq -e --slurpfile request "${request}" '
  .schemaVersion == 1 and
  .kind == "GRAPH_CHECKER_SYMBOLIC_INPUT_SELECTION_RESPONSE" and
  .decisionId == $request[0].decisionId and
  .candidateSetSha256 == $request[0].candidateSetSha256 and
  (.selectedCandidateIds | type == "array" and length > 0)
' "${response}" >/dev/null
cat "${response}"

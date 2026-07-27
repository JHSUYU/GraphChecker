#!/usr/bin/env bash

set -euo pipefail

if [[ $# -ne 1 || -z "$1" ]]; then
  echo "usage: $0 <user@server>" >&2
  exit 1
fi

server=$1
experiments_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker_dir=$(cd "${experiments_dir}/.." && pwd -P)
remote_root=target/manual-container-three-thread-rpc
download_root="${graphchecker_dir}/target/manual-container-three-thread-rpc-json"
run_id=$(date -u +%Y%m%dT%H%M%SZ)

mkdir -p "${download_root}"
output="${download_root}/${run_id}"
staging=$(mktemp -d "${download_root}/.download-${run_id}.XXXXXX")
[[ ! -e "${output}" ]] || {
  echo "download output already exists: ${output}" >&2
  exit 1
}

cleanup() {
  rm -rf -- "${staging}"
}
trap cleanup EXIT

for command_name in ssh tar jq; do
  command -v "${command_name}" >/dev/null 2>&1 || {
    echo "required command not found: ${command_name}" >&2
    exit 1
  }
done

mkdir -p "${staging}/source" "${staging}/converted"

echo "[manual-container-json] downloading JSON artifacts from ${server}:${remote_root}"
ssh -- "${server}" \
  "set -eu; test -d '${remote_root}'; cd '${remote_root}'; find . -type f \\( -name '*.json' -o -name '*.jsonl' \\) -print0 | tar --null -czf - --files-from=-" \
  | tar -xzf - -C "${staging}/source"

json_count=0
jsonl_count=0
while IFS= read -r -d '' source; do
  relative=${source#"${staging}/source/"}
  case "${relative}" in
    *.jsonl)
      destination="${staging}/converted/${relative%.jsonl}.json"
      if [[ -e "${destination}" ]]; then
        echo "converted path conflicts with an existing JSON file: ${relative%.jsonl}.json" >&2
        exit 1
      fi
      mkdir -p "$(dirname "${destination}")"
      jq -s . "${source}" >"${destination}"
      jsonl_count=$((jsonl_count + 1))
      ;;
    *.json)
      destination="${staging}/converted/${relative}"
      if [[ -e "${destination}" ]]; then
        echo "downloaded JSON conflicts with a converted JSONL file: ${relative}" >&2
        exit 1
      fi
      mkdir -p "$(dirname "${destination}")"
      cp -p -- "${source}" "${destination}"
      json_count=$((json_count + 1))
      ;;
  esac
done < <(find "${staging}/source" -type f \
  \( -name '*.json' -o -name '*.jsonl' \) -print0)

if (( json_count + jsonl_count == 0 )); then
  echo "remote artifact directory contains no .json or .jsonl files" >&2
  exit 1
fi

mv -- "${staging}/converted" "${output}"

echo "[manual-container-json] complete"
echo "  JSON copied: ${json_count}"
echo "  JSONL converted: ${jsonl_count}"
echo "  output: ${output}"

#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
# shellcheck source=../lib/gc-env.sh
source "${here}/../lib/gc-env.sh"
read -r -a hosts <<<"${LIFTS}"
server=${BULK_SERVER:-${hosts[0]}}
subnet=${BULK_SUBNET:?setup-nodes.sh: name the hosts private subnet as BULK_SUBNET, e.g. 10.10.1.0/24}
disk=${BULK_DISK:-/dev/sdb}
ssh -o BatchMode=yes "${server}" 'bash -s' "${server}" "${subnet}" "${disk}" <"${here}/setup-node.sh"
for host in "${hosts[@]}"; do
  [[ "${host}" != "${server}" ]] || continue
  ssh -o BatchMode=yes "${host}" 'bash -s' "${server}" "${subnet}" "${disk}" <"${here}/setup-node.sh" &
done
wait
if [[ ! -x "${GC_BULK}/bin/z3" ]]; then
  dl=$(mktemp -d "${GC_BULK}/z3.XXXXXX")
  curl -sSL -o "${dl}/z3.zip" https://github.com/Z3Prover/z3/releases/download/z3-4.14.1/z3-4.14.1-x64-glibc-2.35.zip
  unzip -q -o "${dl}/z3.zip" -d "${dl}"
  cp "${dl}"/z3-4.14.1-x64-glibc-2.35/bin/z3 "${GC_BULK}/bin/z3"
  rm -rf "${dl:?}"
fi
for host in "${hosts[@]}"; do
  ssh -o BatchMode=yes "${host}" "sudo ln -sfn ${GC_BULK}/bin/z3 /usr/local/bin/z3; ln -sfn ${GC_BULK}/bin/z3 \${HOME}/.local/bin/z3; echo \$(hostname -s): \$(z3 --version), \$(java -version 2>&1 | head -1), \$(df -h /bulk | tail -1 | awk '{print \$4}') free on /bulk"
done

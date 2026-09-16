#!/usr/bin/env bash
# restore_slots.sh <id> <corpus-dir> <case-dir>
#
# Re-derive <corpus>/schedule/iteration-0000/slots.jsonl by replaying the
# campaign's explore waves with the corpus's OWN frozen jar, in a staging
# iteration directory of symlinks -- nothing is written under the corpus.
# SlotTable.read reads only <iteration>/slots.jsonl and reconcile() takes the
# corpus's session rows plus the anchor's closure (SlotTable.java:139-152,
# :164-165, :192+), so the table is a fold: empty -> wave 0 (seed session
# only) -> wave 1 (every session), which is what this replays.
set -euo pipefail
ID=$1; CORPUS=$2; CASE_DIR=$3
MY=/tmp/claude-20003/-opt-GraphChecker/10153a9a-290a-45d1-b3c9-072f259e090e/scratchpad
JAVA=/usr/lib/jvm/java-8-openjdk-amd64/bin/java
Z3=/usr/local/bin/z3
R="${MY}/gate3/restore/${ID}"
IT="${CORPUS}/schedule/iteration-0000"
JAR="${CORPUS}/schedule/frozen-inputs/GraphChecker.jar"
prop() { sed -n "s/^$1=//p" "${CASE_DIR}/workflow.properties" | tail -n 1; }
resolve() { case "$1" in "") ;; /*) echo "$1";; @config/*) echo "${CASE_DIR}/${1#@config/}";; *) echo "$1";; esac; }
ANCHOR=$(prop declared_target_occurrence)
BOUND=$(prop causynth_loop_default_bound)
DOM=$(resolve "$(prop causynth_root_domains)")
MAXT=$(prop region_path_max_tasks)
MAXP=$(prop region_path_max_paths_per_region)
MAXF=$(prop region_path_max_flips_per_path)
ST=$(prop solver_timeout_ms); MV=$(prop compose_max_valuations)
EXTRA=()
[[ -z "${DOM}"  ]] || EXTRA+=(--root-domains "${DOM}")
[[ -z "${MAXP}" ]] || EXTRA+=(--max-paths-per-region "${MAXP}")
[[ -z "${MAXF}" ]] || EXTRA+=(--max-flips-per-path "${MAXF}")
[[ -z "${MAXT}" ]] || EXTRA+=(--max-tasks "${MAXT}")

# the campaign's last wave: the highest obligations-NNNN the corpus kept
LAST=$(ls -d "${IT}"/obligations-[0-9][0-9][0-9][0-9] | sed 's/.*obligations-0*//' \
  | sort -n | tail -1); LAST=${LAST:-0}
echo "[${ID}] frozen jar=$(sha256sum "${JAR}" | cut -c1-12) lastWave=${LAST} anchor=${ANCHOR:0:60}…"

rm -rf -- "${R}"; mkdir -p "${R}"
explore() { # <stage dir> <wave> <output-dir>
  ( cd "${R}" && nice -n 10 "${JAVA}" -Xmx8g \
      "-Dcausynth.loop.default.bound=${BOUND}" -cp "${JAR}" \
      edu.uva.liftlab.graphchecker.explore.ExploreMain \
      --sessions "$1/sessions" --results "$1/obligation_results.jsonl" \
      --static-scope-map "${CORPUS}/static_scope_map.jsonl" \
      --topology-epoch iteration-0000 --wave "$2" --output-dir "$3" \
      --target-occurrence "${ANCHOR}" "${EXTRA[@]}" </dev/null )
}

# ---- wave 0: the seed session only, no results, NO slots.jsonl present ----
mkdir -p "${R}/w0/sessions" "${R}/w0/obligations-0000"
for s in "${IT}"/sessions/seed-result-*; do ln -s "${s}" "${R}/w0/sessions/"; done
: >"${R}/w0/obligation_results.jsonl"
explore "${R}/w0" 0 "${R}/w0/obligations-0000" >"${R}/w0.log" 2>&1
echo "[${ID}] wave 0 -> $(wc -l <"${R}/w0/slots.jsonl") slots, $(wc -l <"${R}/w0/obligations-0000/obligations.jsonl") obligations"

# ---- waves 1..LAST: every session, the campaign's results, prior table ----
prev="${R}/w0"
for w in $(seq 1 "${LAST}"); do
  d=$(printf '%s/w%d' "${R}" "${w}")
  mkdir -p "${d}/sessions"
  for s in "${IT}"/sessions/*; do ln -s "${s}" "${d}/sessions/"; done
  install -m 644 "${IT}/obligation_results.jsonl" "${d}/obligation_results.jsonl"
  for p in $(seq 0 $((w - 1))); do
    ln -s "$(printf '%s/obligations-%04d' "${IT}" "${p}")" \
      "$(printf '%s/obligations-%04d' "${d}" "${p}")"
  done
  install -m 644 "${prev}/slots.jsonl" "${d}/slots.jsonl"
  out=$(printf '%s/obligations-%04d' "${d}" "${w}")
  mkdir -p "${out}"
  explore "${d}" "${w}" "${out}" >"${R}/w${w}.log" 2>&1
  echo "[${ID}] wave ${w} -> $(wc -l <"${d}/slots.jsonl") slots"
  prev="${d}"
done
RESTORED="${prev}/slots.jsonl"

# ---- does the replayed last wave equal the campaign's last wave? ----
ref=$(printf '%s/obligations-%04d' "${IT}" "${LAST}")
got=$(printf '%s/obligations-%04d' "${prev}" "${LAST}")
for f in obligations.jsonl tasks.jsonl gaps.jsonl explore_manifest.json; do
  a=$(LC_ALL=C sort "${ref}/${f}" | sha256sum | cut -d' ' -f1)
  b=$(LC_ALL=C sort "${got}/${f}" | sha256sum | cut -d' ' -f1)
  printf '[%s] wave-%d %-22s %s\n' "${ID}" "${LAST}" "${f}" \
    "$([[ "${a}" == "${b}" ]] && echo identical || echo "DIFFERS")"
done
echo "[${ID}] slots rows: corpus-now=$(wc -l <"${IT}/slots.jsonl") replayed=$(wc -l <"${RESTORED}") manifest-says=$(jq -r '.skeleton.slots' "${ref}/explore_manifest.json")"
echo "[${ID}] slots sha:  corpus-now=$(LC_ALL=C sort "${IT}/slots.jsonl" | sha256sum | cut -c1-16) replayed=$(LC_ALL=C sort "${RESTORED}" | sha256sum | cut -c1-16)"
cmp -s "${IT}/slots.jsonl" "${RESTORED}" \
  && echo "[${ID}] VERDICT: the corpus file is byte-identical to the replay -- nothing was lost" \
  || echo "[${ID}] VERDICT: the corpus file DIFFERS from the replay"

# ---- compose with the frozen jar, restored vs corpus-now, vs the corpus ----
compose() { # <iteration dir> <tag>
  local it=$1
  local tag=$2
  local o="${R}/compose-${tag}"
  mkdir -p "${o}"
  local -a a=(--sessions "${it}/sessions" --output "${o}/candidate.smt2"
    --manifest "${o}/candidate_composition_manifest.json"
    --solver-timeout-ms "${ST}" --max-valuations "${MV}" --z3 "${Z3}"
    --anchor "${ANCHOR}")
  [[ -z "${DOM}" ]] || a+=(--root-domains "${DOM}")
  ( cd "${o}" && nice -n 10 "${JAVA}" -Xmx8g \
      "-Dcausynth.loop.default.bound=${BOUND}" -cp "${JAR}" \
      edu.uva.liftlab.graphchecker.compose.ComposeMain "${a[@]}" \
      </dev/null ) >"${o}/compose.log" 2>&1
}
norm() { python3 "${MY}/gate3/norm.py" "$1" --mask "$2=<X>" | sha256sum | cut -c1-16; }
mkdir -p "${R}/damaged"; ln -s "${prev}/sessions" "${R}/damaged/sessions"
for p in $(seq 0 "${LAST}"); do
  ln -s "$(printf '%s/obligations-%04d' "${IT}" "${p}")" \
    "$(printf '%s/obligations-%04d' "${R}/damaged" "${p}")"
done
install -m 644 "${IT}/slots.jsonl" "${R}/damaged/slots.jsonl"
compose "${prev}" restored
compose "${R}/damaged" damaged
echo "[${ID}] compose smt2   corpus=$(sha256sum "${CORPUS}/schedule/final/candidate.smt2" | cut -c1-16) restored=$(sha256sum "${R}/compose-restored/candidate.smt2" | cut -c1-16) damaged=$(sha256sum "${R}/compose-damaged/candidate.smt2" | cut -c1-16)"
echo "[${ID}] compose manif  corpus=$(norm "${CORPUS}/schedule/final/candidate_composition_manifest.json" "${CORPUS}") restored=$(norm "${R}/compose-restored/candidate_composition_manifest.json" "${R}/compose-restored") damaged=$(norm "${R}/compose-damaged/candidate_composition_manifest.json" "${R}/compose-damaged")"
echo "[${ID}] restored slots.jsonl: ${RESTORED}"

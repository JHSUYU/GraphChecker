#!/usr/bin/env bash
# confirmrun.sh REMOTE_WORKER_SH ITERATION WORKER SESSIONS [JAVA_OPTS]
# WORKER is an explore.ConfirmMain output directory under ~/gc-out (the seed plan is
# hard-linked into it); REMOTE_WORKER_SH is any remote-worker.sh of the same round.
# One CONFIRM replay + decision, in the environment a round's worker ran with.
set -uo pipefail
script=$1 iteration=$2 worker=$3 sessions=$4 opts=${5:-}
engine=$(grep -o '[^ ]*/run_engine.sh' "$script" | head -1)
config=$(grep -o -- '--config [^ ]*' "$script" | head -1 | cut -d' ' -f2)
jar=$(grep -o -- '--graphchecker-jar [^ ]*' "$script" | head -1 | cut -d' ' -f2)
inner=$worker/../confirm-inner.sh
cat > "$inner" <<INNER
source $engine
initialize_config $config
graphchecker_jar=$jar
campaign_init_local_scratch_root
export CAUSYNTH_WORKLOAD_JAVA_OPTS='$opts'
campaign_obligation_replay CONFIRM $iteration/instrumented-classes $worker $sessions $iteration/seed-replay/execution_task_plan.jsonl
campaign_confirm_decide $worker $sessions
INNER
outer=$worker/../confirm-outer.sh
{ echo '#!/usr/bin/env bash'; sed -n '/^  env \\$/,/run_engine.sh --config/p' "$script" | sed '$d'; echo "    bash $inner"; } > "$outer"
bash "$outer"

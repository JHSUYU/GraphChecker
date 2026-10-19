#!/usr/bin/env bash
min=6
host=""
while [[ $1 == -g || $1 == -h ]]; do
  if [[ $1 == -g ]]; then min=$2; else host=$2; fi
  shift 2
done
[[ -n $host ]] || host=$("$(dirname "${BASH_SOURCE[0]}")/pick-lift.sh" "$min")
[[ -n $host ]] || { echo "onlift: no host has ${min} GB free" >&2; exit 75; }
echo "onlift: running on $host" >&2
exec ssh -o BatchMode=yes "$host" "cd $(printf %q "$PWD") && unset SSH_CLIENT SSH2_CLIENT && export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64 PATH=/usr/lib/jvm/java-8-openjdk-amd64/bin:/usr/lib/maven/bin:\$PATH && $(printf '%q ' "$@")"

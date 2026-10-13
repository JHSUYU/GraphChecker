#!/usr/bin/env bash
# onlift.sh [-g min-free-gb] [-h host] <command...>: runs the command in the
# current directory on the least loaded host of LIFTS (pick-lift.sh; never
# lift11, the control host, unless LIFTS names it), or on the named host,
# with JAVA_HOME/PATH set for the Java 8 + Maven toolchain.
# Use it for mvn, the shell test, tree and VM builds, offline stages and
# anything heavy; the current directory must be on storage every host mounts.
#
# SSH_CLIENT/SSH2_CLIENT are unset first: Ubuntu's bash re-reads
# /etc/bash.bashrc and ~/.bashrc in any `bash -c` that sees SSH_CLIENT at
# shell level 1, and the command below is exec'd without a fork (SHLVL drops
# back to 0), so a `bash -c ...` command re-ran ~/.bashrc and got whatever
# JAVA_HOME it exports back.  ssh drops exported variables: pass them in the
# command (`onlift.sh env VAR=... cmd`).
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

package edu.uva.liftlab.graphchecker.smt;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;

/**
 * A fixture z3 written for one-shot asks -- it reads its whole input and
 * answers by what the input contains -- made to answer a scoped z3's
 * questions too ({@link Z3Incremental}): each command up to an echo mark is
 * answered by the fixture over the shared part, the scope and that command,
 * as a one-shot ask of that question would be; an input with no mark is a
 * one-shot ask, the fixture's own.  SIGINT is ignored: the fixture answers
 * at once.  As z3 is one process, nothing of it outlives it: a one-shot
 * ask execs the fixture, and a scope's fixture is its direct child, ended
 * with it ({@code setpriv --pdeathsig}), never one left in a subshell to
 * answer -- and log -- after its z3 was stopped.
 */
public final class ScopedFixture {

    private ScopedFixture() {
    }

    /** The fixture at {@code oneShot}, answering scopes too: a script next
     *  to it. */
    public static Path of(Path oneShot) throws IOException {
        Path scoped = oneShot.resolveSibling(oneShot.getFileName()
                + "-scoped");
        Files.write(scoped, Arrays.asList("#!/bin/bash",
                "trap '' INT",
                "fixture='" + oneShot + "'",
                "work=$(mktemp -d \"$(dirname \"$fixture\")/scoped.XXXXXX\")",
                "args=(\"$@\")",
                "all=''; shared=''; scope=''; command=''; inscope=0; marked=0",
                "while IFS= read -r line || [[ -n $line ]]; do",
                "  all+=\"$line\"$'\\n'",
                "  case $line in",
                "    '(echo \"'*)",
                "      marked=1",
                "      mark=${line#'(echo \"'}; mark=${mark%'\")'}",
                "      if [[ -n $command ]]; then",
                "        suffix=$'(check-sat)\\n'",
                "        [[ $command == '(check-sat)' ]]"
                        + " || suffix+=\"$command\"$'\\n'",
                "        printf '%s' \"$shared$scope$suffix\" >\"$work/in\"",
                "        setpriv --pdeathsig KILL -- \"$fixture\" \"${args[@]}\""
                        + " <\"$work/in\" >\"$work/out\"; status=$?",
                "        out=$(<\"$work/out\")",
                "        [[ $command == '(check-sat)' ]]"
                        + " || out=$(printf '%s\\n' \"$out\" | tail -n +2)",
                "        [[ -z $out ]] || printf '%s\\n' \"$out\"",
                "        if (( status == 101 ))"
                        + " || [[ $out == *'(error \"out of memory\")'* ]];"
                        + " then exit 101; fi",
                "        command=''",
                "      fi",
                "      printf '%s\\n' \"$mark\" ;;",
                "    '(push 1)') inscope=1; scope='' ;;",
                "    '(pop 1)') inscope=0; scope='' ;;",
                "    '(check-sat)'|'(get-value '*|'(get-unsat-core)'"
                        + "|'(get-info '*) command=$line ;;",
                "    *) if (( inscope )); then scope+=\"$line\"$'\\n';"
                        + " else shared+=\"$line\"$'\\n'; fi ;;",
                "  esac",
                "done",
                "(( marked )) && exit 0",
                "printf '%s' \"$all\" >\"$work/in\"",
                "exec \"$fixture\" \"${args[@]}\" <\"$work/in\""),
                StandardCharsets.UTF_8);
        if (!scoped.toFile().setExecutable(true)) {
            throw new IOException("not executable: " + scoped);
        }
        return scoped;
    }

    /**
     * What stands in for ssh in {@code dir}: its first argument the host,
     * the rest the command, run here as ssh's login shell runs it, in a
     * shell of its own, so a z3 there ends with it as with its sshd
     * ({@code setpriv --pdeathsig}); host {@code gone} refuses, as ssh to a
     * host that is down does.
     */
    public static Path ssh(Path dir) throws IOException {
        Path ssh = dir.resolve("ssh");
        Files.write(ssh, Arrays.asList("#!/bin/bash",
                "host=$1; shift",
                "if [[ $host == gone ]]; then",
                "  echo \"ssh: connect to host $host port 22:"
                        + " Connection refused\" >&2; exit 255",
                "fi",
                "if [[ $host == busy ]]; then",
                "  n=$(cat \"$0.busy\" 2>/dev/null || echo 0)",
                "  echo $((n + 1)) >\"$0.busy\"",
                "  if (( n < 2 )); then",
                "    echo \"kex_exchange_identification: Connection closed"
                        + " by remote host\" >&2; exit 255",
                "  fi",
                "fi",
                "bash -c \"$*\""), StandardCharsets.UTF_8);
        if (!ssh.toFile().setExecutable(true)) {
            throw new IOException("not executable: " + ssh);
        }
        return ssh;
    }
}

package edu.uva.liftlab.graphchecker.smt;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;

public final class ScopedFixture {

    private ScopedFixture() {
    }

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
                "setsid bash -c \"$*\" <&0 &",
                "pid=$!",
                "wait \"$pid\"; status=$?",
                "kill -KILL -- \"-$pid\" 2>/dev/null",
                "exit \"$status\""), StandardCharsets.UTF_8);
        if (!ssh.toFile().setExecutable(true)) {
            throw new IOException("not executable: " + ssh);
        }
        return ssh;
    }
}

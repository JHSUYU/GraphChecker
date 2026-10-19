package edu.uva.liftlab.graphchecker.runtime;

import java.io.FileDescriptor;
import java.io.FileOutputStream;
import java.io.PrintStream;

final class EngineConsole {
    private static final PrintStream ERR = new PrintStream(
            new FileOutputStream(FileDescriptor.err), true);

    private EngineConsole() {
    }

    static void println(String line) {
        ConcolicVmBroker.asEngineWork(() -> ERR.println(line));
    }

    static void trace(Throwable thrown) {
        ConcolicVmBroker.asEngineWork(() -> thrown.printStackTrace(ERR));
    }
}

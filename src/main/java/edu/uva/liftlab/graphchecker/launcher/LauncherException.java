package edu.uva.liftlab.graphchecker.launcher;

/** A launcher failure that names the prerequisite or step that failed. */
public final class LauncherException extends Exception {
    private static final long serialVersionUID = 1L;

    private final LauncherDiagnostic diagnostic;

    public LauncherException(LauncherDiagnostic diagnostic, String detail) {
        this(diagnostic, detail, null);
    }

    public LauncherException(LauncherDiagnostic diagnostic, String detail,
                             Throwable cause) {
        super(diagnostic + ": " + detail, cause);
        this.diagnostic = diagnostic;
    }

    public LauncherDiagnostic diagnostic() {
        return diagnostic;
    }
}

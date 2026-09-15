package edu.uva.liftlab.graphchecker.d3.plan;

/**
 * Static declaration emitted for an explicit application-side symbolize hook.
 * It names the exact source field; the hook's live owner argument identifies
 * the receiver, and runtime occurrence admission rejects one source id
 * resolving to more than one object.  It deliberately does not name an
 * output: the runtime-selected output slice is the authority for which
 * responses that field can influence.
 */
public final class StaticSymbolicSourceDeclaration {
    public static final int SCHEMA_VERSION = 1;
    public static final String FIELD = "declaredSymbolicSources";
    public static final String KIND = "STATIC_SYMBOLIC_SOURCE_DECLARATION";
    public static final String AUTHORITY = "EXPLICIT_SYMBOLIZE_HOOK_V1";

    private StaticSymbolicSourceDeclaration() {
    }
}

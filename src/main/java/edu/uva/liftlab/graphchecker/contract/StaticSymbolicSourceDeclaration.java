package edu.uva.liftlab.graphchecker.contract;

/**
 * Static declaration emitted for an explicit application-side symbolize
 * hook. It names the exact source field, while the hook's live owner argument
 * identifies the receiver object. The owner may be a region receiver or an
 * exact object first selected from an array/Map; runtime occurrence admission
 * rejects one source id resolving to more than one object. The declaration
 * deliberately does not name an output: the runtime-selected output slice is
 * the authority for which response(s) that field can influence.
 */
public final class StaticSymbolicSourceDeclaration {
    public static final int SCHEMA_VERSION = 1;
    public static final String FIELD = "declaredSymbolicSources";
    public static final String KIND = "STATIC_SYMBOLIC_SOURCE_DECLARATION";
    public static final String AUTHORITY = "EXPLICIT_SYMBOLIZE_HOOK_V1";

    private StaticSymbolicSourceDeclaration() {
    }
}

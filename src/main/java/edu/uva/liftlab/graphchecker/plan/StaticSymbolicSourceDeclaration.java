package edu.uva.liftlab.graphchecker.plan;

/** Declaration for an explicit symbolize hook: names the source field only. The
 *  hook's owner argument identifies the receiver; the runtime output slice, not
 *  this declaration, decides which responses the field can influence. */
public final class StaticSymbolicSourceDeclaration {
    public static final int SCHEMA_VERSION = 1;
    public static final String FIELD = "declaredSymbolicSources";
    public static final String KIND = "STATIC_SYMBOLIC_SOURCE_DECLARATION";
    public static final String AUTHORITY = "EXPLICIT_SYMBOLIZE_HOOK_V1";

    private StaticSymbolicSourceDeclaration() {
    }
}

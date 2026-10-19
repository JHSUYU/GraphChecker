package edu.uva.liftlab.graphchecker.plan;

public final class StaticSymbolicSourceDeclaration {
    public static final int SCHEMA_VERSION = 1;
    public static final String FIELD = "declaredSymbolicSources";
    public static final String KIND = "STATIC_SYMBOLIC_SOURCE_DECLARATION";
    public static final String AUTHORITY = "EXPLICIT_SYMBOLIZE_HOOK_V1";
    public static final String CONFIG_AUTHORITY = "AUTOMATIC_CONFIG_READ_V1";

    private StaticSymbolicSourceDeclaration() {
    }

    public static boolean authority(String stated) {
        return AUTHORITY.equals(stated) || CONFIG_AUTHORITY.equals(stated);
    }
}

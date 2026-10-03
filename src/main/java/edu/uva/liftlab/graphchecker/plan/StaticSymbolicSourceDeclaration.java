package edu.uva.liftlab.graphchecker.plan;

/** Declaration of a configured source a region mints: names the source and
 *  its field only, by a tree's symbolize hook ({@link #AUTHORITY}) or by the
 *  engine's configuration read ({@link #CONFIG_AUTHORITY}).  The mint's owner
 *  identifies the receiver; the runtime output slice, not this declaration,
 *  decides which responses the field can influence. */
public final class StaticSymbolicSourceDeclaration {
    public static final int SCHEMA_VERSION = 1;
    public static final String FIELD = "declaredSymbolicSources";
    public static final String KIND = "STATIC_SYMBOLIC_SOURCE_DECLARATION";
    public static final String AUTHORITY = "EXPLICIT_SYMBOLIZE_HOOK_V1";
    public static final String CONFIG_AUTHORITY = "AUTOMATIC_CONFIG_READ_V1";

    private StaticSymbolicSourceDeclaration() {
    }

    /** Whether a declaration states one of the two authorities. */
    public static boolean authority(String stated) {
        return AUTHORITY.equals(stated) || CONFIG_AUTHORITY.equals(stated);
    }
}

package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §2.2: one write, the producer half of a STATE interaction.
 * {@code version} joins reads within a run; across runs the endpoint is the
 * identity (CONTRACT-SPEC §1).
 */
public final class WriteRow extends Value {
    private final String sessionId;
    private final long seq;
    private final Endpoint endpoint;
    private final LocationId location;
    private final long version;
    private final String expressionRef;
    private final String javaType;
    private final Referent referentState;
    private final String referentStateRefused;

    private WriteRow(String sessionId, long seq, Endpoint endpoint,
                     LocationId location, long version, String expressionRef,
                     String javaType, Referent referentState,
                     String referentStateRefused) {
        this.sessionId = sessionId;
        this.seq = seq;
        this.endpoint = endpoint;
        this.location = location;
        this.version = version;
        this.expressionRef = expressionRef;
        this.javaType = javaType;
        this.referentState = referentState;
        this.referentStateRefused = referentStateRefused;
    }

    public static WriteRow of(String sessionId, long seq, Endpoint endpoint,
                              LocationId location, long version,
                              String expressionRef, String javaType) {
        return of(sessionId, seq, endpoint, location, version, expressionRef,
                javaType, null, null);
    }

    /** The same write of a reference, stating the state of the container
     *  it stored, or why none is stated (at most one of the two). */
    public static WriteRow of(String sessionId, long seq, Endpoint endpoint,
                              LocationId location, long version,
                              String expressionRef, String javaType,
                              Referent referentState,
                              String referentStateRefused) {
        String refused = Fields.optional(referentStateRefused);
        if (referentState != null && refused != null) {
            throw new IllegalArgumentException("referentState and "
                    + "referentStateRefused are exclusive");
        }
        return new WriteRow(Fields.text(sessionId, "sessionId"),
                Fields.nonNegative(seq, "seq"),
                Fields.required(endpoint, "endpoint"),
                Fields.required(location, "location"), version,
                Fields.required(expressionRef, "expressionRef"),
                Fields.text(javaType, "javaType"), referentState, refused);
    }

    public String sessionId() {
        return sessionId;
    }

    public long seq() {
        return seq;
    }

    public Endpoint endpoint() {
        return endpoint;
    }

    public LocationId location() {
        return location;
    }

    /** The version of the location this write produced. */
    public long version() {
        return version;
    }

    /** The expression the write stored, in the session's table. */
    public String expressionRef() {
        return expressionRef;
    }

    /** The JVM descriptor of the stored value. */
    public String javaType() {
        return javaType;
    }

    /**
     * The state of the container this write stored a reference to (or a
     * view or wrapper of one), as it was when the store ran: its canonical
     * {@code MAP} location and that location's live version.  Null when the
     * write stored no modeled container, or none is stated
     * ({@link #referentStateRefused}).
     */
    public Referent referentState() {
        return referentState;
    }

    /** Why a stored container's state is not stated, or null. */
    public String referentStateRefused() {
        return referentStateRefused;
    }

    @Override
    Object[] parts() {
        return new Object[] {sessionId, seq, endpoint, location, version,
                expressionRef, javaType, referentState, referentStateRefused};
    }

    @Override
    public String toString() {
        return "WriteRow{" + sessionId + "#" + seq + " " + endpoint + " "
                + location + " v" + version + ":" + javaType
                + (referentState == null ? "" : " -> " + referentState)
                + "}";
    }

    /** A container's {@code MAP} location and one version of it. */
    public static final class Referent extends Value {
        private final LocationId location;
        private final long version;

        private Referent(LocationId location, long version) {
            this.location = location;
            this.version = version;
        }

        public static Referent of(LocationId location, long version) {
            if (Fields.required(location, "referentState.location").kind()
                    != LocationKind.MAP) {
                throw new IllegalArgumentException("referentState names a "
                        + "MAP location; got " + location);
            }
            return new Referent(location, Fields.nonNegative(version,
                    "referentState.version"));
        }

        public LocationId location() {
            return location;
        }

        public long version() {
            return version;
        }

        @Override
        Object[] parts() {
            return new Object[] {location, version};
        }

        @Override
        public String toString() {
            return location + "@v" + version;
        }
    }
}

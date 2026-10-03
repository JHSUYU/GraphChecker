package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §2.2: one write, the producer half of a STATE interaction.
 * {@code version} joins reads within a run; across runs the endpoint is the
 * identity (CONTRACT-SPEC §1).  A location's INITIAL version is a row too
 * ({@link #initial}): Writers_W(l)'s writer at version 0.
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
    private final boolean initial;

    private WriteRow(String sessionId, long seq, Endpoint endpoint,
                     LocationId location, long version, String expressionRef,
                     String javaType, Referent referentState,
                     String referentStateRefused, boolean initial) {
        this.sessionId = sessionId;
        this.seq = seq;
        this.endpoint = endpoint;
        this.location = location;
        this.version = version;
        this.expressionRef = expressionRef;
        this.javaType = javaType;
        this.referentState = referentState;
        this.referentStateRefused = referentStateRefused;
        this.initial = initial;
    }

    public static WriteRow of(String sessionId, long seq, Endpoint endpoint,
                              LocationId location, long version,
                              String expressionRef, String javaType) {
        return of(sessionId, seq, endpoint, location, version, expressionRef,
                javaType, null, null);
    }

    /** A location's INITIAL version ({@link #initial}), placed where an
     *  access first observed it. */
    public static WriteRow initial(String sessionId, long seq,
                                   Endpoint endpoint, LocationId location,
                                   long version, String expressionRef,
                                   String javaType) {
        WriteRow row = of(sessionId, seq, endpoint, location, version,
                expressionRef, javaType);
        return new WriteRow(row.sessionId, row.seq, row.endpoint,
                row.location, row.version, row.expressionRef, row.javaType,
                null, null, true);
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
                Fields.text(javaType, "javaType"), referentState, refused,
                false);
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

    /**
     * Whether this is the location's INITIAL version: what it held before
     * every write its log names -- a constructor's or an initializer's
     * store from before the log began, the JVM default, a container's
     * members -- stated where an access first observed it.  No occurrence
     * wrote it: its endpoint only places that observation, and it is no
     * write of the endpoint's occurrence.
     */
    public boolean initial() {
        return initial;
    }

    @Override
    Object[] parts() {
        return new Object[] {sessionId, seq, endpoint, location, version,
                expressionRef, javaType, referentState, referentStateRefused,
                initial};
    }

    @Override
    public String toString() {
        return "WriteRow{" + sessionId + "#" + seq + " " + endpoint + " "
                + location + " v" + version + (initial ? " INITIAL" : "")
                + ":" + javaType
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

package edu.uva.liftlab.graphchecker.contract;

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
    private final int tie;

    private WriteRow(String sessionId, long seq, Endpoint endpoint,
                     LocationId location, long version, String expressionRef,
                     String javaType, Referent referentState,
                     String referentStateRefused, boolean initial, int tie) {
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
        this.tie = tie;
    }

    public static WriteRow of(String sessionId, long seq, Endpoint endpoint,
                              LocationId location, long version,
                              String expressionRef, String javaType) {
        return of(sessionId, seq, endpoint, location, version, expressionRef,
                javaType, null, null);
    }

    public static WriteRow initial(String sessionId, long seq,
                                   Endpoint endpoint, LocationId location,
                                   long version, String expressionRef,
                                   String javaType) {
        WriteRow row = of(sessionId, seq, endpoint, location, version,
                expressionRef, javaType);
        return new WriteRow(row.sessionId, row.seq, row.endpoint,
                row.location, row.version, row.expressionRef, row.javaType,
                null, null, true, 0);
    }

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
                false, 0);
    }

    public WriteRow withTie(int tie) {
        if (tie == this.tie) return this;
        return new WriteRow(sessionId, seq, endpoint, location, version,
                expressionRef, javaType, referentState, referentStateRefused,
                initial, (int) Fields.nonNegative(tie, "tie"));
    }

    public int tie() {
        return tie;
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

    public long version() {
        return version;
    }

    public String expressionRef() {
        return expressionRef;
    }

    public String javaType() {
        return javaType;
    }

    public Referent referentState() {
        return referentState;
    }

    public String referentStateRefused() {
        return referentStateRefused;
    }

    public boolean initial() {
        return initial;
    }

    @Override
    Object[] parts() {
        return new Object[] {sessionId, seq, endpoint, location, version,
                expressionRef, javaType, referentState, referentStateRefused,
                initial, tie};
    }

    @Override
    public String toString() {
        return "WriteRow{" + sessionId + "#" + seq + " " + endpoint + " "
                + location + " v" + version + (initial ? " INITIAL" : "")
                + ":" + javaType
                + (referentState == null ? "" : " -> " + referentState)
                + "}";
    }

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

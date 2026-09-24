package edu.uva.liftlab.graphchecker.contract;

import java.util.Objects;

/**
 * One message passing a transport door: which occurrence it left or entered.
 *
 * <p>A message carries its producer's endpoint id, and every occurrence that
 * serves it states that id as its {@code Anchor}.  What the anchor does not
 * state is where the message stood at each end: the occurrence whose door
 * SENT it and the occurrence whose door took it IN (DESIGN4 §1.2).  Those are
 * the served occurrence's control producers -- their fault points decide
 * whether the message, and everything served under it, exists at all -- so
 * each door states its occurrence here, keyed by the producer endpoint.</p>
 *
 * <p>A fact about a pairing, not an ordering one: nothing reads the order of
 * these rows.</p>
 */
public final class DoorRow {
    /** Which end of the message this door was. */
    public enum Kind {
        SEND,
        RECV
    }

    private final String sessionId;
    private final Kind kind;
    private final String endpoint;
    private final String occurrence;

    private DoorRow(String sessionId, Kind kind, String endpoint,
                    String occurrence) {
        this.sessionId = sessionId;
        this.kind = kind;
        this.endpoint = endpoint;
        this.occurrence = occurrence;
    }

    /**
     * @param endpoint   the producer endpoint id the message carries
     * @param occurrence the id of the occurrence the door stands in
     */
    public static DoorRow of(String sessionId, Kind kind, String endpoint,
                             String occurrence) {
        return new DoorRow(Fields.text(sessionId, "sessionId"),
                Fields.required(kind, "kind"),
                Fields.text(endpoint, "endpoint"),
                Fields.text(occurrence, "occurrence"));
    }

    public String sessionId() {
        return sessionId;
    }

    public Kind kind() {
        return kind;
    }

    /** The producer endpoint id of the message. */
    public String endpoint() {
        return endpoint;
    }

    /** The id of the occurrence the door stands in. */
    public String occurrence() {
        return occurrence;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof DoorRow)) return false;
        DoorRow other = (DoorRow) value;
        return kind == other.kind && sessionId.equals(other.sessionId)
                && endpoint.equals(other.endpoint)
                && occurrence.equals(other.occurrence);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sessionId, kind, endpoint, occurrence);
    }

    @Override
    public String toString() {
        return "DoorRow{" + sessionId + " " + kind + " " + endpoint + " @ "
                + occurrence + "}";
    }
}

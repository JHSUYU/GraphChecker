package edu.uva.liftlab.graphchecker.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 2: one refusal or one diagnostic, naming its subject.
 *
 * <p>{@code subject} is the thing the gap is about -- an endpoint id, a root, a
 * location, an address -- so that a refusal always names what it refused on
 * rather than reporting a category.</p>
 */
public final class GapRow {
    private final String sessionId;
    private final GapKind kind;
    private final GapClass cls;
    private final String subject;
    private final String detail;

    private GapRow(String sessionId, GapKind kind, GapClass cls, String subject,
                   String detail) {
        this.sessionId = sessionId;
        this.kind = kind;
        this.cls = cls;
        this.subject = subject;
        this.detail = detail;
    }

    public static GapRow of(String sessionId, GapKind kind, GapClass cls,
                            String subject, String detail) {
        return new GapRow(Fields.text(sessionId, "sessionId"),
                Fields.required(kind, "kind"), Fields.required(cls, "cls"),
                Fields.text(subject, "subject"),
                Fields.stated(detail, "detail"));
    }

    public String sessionId() {
        return sessionId;
    }

    public GapKind kind() {
        return kind;
    }

    public GapClass cls() {
        return cls;
    }

    /** What the gap is about, named. */
    public String subject() {
        return subject;
    }

    public String detail() {
        return detail;
    }

    /** Whether this gap stops a claim. */
    public boolean blocking() {
        return cls == GapClass.BLOCKING;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof GapRow)) return false;
        GapRow other = (GapRow) value;
        return kind == other.kind && cls == other.cls
                && sessionId.equals(other.sessionId)
                && subject.equals(other.subject)
                && detail.equals(other.detail);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sessionId, kind, cls, subject, detail);
    }

    @Override
    public String toString() {
        return "GapRow{" + sessionId + " " + kind + " " + cls + " " + subject
                + "}";
    }
}

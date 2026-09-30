package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §2.2: one refusal or diagnostic, always naming its
 * {@code subject} (endpoint id, root, location, address), never a category.
 */
public final class GapRow extends Value {
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
                Fields.required(detail, "detail"));
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

    public boolean blocking() {
        return cls == GapClass.BLOCKING;
    }

    @Override
    Object[] parts() {
        return new Object[] {sessionId, kind, cls, subject, detail};
    }

    @Override
    public String toString() {
        return "GapRow{" + sessionId + " " + kind + " " + cls + " " + subject
                + "}";
    }
}

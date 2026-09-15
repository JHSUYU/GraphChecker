package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.JsonFields;

import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;

/**
 * CONTRACT-SPEC 4: how far a root may move, absolutely.
 *
 * <p>Declared relative to the recorded value and resolved to absolute bounds by
 * the runtime ({@link RootMintRow}); a root with neither bound is pinned
 * everywhere -- in the composer and in the flip solver, which is the same rule
 * stated once.</p>
 *
 * <p>Both halves of that rule live here.  {@link #declared(Path)} is the ONE
 * reader of the case's {@code root-domains.jsonl} and {@link #resolved} is the
 * ONE join of that declaration with what a session minted: the composer and
 * the flip solver each had their own copy of both, and the copies disagreed
 * about the key to look a root up under, about what a malformed bound means,
 * and about whether a refused bound is {@code ""} or {@code null}.  A refused
 * bound is {@code null} -- a domain the case did not state is not a string --
 * and a root with neither bound does not move.</p>
 */
public final class RootDomain {
    private final String rootId;
    private final RootKind kind;
    private final String recordedValue;
    private final String min;
    private final String max;

    private RootDomain(String rootId, RootKind kind, String recordedValue,
                       String min, String max) {
        this.rootId = rootId;
        this.kind = kind;
        this.recordedValue = recordedValue;
        this.min = min;
        this.max = max;
    }

    public static RootDomain of(String rootId, RootKind kind,
                                String recordedValue, String min, String max) {
        return new RootDomain(Fields.text(rootId, "rootId"),
                Fields.required(kind, "kind"),
                Fields.stated(recordedValue, "recordedValue"),
                Fields.optional(min), Fields.optional(max));
    }

    /**
     * What the CASE declares each of its roots may be, by root id.
     *
     * <p>One JSONL row per root, in the one spelling the cases write:
     * {@code sourceId} with {@code declaredDomainMin} and
     * {@code declaredDomainMax}, each an absolute value or {@code +k}/{@code
     * -k} steps from what the recording read.  A case declares nothing else:
     * the KIND and the recorded value are the recording's own facts, read off
     * the mint row in {@link #resolved}, so a declaration row carries
     * {@link RootKind#INTEGRAL} and no recorded value because only an
     * integral root has a window to declare.</p>
     *
     * <p>A file that is not there declares nothing, which is not the same as
     * declaring that nothing moves: an undeclared root is pinned by
     * {@link #resolved} for want of bounds, and says so by name.</p>
     */
    public static Map<String, RootDomain> declared(Path file)
            throws IOException {
        Map<String, RootDomain> domains =
                new LinkedHashMap<String, RootDomain>();
        if (file == null || !Files.isRegularFile(file)) return domains;
        for (RootDomain domain
                : RowCodec.readAll(file, RootDomain::declaration)) {
            domains.put(domain.rootId(), domain);
        }
        return domains;
    }

    private static RootDomain declaration(JsonObject row) {
        return of(JsonFields.text(row, "sourceId"), RootKind.INTEGRAL, "",
                JsonFields.text(row, "declaredDomainMin"),
                JsonFields.text(row, "declaredDomainMax"));
    }

    /**
     * One minted root's domain, absolutely.
     *
     * <p>The case's declaration where there is one and the mint's own
     * resolved bounds otherwise -- never both, because a window stated twice
     * is two windows.  The kind and the recorded value are the mint's: what a
     * root WAS is the recording's fact, and only the case can say what else
     * it could have been.</p>
     */
    public static RootDomain resolved(RootMintRow row,
                                      Map<String, RootDomain> declared) {
        RootDomain stated = declared == null ? null
                : declared.get(row.rootId());
        String min = stated == null ? row.domainMin() : stated.min();
        String max = stated == null ? row.domainMax() : stated.max();
        return of(row.rootId(), row.kind(), row.recordedValue(),
                resolve(min, row.recordedValue()),
                resolve(max, row.recordedValue()));
    }

    /**
     * One declared bound as an absolute value, or {@code null}.
     *
     * <p>Two spellings, one notion: an absolute bound is the value itself,
     * and a bound written {@code +k} or {@code -k} is that many steps from
     * what the recording read -- the only way a case can state the domain of
     * a counter whose zero nobody chose.  A bound that is not an integral
     * literal, or a relative bound against a reading that is not one, states
     * no bound at all: {@code null}, and the root does not move on account of
     * it.</p>
     */
    public static String resolve(String bound, String recorded) {
        String stated = bound == null ? "" : bound.trim();
        if (stated.isEmpty()) return null;
        if (!stated.startsWith("+") && !stated.startsWith("-")) {
            return integral(stated) ? stated : null;
        }
        String offset = stated.startsWith("+")
                ? stated.substring(1) : stated;
        if (!integral(offset) || !integral(recorded)) return null;
        return new BigInteger(recorded.trim())
                .add(new BigInteger(offset.trim())).toString();
    }

    /** Whether one text is an integral literal: the one such test. */
    private static boolean integral(String value) {
        return !JavaPrimitiveSmtSemantics.integralLiteral(value).isEmpty();
    }

    public String rootId() {
        return rootId;
    }

    public RootKind kind() {
        return kind;
    }

    public String recordedValue() {
        return recordedValue;
    }

    /** The absolute lower bound, or {@code null}. */
    public String min() {
        return min;
    }

    /** The absolute upper bound, or {@code null}. */
    public String max() {
        return max;
    }

    /** A root with no declared domain does not move. */
    public boolean pinned() {
        return min == null && max == null;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof RootDomain)) return false;
        RootDomain other = (RootDomain) value;
        return kind == other.kind && rootId.equals(other.rootId)
                && recordedValue.equals(other.recordedValue)
                && Objects.equals(min, other.min)
                && Objects.equals(max, other.max);
    }

    @Override
    public int hashCode() {
        return Objects.hash(rootId, kind, recordedValue, min, max);
    }

    @Override
    public String toString() {
        return "RootDomain{" + rootId + " " + kind + " [" + min + ", " + max
                + "] recorded " + recordedValue + "}";
    }
}

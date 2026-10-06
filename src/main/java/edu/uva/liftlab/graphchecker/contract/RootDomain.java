package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.JsonFields;

import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * CONTRACT-SPEC §4: how far a root may move, as absolute bounds.  A root with
 * neither bound is pinned, in the composer and the flip solver alike.
 * {@link #declared(Path)} is the one reader of {@code root-domains.jsonl} and
 * {@link #resolved} the one join with a mint, so the two consumers cannot
 * disagree.  A refused bound is {@code null}, never {@code ""}.
 */
public final class RootDomain extends Value {
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
                Fields.required(recordedValue, "recordedValue"),
                Fields.optional(min), Fields.optional(max));
    }

    /**
     * The case's declared domains by root id: {@code sourceId},
     * {@code declaredDomainMin/Max} (absolute or {@code +k}/{@code -k}).
     * Kind and recorded value come from the mint in {@link #resolved}, so a
     * declaration carries INTEGRAL and no value.  No file declares nothing.
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
     * One minted root's absolute domain: the case's declaration if any, its
     * {@code +k}/{@code -k} read off the reading, else the mint's bounds,
     * which are absolute ({@code -2} is minus two), never both.  Kind and
     * recorded value are the mint's.
     */
    public static RootDomain resolved(RootMintRow row,
                                      Map<String, RootDomain> declared) {
        return resolved(row, declared,
                Collections.<BigInteger>emptyList());
    }

    /**
     * The same, for an integral configuration widened by {@code compared}:
     * each literal a recorded decision compared the root with, its {@code
     * c - 1, c, c + 1} joining the mint's hull and its reading (a comparison
     * with a value the slice does not state, a live replica count, is one
     * with the literal the run had: SYMBOL-SCOPE §4.3), the whole within
     * what the configuration's own validation admits ({@link
     * RootMintRow#valid}).  The case's declaration still wins.
     */
    public static RootDomain resolved(RootMintRow row,
                                      Map<String, RootDomain> declared,
                                      Collection<BigInteger> compared) {
        RootDomain mint = resolved(row, row.recordedValue(), declared);
        if (declared != null && declared.containsKey(row.rootId())
                || row.kind() != RootKind.INTEGRAL
                || row.category() != RootCategory.CONFIG) {
            return mint;
        }
        BigInteger low = mint.min == null ? null : new BigInteger(mint.min);
        BigInteger high = mint.max == null ? null : new BigInteger(mint.max);
        if (!compared.isEmpty() && integral(row.recordedValue())) {
            BigInteger reading = new BigInteger(row.recordedValue().trim());
            low = low == null ? reading : low.min(reading);
            high = high == null ? reading : high.max(reading);
            for (BigInteger literal : compared) {
                low = low.min(literal.subtract(BigInteger.ONE));
                high = high.max(literal.add(BigInteger.ONE));
            }
        }
        if (low == null || high == null) return mint;
        Validity valid = row.valid();
        low = valid.clip(low);
        high = valid.clip(high);
        return of(row.rootId(), row.kind(), row.recordedValue(),
                low.toString(), high.toString());
    }

    /**
     * The same, about a reading other than the mint's own: a clock cell the
     * composition anchors on the recording's timeline
     * ({@code Composer#clocks}).
     */
    public static RootDomain resolved(RootMintRow row, String reading,
                                      Map<String, RootDomain> declared) {
        RootDomain stated = declared == null ? null
                : declared.get(row.rootId());
        if (stated == null) {
            return of(row.rootId(), row.kind(), reading,
                    absolute(row.domainMin()), absolute(row.domainMax()));
        }
        return of(row.rootId(), row.kind(), reading,
                declaredBound(stated.min(), reading),
                declaredBound(stated.max(), reading));
    }

    /**
     * One declared bound as an absolute value: itself, or {@code +k}/{@code
     * -k} from the recorded reading -- the case file's syntax, read only
     * here.  {@code null} when either is not integral.
     */
    private static String declaredBound(String bound, String recorded) {
        String stated = bound == null ? "" : bound.trim();
        if (!stated.startsWith("+") && !stated.startsWith("-")) {
            return absolute(stated);
        }
        String offset = stated.startsWith("+")
                ? stated.substring(1) : stated;
        if (!integral(offset) || !integral(recorded)) return null;
        return new BigInteger(recorded.trim())
                .add(new BigInteger(offset.trim())).toString();
    }

    /** One absolute bound, or {@code null} when absent or not integral. */
    private static String absolute(String bound) {
        String stated = bound == null ? "" : bound.trim();
        return integral(stated) ? stated : null;
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
    Object[] parts() {
        return new Object[] {rootId, kind, recordedValue, min, max};
    }

    @Override
    public String toString() {
        return "RootDomain{" + rootId + " " + kind + " [" + min + ", " + max
                + "] recorded " + recordedValue + "}";
    }
}

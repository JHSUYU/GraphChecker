package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.JsonFields;

import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;

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

    public static RootDomain resolved(RootMintRow row,
                                      Map<String, RootDomain> declared,
                                      Collection<BigInteger> compared) {
        RootDomain mint = resolved(row, row.recordedValue(), declared);
        if (!widened(row, declared != null
                && declared.containsKey(row.rootId()))) {
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
        if (!integral(row.recordedValue()) || valid.admits(
                new BigInteger(row.recordedValue().trim()))) {
            low = valid.clip(low);
            high = valid.clip(high);
        }
        return of(row.rootId(), row.kind(), row.recordedValue(),
                low.toString(), high.toString());
    }

    public static boolean widened(RootMintRow row, boolean declared) {
        return !declared && row.kind() == RootKind.INTEGRAL
                && row.category() == RootCategory.CONFIG;
    }

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

    private static String absolute(String bound) {
        String stated = bound == null ? "" : bound.trim();
        return integral(stated) ? stated : null;
    }

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

    public String min() {
        return min;
    }

    public String max() {
        return max;
    }

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

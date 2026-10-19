package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.Validity;
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import edu.uva.liftlab.graphchecker.smt.ExpressionWalk;
import edu.uva.liftlab.graphchecker.smt.VmRows;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;
import static edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.locationId;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.runtime.RowPublication.literal;
import static edu.uva.liftlab.graphchecker.runtime.RowPublication.nestedRead;

final class RowPlaceholderMint {
    private RowPlaceholderMint() {
    }

    static void roots(ActiveRegion active,
                              OccurrenceAddress occurrence) {
        roots(active, occurrence, true);
    }

    static void mints(ActiveRegion active, OccurrenceAddress occurrence) {
        roots(active, occurrence, false);
    }

    private static void roots(ActiveRegion active,
                              OccurrenceAddress occurrence, boolean whole) {
        Map<String, List<String[]>> installed = whole
                ? mintedLocations(active)
                : Collections
                        .<String, List<String[]>>emptyMap();
        Map<String, Integer> consumed =
                new LinkedHashMap<String, Integer>();
        Set<String> stated = new LinkedHashSet<String>();
        for (JsonObject row : active.symbolizedRows) {
            String symbol = vmSymbol(row);
            if (symbol.isEmpty()) continue;
            stated.add(optionalString(row, "portId"));
            if (!minted(row)) continue;
            String sourceId = optionalString(row, "sourceId");
            RootKind kind = kindOf(row);
            boolean unattributed = sourceId.isEmpty()
                    && kind == RootKind.INTEGRAL;
            if (whole) {
                placeholder(occurrence, row, symbol,
                        nextStore(installed, consumed, symbol),
                        !unattributed);
            }
            if (unattributed) continue;
            String rootId = sourceId.isEmpty()
                    ? optionalString(row, "portId") : sourceId;
            String recorded = literal(optionalString(row, "recordedValue"));
            if (recorded.isEmpty()) {
                RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING,
                        firstNonBlank(rootId, symbol),
                        "this declared root's mint states no value"
                                + " it observed, so the root has no centre"
                                + " for its domain to resolve against:"
                                + " kind=" + kind + " symbol=" + symbol
                                + " field="
                                + optionalString(row, "fieldSignature"));
            }
            RowRuntime.rootMint(mintOccurrence(row, occurrence),
                    optionalLongInteger(row, "eventSeq", 0L), rootId, symbol,
                    kind, RootCategory.valueOf(optionalString(row,
                            "category")), recorded,
                    optionalString(row, "domainMin"),
                    optionalString(row, "domainMax"), Validity.read(row),
                    true,
                    kind == RootKind.CLOCK ? Clock.of(optionalLongInteger(row,
                            InputActionCatalog.DECLARED_WALL_CLOCK, 0L),
                            optionalString(row,
                                    InputActionCatalog.DECLARED_CLOCK_SOURCE))
                            : null,
                    optionalLongInteger(row, RootMintRow.CLOCK_SKEW, 0L));
        }
        if (!whole) return;
        for (SymbolizeAction action
                : active.activation.symbolize) {
            if (!action.declaredSymbolicRoot
                    || stated.contains(action.symbol)
                    || active.configurationReused(action.symbol)) {
                continue;
            }
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    action.symbol, "a declared region input was never"
                            + " symbolized in this activation: site="
                            + action.siteId + " cell=" + action.cell);
        }
    }

    private static OccurrenceAddress mintOccurrence(
            JsonObject row, OccurrenceAddress publishing) {
        String stated = optionalString(row, "mintOccurrence");
        if (stated.isEmpty()) return publishing;
        OccurrenceAddress owner = OccurrenceAddress.parse(stated);
        if (owner != null) return owner;
        RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                stated, "a mint stated an occurrence this row reader cannot "
                        + "parse, so it is published at the activation that "
                        + "held it: " + publishing.render());
        return publishing;
    }

    private static String[] nextStore(
            Map<String, List<String[]>> installed,
            Map<String, Integer> consumed, String symbol) {
        List<String[]> stores = installed.get(symbol);
        if (stores == null || stores.isEmpty()) return null;
        Integer seen = consumed.get(symbol);
        int index = seen == null ? 0 : seen.intValue();
        consumed.put(symbol, Integer.valueOf(index + 1));
        return stores.get(Math.min(index, stores.size() - 1));
    }

    private static void placeholder(OccurrenceAddress occurrence,
                                    JsonObject row, String symbol,
                                    String[] installedAt,
                                    boolean declaredRoot) {
        String locationKey = installedAt == null ? "" : installedAt[0];
        LocationId location = locationId(locationKey);
        long mintVersion = installedAt == null ? ReadRow.UNKNOWN_VERSION
                : Long.parseLong(installedAt[1]);
        long observed = location == null ? ReadRow.UNKNOWN_VERSION
                : Long.parseLong(installedAt[2]);
        if (location == null) {
            JsonObject read = nestedRead(row.get("expression"));
            locationKey = read == null ? ""
                    : SharedStateCapture.locationKeyOf(
                            object(read, "location"));
            location = locationId(locationKey);
            observed = location == null ? ReadRow.UNKNOWN_VERSION
                    : VmRows.joinedVersion(read);
        }
        if (location == null) {
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    symbol, "a declared region input states no VM location"
                            + " to read: neither the mint table nor the"
                            + " expression it read back names one, port="
                            + optionalString(row, "portId") + " field="
                            + optionalString(row, "fieldSignature"));
            return;
        }
        String stated = optionalString(row, "javaType");
        if (stated.isEmpty()) stated = symbolType(row.get("expression"));
        if (stated.isEmpty()) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    symbol, "a declared region input states no java type,"
                            + " so this read states no sort: port="
                            + optionalString(row, "portId"));
            return;
        }
        String declared = javaDescriptor(stated);
        String sort = mintedSort(symbol);
        if (!sort.isEmpty() && sort.charAt(0) != declared.charAt(0)) {
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    symbol, "a declared region input minted a " + sort
                            + "-sorted symbol for a " + declared + " cell ("
                            + optionalString(row, "fieldSignature")
                            + "), so this read states no one sort: "
                            + optionalString(row, "portId"));
            return;
        }
        String value = optionalString(row, "observedValue");
        if (value.isEmpty()) value = optionalString(row, "recordedValue");
        if (value.isEmpty() && declared.charAt(0) == 'L') {
            String identity = symbolLeaf(row.get("expression"));
            if (identity.startsWith("M_L'") || identity.startsWith("P_L'")
                    || "N".equals(identity)) {
                value = identity;
            }
        }
        if (declaredRoot) {
            if (mintVersion < 0L) {
                RowRuntime.gap(GapKind.DECLARATION_MISSING,
                        GapClass.DIAGNOSTIC, symbol,
                        "this declared root's mint states no version it"
                                + " installed, so no placeholder read can"
                                + " state one for it: port="
                                + optionalString(row, "portId"));
                return;
            }
            observed = mintVersion;
            value = "";
        }
        if (observed < 0L && literal(value).isEmpty()) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    symbol, "a declared region input states no value it"
                            + " read: " + optionalString(row, "portId"));
            return;
        }
        long event = optionalLongInteger(row, "eventSeq", 0L);
        String mintKey = mintVersion < 0L ? "symbol#" + nonNull(symbol)
                : locationKey + "#" + mintVersion;
        if (!RowRuntime.claimEvent("placeholder", mintKey)) {
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    symbol, "this session already states the mint "
                            + mintKey + ", so this row states no second"
                            + " value for it: "
                            + optionalString(row, "portId"));
            return;
        }
        RowRuntime.read(occurrence,
                mintVersion < 0L ? event : mintVersion,
                Endpoint.stateSite(locationKey, "PLACEHOLDER", 0, false),
                location, observed, symbol,
                declared, literal(value),
                optionalString(row, "siteIndex"), mintVersion);
    }

    private static String mintedSort(String symbol) {
        String name = nonNull(symbol);
        if (name.length() < 4 || name.charAt(1) != '_') return "";
        char sort = name.charAt(2);
        char after = name.charAt(3);
        if (after != '_' && after != '\'') return "";
        return "ZBCSIJFDL".indexOf(sort) < 0 ? "" : String.valueOf(sort);
    }

    static Map<String, String> mintStores(ActiveRegion active) {
        Map<String, String> stores = new LinkedHashMap<String,
                String>();
        for (Map.Entry<String, List<String[]>> minted
                : mintedLocations(active).entrySet()) {
            for (String[] store : minted.getValue()) {
                stores.put(store[0] + "#" + store[1], minted.getKey());
            }
        }
        return stores;
    }

    private static Map<String, List<String[]>> mintedLocations(
            ActiveRegion active) {
        Map<String, List<String[]>> bySymbol =
                new LinkedHashMap<String,
                        List<String[]>>();
        for (SharedStateCapture.Filed filed
                : active.sharedStateRecords.values()) {
            JsonObject record = filed.record;
            String locationKey = optionalString(record, "locationKey");
            if (locationId(locationKey) == null) continue;
            for (JsonElement element
                    : array(object(record, "envelope"), "versions")) {
                if (!element.isJsonObject()) continue;
                JsonObject version = element.getAsJsonObject();
                long id = optionalLongInteger(version, "fieldVersionId", -1L);
                JsonElement written = version.get("expression");
                if (id < 0L || written == null || !written.isJsonObject()) {
                    continue;
                }
                JsonObject node = written.getAsJsonObject();
                if (!optionalString(node, "_type").contains("Symbol")) {
                    continue;
                }
                String symbol = optionalString(node, "_exp");
                if (symbol.isEmpty() || !RowRuntime.isDeclaredMint(symbol)) {
                    continue;
                }
                long observed = -1L;
                for (JsonElement candidate
                        : array(object(record, "envelope"), "versions")) {
                    if (!candidate.isJsonObject()) continue;
                    JsonObject other = candidate.getAsJsonObject();
                    long otherId = optionalLongInteger(other,
                            "fieldVersionId", -1L);
                    JsonElement value = other.get("expression");
                    boolean symbolLeaf = value != null
                            && value.isJsonObject()
                            && optionalString(value.getAsJsonObject(),
                            "_type").contains("Symbol");
                    if (!symbolLeaf && otherId >= 0L && otherId < id
                            && otherId > observed) {
                        observed = otherId;
                    }
                }
                List<String[]> stores = bySymbol.get(symbol);
                if (stores == null) {
                    stores = new ArrayList<String[]>();
                    bySymbol.put(symbol, stores);
                }
                String versionId = Long.toString(id);
                boolean known = false;
                for (String[] held : stores) {
                    if (held[0].equals(locationKey)
                            && held[1].equals(versionId)) {
                        known = true;
                        break;
                    }
                }
                if (!known) {
                    stores.add(new String[]{locationKey, versionId,
                            Long.toString(observed)});
                }
            }
        }
        for (List<String[]> stores : bySymbol.values()) {
            stores.sort((left, right) -> Long.compare(
                    Long.parseLong(left[1]), Long.parseLong(right[1])));
        }
        return bySymbol;
    }

    private static String javaDescriptor(String javaType) {
        String type = nonNull(javaType);
        if (type.length() == 1) return type;
        if ("boolean".equals(type)) return "Z";
        if ("byte".equals(type)) return "B";
        if ("char".equals(type)) return "C";
        if ("short".equals(type)) return "S";
        if ("int".equals(type)) return "I";
        if ("long".equals(type)) return "J";
        if ("float".equals(type)) return "F";
        if ("double".equals(type)) return "D";
        return "L" + type.replace('.', '/') + ";";
    }

    static String vmSymbol(JsonObject row) {
        String raw = optionalString(row, "rawSymbol");
        if (!raw.isEmpty()) return raw;
        String leaf = symbolLeaf(row.get("expression"));
        return leaf.isEmpty() ? optionalString(row, "symbol") : leaf;
    }

    private static String symbolLeaf(JsonElement expression) {
        return firstSymbol(expression, "_exp");
    }

    private static String symbolType(JsonElement expression) {
        return firstSymbol(expression, "_java_type");
    }

    private static String firstSymbol(JsonElement expression,
                                      String member) {
        for (ExpressionWalk walk = ExpressionWalk.of(expression);
             walk.hasNext(); ) {
            JsonObject node = walk.next();
            if (!optionalString(node, "_type").contains("Symbol")) continue;
            String found = optionalString(node, member);
            if (!found.isEmpty()) return found;
            walk.prune();
        }
        return "";
    }

    private static boolean minted(JsonObject row) {
        return !optionalBool(row, "reused", false);
    }

    private static RootKind kindOf(JsonObject row) {
        if (optionalLongInteger(row, InputActionCatalog.DECLARED_WALL_CLOCK,
                0L) > 0L) {
            return RootKind.CLOCK;
        }
        String stated = optionalString(row, "javaType");
        String javaType = stated.isEmpty()
                ? symbolType(row.get("expression")) : stated;
        return "Z".equals(javaType) || "boolean".equals(javaType)
                ? RootKind.MARKER : RootKind.INTEGRAL;
    }
}

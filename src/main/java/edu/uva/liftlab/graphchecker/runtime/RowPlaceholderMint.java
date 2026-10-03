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
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import edu.uva.liftlab.graphchecker.smt.ExpressionWalk;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.locationId;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
// One reader per VM value spelling, shared with RowPublication.
import static edu.uva.liftlab.graphchecker.runtime.RowPublication.literal;
import static edu.uva.liftlab.graphchecker.runtime.RowPublication.nestedRead;
import static edu.uva.liftlab.graphchecker.runtime.RowPublication.versionOf;

/**
 * The mints of one activation: which are roots, and which are the read
 * placeholders a declared region input stands for.  The "what did this
 * activation MINT" half of {@link RowPublication}, the one entry point.
 *
 * <p>Every mint's store is suppressed ({@link #mintStores}), so every mint
 * publishes a placeholder read stating the version; a declared root also
 * publishes a root row stating kind, domain and reading.</p>
 */
final class RowPlaceholderMint {
    private RowPlaceholderMint() {
    }

    /**
     * The roots this activation minted, and the placeholders it did not.
     *
     * <p>An UNATTRIBUTED region input is a READ PLACEHOLDER, not a root:
     * the composer pins every domain-less root to its recorded value, so a
     * placeholder published as a root makes every moved valuation
     * unsatisfiable.</p>
     *
     * <p>A declared root publishes BOTH rows; without the placeholder every
     * read of its suppressed store is unbound.  ONE ROOT PER SYMBOL: a
     * {@code reused} row minted nothing ({@link #minted}), and a root row
     * for it would name another mint's symbol.</p>
     */
    static void roots(ActiveRegion active,
                              OccurrenceAddress occurrence) {
        roots(active, occurrence, true);
    }

    /**
     * THE MINTS ALONE, for an activation the run abandons: it publishes no
     * decisions, writes or anchor, but its declared roots' symbols already
     * appear in other activations' rows, so their root rows must be
     * published or the composer cannot guard those arms.  No placeholders:
     * an abandoned activation's reads are not published.
     */
    static void mints(ActiveRegion active, OccurrenceAddress occurrence) {
        roots(active, occurrence, false);
    }

    private static void roots(ActiveRegion active,
                              OccurrenceAddress occurrence, boolean whole) {
        Map<String, List<String[]>> installed = whole
                ? mintedLocations(active)
                : Collections
                        .<String, List<String[]>>emptyMap();
        // ONE PLACEHOLDER PER MINT STORE, IN ORDER: a symbol minted twice
        // in one activation has two suppressed stores, and pairing both rows
        // with the first store leaves the second unstated.
        Map<String, Integer> consumed =
                new LinkedHashMap<String, Integer>();
        Set<String> stated = new LinkedHashSet<String>();
        for (JsonObject row : active.symbolizedRows) {
            String symbol = vmSymbol(row);
            if (symbol.isEmpty()) continue;
            stated.add(optionalString(row, "portId"));
            // A reused symbol is symbolic but minted nothing: no second root
            // (its row would carry another mint's symbol under this reading).
            if (!minted(row)) continue;
            String sourceId = optionalString(row, "sourceId");
            // Kind from the declaration (#kindOf); a configured source
            // carries its type on the symbol only.
            RootKind kind = kindOf(row);
            // EVERY MINT OWES THE PLACEHOLDER READ THAT STATES IT: its store
            // is suppressed (#mintStores), and this is the only row carrying
            // a `mintVersion`.  A declared root publishes it in addition to
            // the RootMintRow; without it every read of the clock is unbound.
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
            // A declared root row states what its mint observed; a blank is
            // a value #recordedScalar cannot spell (e.g. a reference root).
            // The row is still published as evidence the mint ran, and the
            // composer's invariant 8 withholds the claim.
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
                    optionalString(row, "domainMax"), true,
                    kind == RootKind.CLOCK ? Clock.of(optionalLongInteger(row,
                            InputActionCatalog.DECLARED_WALL_CLOCK, 0L),
                            optionalString(row,
                                    InputActionCatalog.DECLARED_CLOCK_SOURCE))
                            : null,
                    optionalLongInteger(row, RootMintRow.CLOCK_SKEW, 0L));
        }
        if (!whole) return;
        // Every declared region input this activation never symbolized:
        // otherwise a declaration the replay silently missed reads
        // downstream as "this branch is concrete".  A configuration read
        // that took its key's first read's box is symbolic, stated there.
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

    /**
     * The occurrence a ROOT MINT row is addressed at: the activation of the
     * region whose plan OWNS the mint, as stated when it ran ({@code
     * ActiveRegion#mintOccurrence}).  Not the publishing activation:
     * regions nest, and the innermost one is not the owner.
     *
     * <p>An unstated occurrence publishes at the publishing activation; an
     * unparseable one is NAMED, since only the runtime wrote it.</p>
     */
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

    /**
     * The store the NEXT mint row of {@code symbol} is of: the k-th row is
     * of the k-th store.  A row past the last store answers to the last
     * one, and {@link #placeholder}'s duplicate guard names it if it is a
     * real duplicate.
     */
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

    /**
     * One declared region input, as the read it stands for: the placeholder
     * symbol, the VM location it was installed on, and the value it held.
     *
     * <p>For a {@code declaredRoot} the RootMintRow is the one statement of
     * the value: this row states only the installed version, since a value
     * or an earlier writer would PIN a movable root.</p>
     */
    private static void placeholder(OccurrenceAddress occurrence,
                                    JsonObject row, String symbol,
                                    String[] installedAt,
                                    boolean declaredRoot) {
        // The VM's own location (owner rid, slot offset), found by the
        // symbol the VM stated for the mint -- never a Java field signature
        // or a symbol-name suffix guess, which name locations no write has.
        String locationKey = installedAt == null ? "" : installedAt[0];
        LocationId location = locationId(locationKey);
        // The version this read OBSERVED is the last REAL write before the
        // mint (the mint's own version is no write, see #mintStores); that
        // makes this row a join to the writer.  None: -1, pin the decimal.
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
                    : versionOf(read);
        }
        if (location == null) {
            // Only the VM may name the location: the mint table, else the
            // expression read back.  No third source.
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    symbol, "a declared region input states no VM location"
                            + " to read: neither the mint table nor the"
                            + " expression it read back names one, port="
                            + optionalString(row, "portId") + " field="
                            + optionalString(row, "fieldSignature"));
            return;
        }
        // The declaration's type, read exactly as #kindOf reads it: the
        // row's own, else the type the VM spelled into the symbol this mint
        // installed.
        String stated = optionalString(row, "javaType");
        if (stated.isEmpty()) stated = symbolType(row.get("expression"));
        if (stated.isEmpty()) {
            // No default type: it drives the sort check below.
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    symbol, "a declared region input states no java type,"
                            + " so this read states no sort: port="
                            + optionalString(row, "portId"));
            return;
        }
        String declared = javaDescriptor(stated);
        String sort = mintedSort(symbol);
        if (!sort.isEmpty() && sort.charAt(0) != declared.charAt(0)) {
            // The mint symbolized the OBJECT, not the cell: one name with
            // two sorts, which no lowering can hold.
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
            // A reference cell records no decimal: state the VM's identity
            // spelling on the leaf (as FieldAccess.concreteValue does), or
            // "N" for null.
            String identity = symbolLeaf(row.get("expression"));
            if (identity.startsWith("M_L'") || identity.startsWith("P_L'")
                    || "N".equals(identity)) {
                value = identity;
            }
        }
        if (declaredRoot) {
            // A MINT THAT IS ALSO A ROOT STATES ITS VALUE ONCE, ON THE ROOT
            // ROW (see Composer#placeholder).  A value here, or a join to the
            // last real write, is a PIN, and a pinned clock makes CLOCK_SKEW
            // unreachable.  So this row observes the mint's own version --
            // for a woven clock mint the only version the cell ever had.
            // No version: named, since invariant 7 makes a versionless
            // placeholder BLOCKING.
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
        // ONE ROW PER MINT, keyed by its own store (location, version) --
        // the key #mintStores suppresses by and the composer resolves
        // ReadFrom@(L, v) by.  The occurrence is no identity: two thread
        // activations can share one OccurrenceAddress.  A mint with no
        // version answers to its symbol (already an invariant-7 failure).
        long event = optionalLongInteger(row, "eventSeq", 0L);
        String mintKey = mintVersion < 0L ? "symbol#" + safe(symbol)
                : locationKey + "#" + mintVersion;
        if (!RowRuntime.claimEvent("placeholder", mintKey)) {
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    symbol, "this session already states the mint "
                            + mintKey + ", so this row states no second"
                            + " value for it: "
                            + optionalString(row, "portId"));
            return;
        }
        // The row's seq is the mint's version: versions and read events
        // share one monotone session counter (VM §2), while the
        // per-activation eventSeq collides for field inputs.
        RowRuntime.read(occurrence,
                mintVersion < 0L ? event : mintVersion,
                Endpoint.stateSite(locationKey, "PLACEHOLDER", 0, false),
                location, observed, symbol,
                declared, literal(value),
                optionalString(row, "siteIndex"), mintVersion);
    }

    /**
     * The sort the VM spelled into one of its symbols ({@code M_I_field_...},
     * {@code P_L'...'_}), or {@code ""}.  Only the SORT must agree with the
     * cell: a reference symbol does not spell its class.  A runtime-made
     * symbol spells no sort and claims none.
     */
    private static String mintedSort(String symbol) {
        String name = safe(symbol);
        if (name.length() < 4 || name.charAt(1) != '_') return "";
        char sort = name.charAt(2);
        char after = name.charAt(3);
        if (after != '_' && after != '\'') return "";
        return "ZBCSIJFDL".indexOf(sort) < 0 ? "" : String.valueOf(sort);
    }

    /**
     * Every mint store of this activation, keyed {@code location#version}:
     * a version whose whole value is a declared mint's symbol is that
     * mint's shadow store, and nobody wrote it: {@link #mintedLocations},
     * keyed by store instead of symbol.
     */
    static Map<String, String> mintStores(ActiveRegion active) {
        // EVERY such version, not the first per symbol: a second store
        // would otherwise be published as a write.
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

    /**
     * Where the VM says each minted symbol lives: symbol -&gt; its stores
     * {location key, version, last earlier real write}, in version order.
     * Only a version whose expression IS the symbol counts; one computed
     * FROM it is a different value.
     */
    private static Map<String, List<String[]>> mintedLocations(
            ActiveRegion active) {
        Map<String, List<String[]>> bySymbol =
                new LinkedHashMap<String,
                        List<String[]>>();
        for (JsonObject record : active.sharedStateRecords.values()) {
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
                // Only a write EARLIER than the mint is the one the read
                // observed; a later store is a value this read never saw.
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
        // Ordered by version id, the order the mint rows are walked in.
        for (List<String[]> stores : bySymbol.values()) {
            stores.sort((left, right) -> Long.compare(
                    Long.parseLong(left[1]), Long.parseLong(right[1])));
        }
        return bySymbol;
    }

    /**
     * A source type name as the JVM descriptor a row states.  Callers refuse
     * an unstated type first, because the descriptor drives the sort.
     */
    private static String javaDescriptor(String javaType) {
        String type = safe(javaType);
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

    /**
     * The one spelling of a symbol: the VM's name, since the composer binds
     * a root by finding that name in the lowered terms.
     */
    static String vmSymbol(JsonObject row) {
        String raw = optionalString(row, "rawSymbol");
        if (!raw.isEmpty()) return raw;
        // A configured source mints through the VM's own label and states
        // no raw symbol of its own; the expression it published names it.
        String leaf = symbolLeaf(row.get("expression"));
        return leaf.isEmpty() ? optionalString(row, "symbol") : leaf;
    }

    /** The first symbol leaf an expression states, or {@code ""}. */
    private static String symbolLeaf(JsonElement expression) {
        return firstSymbol(expression, "_exp");
    }

    /** The type of the first symbol leaf an expression states. */
    private static String symbolType(JsonElement expression) {
        return firstSymbol(expression, "_java_type");
    }

    /**
     * One member of the first symbol leaf that states it, each node once
     * ({@link ExpressionWalk}; cut at depth 8, a deeper one was a gap and
     * no symbol).  A symbol leaf is not walked into.
     */
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

    /**
     * Whether this row MINTED the symbol it names.  A declared read of a
     * field already holding an expression keeps it ({@code
     * SymInstance::has_sym_exp}) and the row says {@code reused}; such a
     * row may not be a root, since {@link #vmSymbol} would name another
     * mint's symbol.
     */
    private static boolean minted(JsonObject row) {
        return !optionalBool(row, "reused", false);
    }

    /**
     * What kind of root one mint row states: declared clock, boolean
     * marker, else integral.  Read from the declaration, never guessed from
     * the value, because it decides how the composer may move the root.
     */
    private static RootKind kindOf(JsonObject row) {
        if (optionalLongInteger(row, InputActionCatalog.DECLARED_WALL_CLOCK,
                0L) > 0L) {
            return RootKind.CLOCK;
        }
        // A configured source states its type only on its symbol; without
        // this a boolean configured root reads INTEGRAL.
        String stated = optionalString(row, "javaType");
        String javaType = stated.isEmpty()
                ? symbolType(row.get("expression")) : stated;
        return "Z".equals(javaType) || "boolean".equals(javaType)
                ? RootKind.MARKER : RootKind.INTEGRAL;
    }
}

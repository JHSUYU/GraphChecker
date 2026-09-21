package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.locationId;
// The readers of the VM's own value spellings stay with the entry point:
// one reader per spelling, shared by the two halves of the publication.
import static edu.uva.liftlab.graphchecker.runtime.RowPublication.cut;
import static edu.uva.liftlab.graphchecker.runtime.RowPublication.literal;
import static edu.uva.liftlab.graphchecker.runtime.RowPublication.nestedRead;
import static edu.uva.liftlab.graphchecker.runtime.RowPublication.versionOf;

/**
 * The mints of one activation: which are roots, and which are the read
 * placeholders a declared region input stands for.
 *
 * <p>Split out of {@link RowPublication}, which stays the one entry point:
 * this is the half that answers "what did this activation MINT", against
 * the mint table the VM's write log states, and it shares with the other
 * half only the readers of the VM's own value spellings.</p>
 *
 * <p>A DECLARED root is a marker, a clock or a configured source: the case
 * names it and the search may move it.  A region's declared input is not a
 * root at all -- it is a READ PLACEHOLDER, the symbol standing for what
 * that read returned -- and publishing it as a root is what pins it.</p>
 */
final class RowPlaceholderMint {
    private RowPlaceholderMint() {
    }

    /**
     * The roots this activation minted, and the placeholders it did not.
     *
     * <p>A DECLARED root is a marker, a clock or a configured source: the
     * case names it and the search may move it.  A region's declared input
     * is not a root at all -- it is a READ PLACEHOLDER, the symbol standing
     * for what that read returned -- and publishing it as a root is what
     * pins it: the composer pins every domain-less root to its recorded
     * value, and a placeholder that is pinned AND joined to its writer's
     * expression makes every moved valuation unsatisfiable.</p>
     *
     * <p>ONE ROOT PER SYMBOL, and it is the mint that MADE the symbol.  A
     * declared read whose field already carried a propagated expression
     * REUSES it -- {@code SymInstance::has_sym_exp} makes the mint a no-op
     * and both runtime row shapes say {@code reused} -- so it minted no
     * symbol of its own, and the only name {@link #vmSymbol} can give it is
     * the first symbol leaf of the expression it read back, which is
     * ANOTHER mint's symbol.  A root row over that name states one solver
     * name for two quantities, and its {@code recordedValue} is the OTHER
     * quantity's reading, which is what the composer pins the symbol to.
     * </p>
     */
    static void roots(ActiveRegion active,
                              OccurrenceAddress occurrence) {
        roots(active, occurrence, true);
    }

    /**
     * THE MINTS ALONE, for an activation that will state nothing else.
     *
     * <p>An activation the run ABANDONS -- one that did not take the
     * decision its obligation flips -- publishes no decisions, no writes
     * and no anchor, because none of those is a fact about a path anyone
     * asked for.  Its MINTS are a different kind of fact: the mint already
     * symbolized the cell, the symbol is in the VM, and every row the
     * session's other activations publish carries it.  Withholding the row
     * too is what left hdfs-11741 campaign #4 with seven sessions whose
     * expressions name a declared root they publish no RootMintRow for --
     * e635d55d and ed4ab35c with ten each, HDFS.BLOCK_KEY.SERIAL_NO among
     * them -- and an arm the composer could not guard.</p>
     *
     * <p>Only the DECLARED ROOTS: a placeholder is the read a declared
     * region input stands for, and an abandoned activation's reads are not
     * published either.  Its {@code installed} table is read out of the
     * write log, which this activation never read out.</p>
     */
    static void mints(ActiveRegion active, OccurrenceAddress occurrence) {
        roots(active, occurrence, false);
    }

    private static void roots(ActiveRegion active,
                              OccurrenceAddress occurrence, boolean whole) {
        Map<String, String[]> installed = whole
                ? mintedLocations(active)
                : java.util.Collections.<String, String[]>emptyMap();
        Set<String> stated = new LinkedHashSet<String>();
        for (JsonObject row : active.symbolizedRows) {
            String symbol = vmSymbol(row);
            if (symbol.isEmpty()) continue;
            stated.add(optionalString(row, "portId"));
            // The declaration was reached and it IS symbolic -- its value is
            // a term over the symbol it reused -- so there is nothing to
            // refuse and nothing to name: what there is not is a second
            // root.  On 11741's nn0 updateKeys the three expiry hooks read
            // back timer.now() + k*keyUpdateInterval + tokenLifetime over
            // the declared clock cell of that region, and each published a
            // RootMintRow carrying the CLOCK's symbol, the EXPIRY's value
            // and its own source id: six BLOCKING "one solver name for 2
            // roots" refusals out of COMPOSE, and, had the composer got past
            // them, the clock of every rotation pinned to an instant no
            // clock read.  The second rotation's HDFS.BLOCK_KEY.SERIAL_NO is
            // the same row without the collision -- same symbol, same source
            // id, serial+1 as its reading -- so it silently moved the
            // serial root's recorded value one rotation on.
            if (!minted(row)) continue;
            String sourceId = optionalString(row, "sourceId");
            // The kind is read off the declaration, once
            // (see #kindOf): a configured source states no javaType of its
            // own and carries it on the symbol it minted, which is why a
            // declared boolean root read INTEGRAL while the composer looked
            // for a range with two values in it.
            RootKind kind = kindOf(row);
            if (sourceId.isEmpty() && kind == RootKind.INTEGRAL) {
                if (whole) placeholder(occurrence, row, symbol, installed);
                continue;
            }
            String rootId = sourceId.isEmpty()
                    ? optionalString(row, "portId") : sourceId;
            String recorded = literal(optionalString(row, "recordedValue"));
            // A DECLARED ROOT ROW STATES WHAT ITS MINT OBSERVED, and when
            // the run cannot spell that value it SAYS SO here rather than
            // publishing an empty field.  Every mint hands the live read
            // now (RootMint#fieldMintRecordedValue and its two siblings),
            // so a blank left here is a value ConcolicRegionRuntime
            // #recordedScalar has no scalar spelling for -- a reference
            // cell declared as a root -- and not a plant.  The row is
            // still published: it is the evidence that this mint ran, and
            // the composer's own refusal (invariant 8, "a MARKER reading
            // is spelled true or false") is what withholds the claim.
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
                    kind, recorded,
                    optionalString(row, "domainMin"),
                    optionalString(row, "domainMax"), true);
        }
        if (!whole) return;
        // Every declared region input this activation never symbolized.  A
        // declaration the replay silently does not reach is the one failure
        // mode that reads downstream as "this branch is concrete":
        // hdfs-17960's empty phi was exactly that, a declared read that
        // neither minted nor refused.  The row names the port so the absence
        // is answerable from the session rather than from a replay trace.
        for (SymbolizeAction action
                : active.activation.symbolize) {
            if (!action.declaredSymbolicRoot
                    || stated.contains(action.symbol)) {
                continue;
            }
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    action.symbol, "a declared region input was never"
                            + " symbolized in this activation: site="
                            + action.siteId + " cell=" + action.cell);
        }
    }

    /**
     * The occurrence a ROOT MINT row is addressed at.
     *
     * <p>The activation of the region whose plan OWNS the mint, which the
     * mint stated when it ran ({@code ActiveRegion
     * #mintOccurrence}) because that is where the region stack was live.
     * The publishing activation is not the answer: regions nest, and a mint
     * site inside a method two regions both hold runs under whichever
     * activation happened to be innermost, so the seed and a replay
     * addressed one mint at two occurrences and the focus row's rootMints
     * matched neither.</p>
     *
     * <p>A row the mint could not address states {@code ""} and is
     * published where it was published, which is the same rule the
     * declaring-region walk itself ends on.  A stamp this reader cannot
     * parse is NAMED: it is a spelling the runtime wrote and nothing else
     * could, so reading past it would hide a bug in one of the two.</p>
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
     * One declared region input, as the read it stands for.
     *
     * <p>The symbol is the placeholder the mint installed; the location is
     * the field it was installed on; the value is what the field held when
     * it was.  A reader joins it to the write of that location exactly as
     * it joins any other read.</p>
     */
    private static void placeholder(OccurrenceAddress occurrence,
                                    JsonObject row, String symbol,
                                    Map<String, String[]> installed) {
        // A declared mint, session-wide, so no activation's write log offers
        // the mint's own version as a write of that location.  The register
        // is already filled -- at the mint, by ActiveRegion -- and this is
        // the backstop for a mint row that reached publication by some other
        // road than the two recorders.
        RowRuntime.declaredMintSymbol(symbol);
        // The location is the VM's own -- owner rid, slot offset -- so this
        // read and every write of the same storage spell one location.
        // Naming the Java field signature instead left the read saying
        // AtomicInteger#value while the write log said
        // INSTANCE_FIELD/<rid>#<offset>.
        // The mint this row is of, found by the symbol the VM stated for it.
        // The suffix guess that used to stand behind this -- any installed
        // symbol whose name ENDS WITH `_field_<requested>` -- named a mint
        // by a spelling convention rather than by the VM's answer, so a
        // second mint of a port whose request string is a suffix of another
        // answered for it.  A mint the VM's own symbol does not find is
        // refused below.
        String[] installedAt = installed.get(symbol);
        String locationKey = installedAt == null ? "" : installedAt[0];
        LocationId location = locationId(locationKey);
        // The version this read OBSERVED.  The mint's own version is not a
        // write -- nobody stored it, and no WriteRow states it (see
        // #mintStores) -- so the version the read observed is the last
        // REAL write of the location before it, which the VM's version log
        // already holds.  That is what makes this row a JOIN to the writer
        // occurrence: on hdfs-17960 the two deletion occurrences write the
        // counter and the anchor reads what they left.  When no write
        // precedes the mint the row states -1 and pins the plain decimal,
        // which is the never-neither rule and not an invented version.
        long observed = location == null ? ReadRow.UNKNOWN_VERSION
                : Long.parseLong(installedAt[2]);
        if (location == null) {
            JsonObject read = nestedRead(row.get("expression"), 0);
            locationKey = read == null ? ""
                    : SharedStateCapture.locationKeyOf(
                            object(read, "location"));
            location = locationId(locationKey);
            observed = location == null ? ReadRow.UNKNOWN_VERSION
                    : versionOf(read);
        }
        if (location == null) {
            // Both strengths are the VM's own statement: the location the
            // mint installed into, else the location the expression this
            // read returned says it read.  There is no third: building the
            // LocationId out of the Java field signature named a location
            // the VM never stated -- `INSTANCE/<declaring class>#<field>`
            // against a write log that spells `INSTANCE_FIELD/<rid>#<slot>`
            // -- so the read joined no write of the same storage and the
            // composer joined reads on a location nothing wrote.  This
            // covers every declared region input, of any sort, whose mint
            // the VM numbered no location for.
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
        if (stated.isEmpty()) stated = symbolType(row.get("expression"), 0);
        if (stated.isEmpty()) {
            // The declaration's own type, and nothing standing in for it:
            // the descriptor drives the sort check below, so defaulting an
            // unstated type to Ljava/lang/Object; declared every such read
            // a reference and then compared that against the VM symbol's
            // real sort.  A row that cannot state its sort states none.
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    symbol, "a declared region input states no java type,"
                            + " so this read states no sort: port="
                            + optionalString(row, "portId"));
            return;
        }
        String declared = javaDescriptor(stated);
        String sort = mintedSort(symbol);
        if (!sort.isEmpty() && sort.charAt(0) != declared.charAt(0)) {
            // The mint symbolized the OBJECT, not the cell: on hdfs-17960
            // REGION.9492ec77 declares <Snapshot: int id> and the row came
            // back with the VM's reference symbol P_L'...Snapshot'_ beside
            // javaType I, so one row stated an int read and a reference
            // unknown.  A reader that declares the symbol by the row's type
            // and resolves it by the table's gets two sorts for one name,
            // which no lowering can hold; the run states the disagreement
            // instead of a row that hides it.
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
            // A reference cell records no decimal.  What the run states of
            // it is the identity the VM spells on the leaf -- the same
            // spelling FieldAccess.concreteValue carries, so one identity
            // lowering serves both -- and "N" for null.
            String identity = symbolLeaf(row.get("expression"), 0);
            if (identity.startsWith("M_L'") || identity.startsWith("P_L'")
                    || "N".equals(identity)) {
                value = identity;
            }
        }
        if (observed < 0L && literal(value).isEmpty()) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    symbol, "a declared region input states no value it"
                            + " read: " + optionalString(row, "portId"));
            return;
        }
        // ONE ROW PER MINT, and a mint's identity in a session is the
        // version it installed: the VM's version counter hands out one
        // number per store, so two mints can never share it and one mint
        // can never have two.  Nothing coarser will do.  The occurrence is
        // not an identity here -- the anchor region's two FSImageSaver
        // activations share one OccurrenceAddress (the thread-start frame
        // carries no loop iteration, P2h), each mints the declared counter
        // once, and keying on (occurrence, location, read-event ordinal)
        // called the second activation's mint a duplicate of the first:
        // its version was then stated by no row at all and every read that
        // observed it lost its join (17960 corpus 4404a4af: v138 stated,
        // v149 not, `ADMISSION_GAP: 2 paths reached the anchor and all were
        // refused: INSTANCE/1#24@149`).  Two ports of one activation are
        // two mints for the same reason.  A second row for the SAME
        // mintVersion is the one real duplicate, and it is named.
        long event = optionalLongInteger(row, "eventSeq", 0L);
        long mintVersion = installedAt == null ? ReadRow.UNKNOWN_VERSION
                : Long.parseLong(installedAt[1]);
        // The key is the mint's own store: (location, version), which is
        // exactly the key #mintStores and #mintedLocations already suppress
        // and state it by, so the row, the suppression and the composer's
        // ReadFrom@(L, v) resolution all name one thing.  Version alone
        // would do in a real session -- the VM hands out one version per
        // store from the session counter it shares with read events -- and
        // the location only refines it, never merges two mints of one
        // location, which is the case this key exists for.
        // A mint the VM stated no version for has no store to name, so it
        // answers to the symbol it installed -- its only other name.  Such
        // a row is already a stated failure downstream (contract v2.4
        // invariant 7: a placeholder states the version it mints), so
        // nothing is hidden by keying it.
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
        // WHERE IN THE RUN this row sits is the VM event that created the
        // mint: version ids and read event ids are handed out by one monotone
        // session counter (REPORT-P2EF), so the mint's version IS its event
        // id.  The runtime's per-activation eventSeq is not: a declared field
        // input states none at all, so every placeholder of one activation
        // fell back to "no earlier than the last event seen" and two mints of
        // one location went out at one seq -- which is one row per event
        // stating two events (invariant 4 BLOCKING on laneA9: `reads.jsonl
        // seq=171 field=seq/location INSTANCE 1.24`, mints v138 and v149).
        // A mint the VM numbered nothing keeps the activation's reading; such
        // a row is already a stated failure (invariant 7).
        RowRuntime.read(occurrence,
                mintVersion < 0L ? event : mintVersion,
                Endpoint.stateSite(locationKey, "PLACEHOLDER", 0, false),
                location, observed, symbol,
                declared, literal(value),
                optionalString(row, "siteIndex"), mintVersion);
    }

    /**
     * The sort the VM spelled into one of its symbols, or {@code ""}.
     *
     * <p>A VM symbol carries its own sort: {@code M_I_field_...},
     * {@code M_Z_field_...}, {@code M_L_field_...}, {@code P_L'...'_}.  The
     * SORT is what has to agree with the cell -- L against any reference
     * descriptor, I against I -- because a reference symbol does not spell
     * which class the cell is declared as, and demanding the whole
     * descriptor refused every reference mint (P2l).  A symbol the runtime
     * made instead ({@code INSTANCE_FIELD/2#24@v178}) spells no sort and
     * claims none, so nothing is inferred from its absence.</p>
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
     * Whether one symbol is a mint of THIS activation's declared inputs.
     *
     * <p>A version whose whole value is a bare symbol is not by itself a
     * mint: the VM writes a named reference's identity the same way
     * ({@code M_L'org/apache/...FsImage...'}), and a field assigned a
     * symbolized object carries that object's symbol.  Treating every such
     * version as a mint suppressed four real writes of hdfs-17960 --
     * INSTANCE/39#96@226, 35#64@233, 43#96@251, 37#64@263 -- and the reads
     * that observed them lost their writer, which took the anchor's
     * admitted paths from 2 to 0.  A mint is a symbol a DECLARED INPUT of
     * this activation asked for: the VM answers a request for
     * {@code field_<portId>} with {@code M_<sort>_field_<portId>}, and a row
     * that knows its own {@code rawSymbol} states it outright.  The key the
     * suppression and {@code mintVersion} share is still (location,
     * version); this is only which versions are mints at all.</p>
     *
     * <p>And it is a question about the SESSION, not about this activation:
     * the mint files its symbol where it runs
     * ({@code RowRuntime#declaredMintSymbol}), so an activation that merely
     * read the same VM record out gets the same answer as the one that
     * minted, whichever of them publishes first.  Asked of {@code active}
     * alone, hdfs-11741 campaign #5b published 284 clock mint stores as
     * WriteRows of a second activation and bound 593 of 877 reads by
     * accident.</p>
     */
    private static boolean declaredMint(ActiveRegion active, String symbol) {
        for (JsonObject row : active.symbolizedRows) {
            if (symbol.equals(optionalString(row, "rawSymbol"))) return true;
            String requested = optionalString(row, "symbol");
            if (!requested.isEmpty()
                    && symbol.endsWith("_field_" + requested)) {
                return true;
            }
        }
        return RowRuntime.isDeclaredMintSymbol(symbol);
    }

    /**
     * Every mint store of this activation, keyed {@code location#version}.
     *
     * <p>The same scan {@link #mintedLocations} performs, keyed the other
     * way round: there by the symbol a placeholder row is found by, here by
     * the store a WriteRow would have been published for.  One rule decides
     * both -- a version whose whole value is the symbol a declared input
     * minted is that mint's shadow store, and nobody wrote it.</p>
     */
    static Map<String, String> mintStores(ActiveRegion active) {
        Map<String, String> stores = new java.util.LinkedHashMap<String,
                String>();
        Set<String> minted = mintedLocations(active).keySet();
        if (minted.isEmpty()) return stores;
        // EVERY version whose whole value is a mint's symbol, not the first
        // one per symbol: mintedLocations keeps the first because a
        // placeholder row states one mint version, and a symbol that
        // reaches a second store would then have left that store published
        // as a write (v201 `M_L_field_REGION.692d5ed3...` survived exactly
        // that way).  A store is a store wherever it stands.
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
                if (minted.contains(symbol) && declaredMint(active, symbol)) {
                    stores.put(locationKey + "#" + id, symbol);
                }
            }
        }
        return stores;
    }

    /**
     * Where the VM says each minted symbol lives: symbol -&gt; location key.
     *
     * <p>A mint installs a symbol INTO a field the VM versions, so the
     * write log already names the location and the exact version whose
     * whole value that symbol is -- hdfs-17960's counter is version 172 of
     * {@code INSTANCE_FIELD/19#24}, and the anchor's own branch reads that
     * version.  Only a version whose expression IS the symbol counts (a
     * later version computed FROM it is a different value), and the first
     * such version wins.</p>
     */
    private static Map<String, String[]> mintedLocations(ActiveRegion active) {
        Map<String, String[]> bySymbol =
                new java.util.LinkedHashMap<String, String[]>();
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
                if (symbol.isEmpty() || !declaredMint(active, symbol)) {
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
                if (!bySymbol.containsKey(symbol)) {
                    bySymbol.put(symbol, new String[]{locationKey,
                            Long.toString(id), Long.toString(observed)});
                }
            }
        }
        return bySymbol;
    }

    /**
     * A source type name as the JVM descriptor a row states.
     *
     * <p>Only ever called with a type the declaration or the VM's own symbol
     * stated: an unstated one is refused where it is read, because the
     * descriptor drives this row's sort.</p>
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
     * The one spelling of a symbol.
     *
     * <p>A row's symbol and the symbol leaf inside the expressions the
     * same session publishes have to be the same string: the composer
     * binds a root by finding its name in a lowered term, and a row that
     * names {@code REGION.r.in.uuid} while every term says {@code
     * M_J_field_REGION.r.in.uuid.occ.<hash>_java/lang/Long} binds
     * nothing.  The VM's name is the one that appears in the terms, so
     * that is the one the row states.</p>
     */
    static String vmSymbol(JsonObject row) {
        String raw = optionalString(row, "rawSymbol");
        if (!raw.isEmpty()) return raw;
        // A configured source mints through the VM's own label and states
        // no raw symbol of its own; the expression it published names it.
        String leaf = symbolLeaf(row.get("expression"), 0);
        return leaf.isEmpty() ? optionalString(row, "symbol") : leaf;
    }

    /** The first symbol leaf an expression states, or {@code ""}. */
    private static String symbolLeaf(JsonElement node, int depth) {
        if (cut("symbolLeaf", depth)) return "";
        if (node == null || node.isJsonNull()) return "";
        if (node.isJsonArray()) {
            for (JsonElement element : node.getAsJsonArray()) {
                String found = symbolLeaf(element, depth + 1);
                if (!found.isEmpty()) return found;
            }
            return "";
        }
        if (!node.isJsonObject()) return "";
        JsonObject object = node.getAsJsonObject();
        if (optionalString(object, "_type").contains("Symbol")) {
            return optionalString(object, "_exp");
        }
        for (Map.Entry<String, JsonElement> member : object.entrySet()) {
            String found = symbolLeaf(member.getValue(), depth + 1);
            if (!found.isEmpty()) return found;
        }
        return "";
    }

    /**
     * Whether this row MINTED the symbol it names.
     *
     * <p>The VM is the authority and both runtime row shapes carry its
     * answer: a declared read whose field already held a propagated
     * expression keeps it ({@code SymInstance::has_sym_exp} makes the mint
     * a no-op) and the row says {@code reused}.  Such a row created no
     * symbol, so the only name {@link #vmSymbol} can give it is another
     * mint's -- which is why "did this row mint" and "may this row be a
     * root" are ONE question, asked here.</p>
     */
    private static boolean minted(JsonObject row) {
        return !optionalBool(row, "reused", false);
    }

    /**
     * What kind of root one mint row states.
     *
     * <p>The case declares which reads are clocks, a marker mints a boolean,
     * everything else is integral.  The kind decides how the composer may
     * move it -- a clock is unbounded with a floor, a marker has two values
     * -- so it is read from the declaration, never guessed from the value or
     * from the name of the callee that produced it.</p>
     */
    private static RootKind kindOf(JsonObject row) {
        if (optionalBool(row, InputActionCatalog.DECLARED_WALL_CLOCK,
                false)) {
            return RootKind.CLOCK;
        }
        // A configured source mints through the VM's own label and states no
        // type of its own; the symbol it minted carries it.  Without the
        // second reading a boolean configured root -- hdfs-17960's
        // HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED -- is published INTEGRAL,
        // and a composer then looks for a range where there are two values.
        String stated = optionalString(row, "javaType");
        String javaType = stated.isEmpty()
                ? symbolType(row.get("expression"), 0) : stated;
        return "Z".equals(javaType) || "boolean".equals(javaType)
                ? RootKind.MARKER : RootKind.INTEGRAL;
    }

    /** The type of the first symbol leaf an expression states. */
    private static String symbolType(JsonElement node, int depth) {
        if (cut("symbolType", depth)) return "";
        if (node == null || node.isJsonNull()) return "";
        if (node.isJsonArray()) {
            for (JsonElement element : node.getAsJsonArray()) {
                String found = symbolType(element, depth + 1);
                if (!found.isEmpty()) return found;
            }
            return "";
        }
        if (!node.isJsonObject()) return "";
        JsonObject object = node.getAsJsonObject();
        if (optionalString(object, "_type").contains("Symbol")) {
            return optionalString(object, "_java_type");
        }
        for (Map.Entry<String, JsonElement> member : object.entrySet()) {
            String found = symbolType(member.getValue(), depth + 1);
            if (!found.isEmpty()) return found;
        }
        return "";
    }}

package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.WireDeclarations;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

/**
 * Values crossing processes at serialization boundaries, at run time
 * (WIRE-CODEC §4): the codec hooks {@code causynth.CodecWeave} weaves call
 * here (through {@link ConcolicRegionRuntime}), and so do the message doors.
 *
 * <p>An encode walks its graph ({@link CodecWalker}) and exports each leaf
 * of a demanded port ({@link DemandedPorts}) as holes ({@link CodecExport});
 * the entries are bound to their message ({@link CodecMessages}), never to
 * the thread, and travel in its envelope ({@link CodecEnvelope}).  A decode
 * applies the message its encoded argument was read from, else the one its
 * thread's inbound exchange carried, else nothing: the graph is local data.
 * Every export and attach row is published when the message is: an encode no
 * message carries is counted, not published.</p>
 *
 * <p>Inert without a workload session or declarations: the recording and a
 * system that declares no codec run no walk.  Every step runs with
 * observation paused and never throws into the workload.</p>
 */
final class CodecRuntime {
    private CodecRuntime() {
    }

    private static final Object LOCK = new Object();
    private static volatile Setup setup;

    /** The declarations, the demanded ports, and a walker per codec. */
    private static final class Setup {
        final WireDeclarations declared;
        final Map<String, CodecWalker> walkers = new HashMap<>();

        Setup(WireDeclarations declared, DemandedPorts demanded) {
            this.declared = declared;
            for (WireDeclarations.Codec codec : declared.codecs()) {
                walkers.put(codec.name(), new CodecWalker(codec,
                        declared.views(), demanded::demanded));
            }
        }
    }

    /** The configured setup; none (named) when it cannot be read. */
    private static Setup setup() {
        Setup known = setup;
        if (known != null) return known;
        synchronized (LOCK) {
            if (setup == null) {
                try {
                    setup = new Setup(WireDeclarations.configured(),
                            DemandedPorts.configured());
                } catch (Exception unreadable) {
                    RowRuntime.gap(GapKind.DECLARATION_MISSING,
                            GapClass.BLOCKING, WireDeclarations.PROPERTY,
                            "the codec declarations or the demanded ports "
                                    + "could not be read, so no value a codec "
                                    + "carried crossed: " + unreadable);
                    setup = new Setup(WireDeclarations.NONE,
                            DemandedPorts.of(Collections.<String>emptySet()));
                }
            }
            return setup;
        }
    }

    /** The walker of a live codec, or null outside a workload session. */
    private static CodecWalker walker(String codec) {
        if (!ConcolicRegionRuntime.sessionOpen()) return null;
        return setup().walkers.get(codec);
    }

    // ---- the woven hooks ----------------------------------------------------

    /** Per thread, per codec: how deep in its declared methods it runs. */
    private static final ThreadLocal<Map<String, Integer>> DEPTH =
            ThreadLocal.withInitial(HashMap::new);

    /** Enters a declared method of {@code codec}: the depth before. */
    static int enter(String codec) {
        Map<String, Integer> depths = DEPTH.get();
        Integer depth = depths.get(codec);
        int before = depth == null ? 0 : depth;
        depths.put(codec, before + 1);
        return before;
    }

    /** Leaves it, back to {@code depth}. */
    static void exit(String codec, int depth) {
        if (depth <= 0) DEPTH.get().remove(codec);
        else DEPTH.get().put(codec, depth);
    }

    /**
     * An encoder's exit: {@code graph} was encoded into {@code encoded}.
     * Only the outermost declared method of a codec acts (depth 0).
     *
     * @param exchange whether the encoder is bound to its exchange bracket
     *                 rather than to {@code encoded}
     */
    static void encoded(String codec, int depth, Object graph,
                        Object encoded, boolean exchange) {
        if (depth != 0 || graph == null) return;
        ConcolicRegionRuntime.pauseObservation();
        try {
            CodecWalker walker = walker(codec);
            if (walker == null) return;
            CodecWalker.Walk walk = walker.leaves(graph);
            note(walker, walk);
            if (walk.leaves.isEmpty()) return;
            if (exchange) {
                CodecMessages.Bracket bracket = CodecMessages.innermost();
                if (bracket == null) {
                    CodecMessages.unsent(codec);
                    return;
                }
                bracket.staged.addAll(CodecExport.export(walker, walk.leaves,
                        bracket.nextOrdinal(codec)));
                return;
            }
            List<CodecMessages.Entry> entries = CodecExport.export(walker,
                    walk.leaves, 0);
            if (entries.isEmpty()) return;
            if (encoded == null) {
                CodecMessages.unsent(codec);
                return;
            }
            int dropped = CodecMessages.encoded(encoded, codec, entries);
            if (dropped > 0) {
                RowRuntime.gap(GapKind.BOUND_INSUFFICIENT, GapClass.DIAGNOSTIC,
                        codec, "the run holds " + CodecMessages.MAX_ENCODED
                                + " live encodes no door wrote yet; the eldest"
                                + " were dropped, so a door that writes one"
                                + " sends no value");
            }
        } catch (Throwable failure) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, codec,
                    "an encode of " + codec + " exported nothing: "
                            + ConcolicRegionRuntime.rootCause(failure));
        } finally {
            ConcolicRegionRuntime.resumeObservation();
        }
    }

    /**
     * A decoder's graph: mints the holes of the message it was decoded from
     * and answers the graph, whose root a re-homed leaf may have replaced.
     * Only the outermost declared method of a codec acts (depth 0).
     */
    static Object decoded(String codec, int depth, Object encoded,
                          Object graph) {
        if (depth != 0 || graph == null) return graph;
        ConcolicRegionRuntime.pauseObservation();
        try {
            CodecWalker walker = walker(codec);
            if (walker == null) return graph;
            CodecMessages.Message message = CodecMessages.delivered(encoded);
            boolean bound = message != null;
            if (!bound) {
                MessageDoors.Inbound inbound = MessageDoors.current();
                message = inbound == null ? null : inbound.codecMessage;
            }
            if (message == null) return graph;
            List<CodecMessages.Entry> group = group(walker, graph, message,
                    bound);
            return group.isEmpty() ? graph
                    : HandoffMint.mintHoles(walker, graph, message, group);
        } catch (Throwable failure) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, codec,
                    "a decode of " + codec + " minted nothing: "
                            + ConcolicRegionRuntime.rootCause(failure));
            return graph;
        } finally {
            ConcolicRegionRuntime.resumeObservation();
        }
    }

    /**
     * The first encode of this codec in {@code message} whose paths all
     * resolve in {@code graph}.  A message read from the array decoded
     * here is this graph, so a path it does not resolve is named; an
     * exchange's message may meet local data, which resolves none.
     */
    private static List<CodecMessages.Entry> group(CodecWalker walker,
                                                   Object graph,
                                                   CodecMessages.Message message,
                                                   boolean bound) {
        Map<Integer, List<CodecMessages.Entry>> encodes = new TreeMap<>();
        for (CodecMessages.Entry entry : message.entries) {
            if (!entry.codec.equals(walker.codec())) continue;
            encodes.computeIfAbsent(entry.ordinal,
                    ordinal -> new ArrayList<>()).add(entry);
        }
        for (List<CodecMessages.Entry> encode : encodes.values()) {
            String unmatched = "";
            boolean any = false;
            for (CodecMessages.Entry entry : encode) {
                if (walker.resolve(graph, entry.path) != null) {
                    any = true;
                } else if (unmatched.isEmpty()) {
                    unmatched = CodecWalker.text(entry.path);
                }
            }
            if (unmatched.isEmpty()) return encode;
            if (bound || any) {
                RowRuntime.gap(GapKind.CODEC_MISMATCH, GapClass.DIAGNOSTIC,
                        message.key, "PATH_UNMATCHED: " + walker.codec()
                                + " decoded a graph where the entry's path "
                                + unmatched + " is absent (a view that does "
                                + "not see it), so its leaves stay concrete");
            }
        }
        return new ArrayList<>();
    }

    // ---- the doors ----------------------------------------------------------

    /**
     * The most bytes one message's symbolic header may take on
     * {@code transport}: its declared bound, else none.
     */
    static int headerBytes(String transport) {
        if (!ConcolicRegionRuntime.sessionOpen()) return Integer.MAX_VALUE;
        WireDeclarations.Transport declared =
                setup().declared.transport(transport);
        return declared == null || declared.envelopeBytes() == 0
                ? Integer.MAX_VALUE : declared.envelopeBytes();
    }

    /**
     * The codec envelope of one outbound message, within {@code maxBytes}:
     * its payload walked with its transport's codec for this half, then
     * what the thread's innermost bracket of the transport staged.  Every
     * entry carried publishes its export row now, keyed by
     * {@code correlationId}.
     */
    static String outbound(String transport, String correlationId,
                           boolean request, Object payload, int maxBytes) {
        if (!ConcolicRegionRuntime.sessionOpen()) return "";
        ConcolicRegionRuntime.pauseObservation();
        try {
            WireDeclarations.Transport declared =
                    setup().declared.transport(transport);
            List<CodecMessages.Entry> entries = new ArrayList<>();
            String codec = declared == null ? null : declared.codec(request);
            CodecWalker walker = codec == null ? null : walker(codec);
            if (walker != null && payload != null) {
                CodecWalker.Walk walk = walker.leaves(payload);
                note(walker, walk);
                entries.addAll(CodecExport.export(walker, walk.leaves, 0));
            }
            entries.addAll(CodecMessages.drain(transport));
            if (entries.isEmpty()) return "";
            CodecEnvelope.Written written = CodecEnvelope.write(
                    correlationId, entries, maxBytes);
            for (CodecMessages.Entry entry : written.carried) {
                RowRuntime.exportedHole(entry, correlationId);
            }
            return written.wire;
        } catch (Throwable failure) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    transport, "a message of " + transport + " carries no"
                            + " codec value: "
                            + ConcolicRegionRuntime.rootCause(failure));
            return "";
        } finally {
            ConcolicRegionRuntime.resumeObservation();
        }
    }

    /** The codec message an inbound envelope carried, or null. */
    static CodecMessages.Message inbound(String wire, String correlationId) {
        if (wire.isEmpty() || !ConcolicRegionRuntime.sessionOpen()) {
            return null;
        }
        ConcolicRegionRuntime.pauseObservation();
        try {
            List<CodecMessages.Entry> entries = CodecEnvelope.read(wire);
            return entries.isEmpty() ? null
                    : new CodecMessages.Message(correlationId, "", entries);
        } finally {
            ConcolicRegionRuntime.resumeObservation();
        }
    }

    /**
     * A write of a stored version: what an encode bound to {@code data}
     * travels with the version, and its export rows are published.
     */
    static void stored(String transport, String key, Object data) {
        if (data == null || !ConcolicRegionRuntime.sessionOpen()) return;
        ConcolicRegionRuntime.pauseObservation();
        try {
            List<CodecMessages.Entry> entries = CodecMessages.written(data);
            if (entries.isEmpty()) return;
            CodecMessages.Stored stored = CodecMessages.stored(transport,
                    key, entries);
            for (CodecMessages.Entry entry : entries) {
                RowRuntime.exportedHole(entry, stored.message.key);
            }
            if (!stored.dropped.isEmpty()) {
                RowRuntime.gap(GapKind.BOUND_INSUFFICIENT,
                        GapClass.DIAGNOSTIC, stored.dropped, "the run keeps "
                                + "the codec values of " + CodecMessages
                                .MAX_PATHS + " stored paths; this path's were"
                                + " dropped, so a later read of them crosses"
                                + " concrete");
            }
        } finally {
            ConcolicRegionRuntime.resumeObservation();
        }
    }

    /** A read of a stored version: {@code data} is that version's. */
    static void fetched(String transport, String key, Object data) {
        if (data == null || !ConcolicRegionRuntime.sessionOpen()) return;
        ConcolicRegionRuntime.pauseObservation();
        try {
            CodecMessages.Fetch fetch = CodecMessages.fetched(transport, key,
                    data);
            if (fetch.dropped) {
                RowRuntime.gap(GapKind.BOUND_INSUFFICIENT,
                        GapClass.DIAGNOSTIC, transport + " " + key,
                        "this version was read after "
                                + CodecMessages.VERSIONS + " newer versions of"
                                + " its path were written, and its codec"
                                + " values were dropped with it");
            }
        } finally {
            ConcolicRegionRuntime.resumeObservation();
        }
    }

    // ---- what a walk could not address --------------------------------------

    /** Per codec and class: how often a TREE walk met it with no view. */
    private static final Map<String, Integer> VIEW_MISSING =
            new LinkedHashMap<>();

    private static void note(CodecWalker walker, CodecWalker.Walk walk) {
        String codec = walker.codec();
        synchronized (VIEW_MISSING) {
            for (String type : walk.viewMissing) {
                VIEW_MISSING.merge(codec + " " + type, 1, Integer::sum);
            }
        }
        for (String path : walk.unaddressable) {
            mismatch(codec, "LEAF_UNADDRESSABLE", path + " is an element of"
                    + " an unordered collection, which no key path names");
        }
        for (String field : walk.unsupported) {
            mismatch(codec, "LEAF_UNSUPPORTED", field + ", which no single"
                    + " leaf holds");
        }
        for (String path : walk.nullLeaves) {
            mismatch(codec, "NULL_LEAF", path + " holds null");
        }
        if (!walk.bound.isEmpty()) {
            RowRuntime.gap(GapKind.BOUND_INSUFFICIENT, GapClass.DIAGNOSTIC,
                    codec, "a walk of " + codec + " stopped: " + walk.bound);
        }
    }

    private static void mismatch(String codec, String reason, String what) {
        RowRuntime.gap(GapKind.CODEC_MISMATCH, GapClass.DIAGNOSTIC, codec,
                reason + ": a demanded leaf of " + codec + " at " + what
                        + ", so it crosses concrete");
    }

    /**
     * What only the run's end can count, one row per codec or class: the
     * encodes no message carried, and the application classes walks met
     * with no view.
     */
    static void publishTotals() {
        for (Map.Entry<String, Long> unsent
                : CodecMessages.unsentCounts().entrySet()) {
            RowRuntime.gap(GapKind.CODEC_MISMATCH, GapClass.DIAGNOSTIC,
                    unsent.getKey(), "UNSENT: " + unsent.getValue()
                            + " encode(s) of " + unsent.getKey()
                            + " exported values no message carried");
        }
        Map<String, Integer> missing;
        synchronized (VIEW_MISSING) {
            missing = new LinkedHashMap<>(VIEW_MISSING);
        }
        for (Map.Entry<String, Integer> view : missing.entrySet()) {
            String codec = view.getKey().substring(0,
                    view.getKey().indexOf(' '));
            RowRuntime.gap(GapKind.CODEC_MISMATCH, GapClass.DIAGNOSTIC,
                    view.getKey(), "VIEW_MISSING: " + view.getValue()
                            + " walk(s) of " + codec + " met "
                            + view.getKey().substring(codec.length() + 1)
                            + ", which no CODEC_VIEW declares, and walked"
                            + " nothing in it");
        }
    }

    /** Forgets every binding and count: a session boundary. */
    static void clear() {
        CodecMessages.clear();
        synchronized (VIEW_MISSING) {
            VIEW_MISSING.clear();
        }
    }

    // ---- identity and the VM's address of a leaf ----------------------------

    /**
     * The occurrence a codec event runs in: the innermost live region's,
     * else the one running here, stated as an unselected activation.
     */
    static OccurrenceAddress occurrenceHere(String port) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active != null && active.d3Address != null) {
            return active.d3Address;
        }
        RuntimeTraceContext.View view = RuntimeTraceContext.current();
        OccurrenceAddress here = RowRuntime.occurrenceHere(
                view.source == null ? "" : view.source.key(), port);
        RowRuntime.ambientActivation(here);
        return here;
    }

    /** The transport's retry number of the exchange here, or 0. */
    static int attempt() {
        return WireExport.attemptOf(RuntimeTraceContext.current());
    }

    /**
     * A hole's event frame (IDENTITY §7.5): {@code port@<storeKey><path>#k},
     * the store key empty for an exchange, so two queue items one occurrence
     * decodes stay apart; the endpoint's site stays the port.  A frame names
     * no {@code /} or {@code @} (an index's separators), so those and
     * {@code %} are escaped {@code %2F %40 %25}.
     */
    static String frameSite(String port, String storeKey, List<Object> path,
                            int hole) {
        String frame = port + "@" + storeKey + CodecWalker.text(path) + "#"
                + hole;
        return frame.replace("%", "%25").replace("/", "%2F")
                .replace("@", "%40");
    }

    static Object vmParent(CodecWalker.Leaf leaf) {
        return leaf.holding == CodecWalker.Holding.ROOT
                || leaf.holding == CodecWalker.Holding.VIEW ? leaf.value
                : leaf.holder;
    }

    static ConcolicVmBroker.SlotKind vmSlotKind(CodecWalker.Leaf leaf) {
        switch (leaf.holding) {
            case FIELD:
                return ConcolicVmBroker.SlotKind.FIELD;
            case ELEMENT:
                return ConcolicVmBroker.SlotKind.ELEMENT;
            case ENTRY:
                return ConcolicVmBroker.SlotKind.ENTRY;
            case POSITION:
                return ConcolicVmBroker.SlotKind.POSITION;
            default:
                return ConcolicVmBroker.SlotKind.VALUE;
        }
    }

    static Object vmSlot(CodecWalker.Leaf leaf) {
        return vmSlotKind(leaf) == ConcolicVmBroker.SlotKind.VALUE ? null
                : leaf.slot;
    }

    /** Whether the VM refused a slot because it does not model its
     *  container: the leaf object itself is asked instead. */
    static boolean unmodeled(JsonObject answer) {
        return answer != null
                && "UNSUPPORTED".equals(optionalString(answer, "status"))
                && optionalString(answer, "reason").startsWith(
                "NOT_A_MODELED_");
    }
}

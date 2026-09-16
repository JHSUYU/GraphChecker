package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Term;

import edu.uva.liftlab.graphchecker.contract.Arm;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.Family;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.explore.Corpus;
import edu.uva.liftlab.graphchecker.explore.SlotTable;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.smtLiteral;

/**
 * THE FAMILIES of one composition: which deliveries a slot had, in SMT.
 *
 * <p>Relocated out of {@link Composer} unchanged -- the same bodies, the
 * same order, no rule altered.  {@code Arms} decides what an arm IS; this
 * decides how the alternatives of one slot read in a query, which is all a
 * composer should own of them: the WIRE families of the interactions a path
 * reaches ({@link #closeFamilies}), the STATE families of the reads a
 * writer occurrence could have delivered otherwise
 * ({@link #stateFamilies}), the rendering of one arm with its prefix and
 * its guard ({@link #render}), and the rows that say which slots this
 * anchor had no use for.</p>
 *
 * <p>It holds the composition's own collections rather than copies: a
 * family registered here is a family of that composition's manifest, and
 * the gap rows it raises are that composition's ledger.  The three things
 * that stay with {@link Composer} are reached through it -- the gap
 * writer, the free-symbol test, and this epoch's slot table, which the
 * composer assigns while it runs.</p>
 */
final class ComposedFamilies {

    private final Composer composer;
    private final Corpus corpus;
    private final OccurrenceAddress anchor;
    private final Arms arms;
    private final SmtLowering lowering;
    private final Map<String, Family> families;
    private final Map<String, Set<String>> unattestedRoots;
    private final Set<String> replacing;
    private final Set<String> slotNamed;
    private final Set<String> unpairedNamed;
    private final Set<String> aliasingNamed;
    private final List<GapRow> gaps;

    ComposedFamilies(Composer composer, Corpus corpus,
                     OccurrenceAddress anchor, Arms arms,
                     SmtLowering lowering, Map<String, Family> families,
                     Map<String, Set<String>> unattestedRoots,
                     Set<String> replacing, Set<String> slotNamed,
                     Set<String> unpairedNamed, Set<String> aliasingNamed,
                     List<GapRow> gaps) {
        this.composer = composer;
        this.corpus = corpus;
        this.anchor = anchor;
        this.arms = arms;
        this.lowering = lowering;
        this.families = families;
        this.unattestedRoots = unattestedRoots;
        this.replacing = replacing;
        this.slotNamed = slotNamed;
        this.unpairedNamed = unpairedNamed;
        this.aliasingNamed = aliasingNamed;
        this.gaps = gaps;
    }

    /** The declared roots one lowered expression mentions. */
    private Set<String> declaredRootsIn(String term) {
        Set<String> found = new LinkedHashSet<String>();
        for (Map.Entry<String, List<RootMintRow>> entry
                : corpus.roots().entrySet()) {
            RootMintRow row = corpus.anyRoot(entry.getKey());
            if (row == null || !row.declared()) continue;
            if (SmtLowering.mentions(term, row.symbol())) {
                found.add(row.rootId());
            }
        }
        return found;
    }


    void closeFamilies(Corpus.RecordedPath path, int ordinal,
                               String selector, Set<String> reached) {
        for (AttachRow attach : corpus.attachesOn(path.sessionId,
                anchor)) {
            Interaction slot = attach.interaction();
            if (slot == null) continue;
            Map<String, List<String>> bySlot =
                    new LinkedHashMap<String, List<String>>();
            Map<String, List<Arm>> rowsBySlot =
                    new LinkedHashMap<String, List<Arm>>();
            for (Arms.Arm arm : arms.wireArms(slot, attach.symbol())) {
                if (replacing.contains(arm.sessionId())) continue;
                String text = render(arm,
                        Collections.singletonList(arm.symbol()));
                if (text.isEmpty()) continue;
                add(bySlot, arm.slotId(), text);
                add(rowsBySlot, arm.slotId(), row(arm));
            }
            for (Map.Entry<String, List<String>> family : bySlot.entrySet()) {
                reached.add(family.getKey());
                slotOpened(family.getKey(), slot);
                families.put(family.getKey(), Family.of(family.getKey(),
                        rowsBySlot.get(family.getKey())));
                lowering.assertNamed("handoff_family__" + ordinal + "__"
                                + ArtifactIO.digest(family.getKey(), 12),
                        "(=> " + selector + " "
                                + VmTermLowering.or(family.getValue()) + ")");
            }
            if (bySlot.isEmpty()) {
                composer.gap(GapKind.UNPRODUCIBLE_ANSWER, GapClass.DIAGNOSTIC,
                        slot.id(), "no session of this corpus published "
                                + "what was delivered at this interaction");
            }
        }
    }

    /**
     * One shared arm, rendered: its prefix, its guard, its binding.
     *
     * <p>{@link Arms} decided what the arm IS; this decides how it reads in
     * SMT, which is all a stage should own of it.</p>
     */
    private String render(Arms.Arm arm, List<String> symbols) {
        Term delivered = lower(arm.sessionId(), arm.expressionRef(),
                "arm:" + arm.slotId());
        if (delivered == null) return "";
        List<String> conjuncts = prefix(arm);
        if (conjuncts == null) return "";
        for (Map.Entry<String, String> guard : arm.guard().entrySet()) {
            String literal = smtLiteral(guard.getValue());
            if (literal.isEmpty()) continue;
            // The name has to be IN the query.  A guard names a root the
            // arm's own expression need not mention -- the delivering
            // replay's valuation of every varied root is part of what the
            // delivery happened under -- and asserting an equality over a
            // constant nothing declares makes z3 answer the whole query
            // with an error instead of a verdict.  The one registry says
            // whether the recording states the name, and at what sort.
            if (!lowering.declareStated(guard.getKey())) {
                composer.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                        guard.getKey(), "an arm of " + arm.slotId()
                                + " is guarded by a symbol no row of this "
                                + "corpus declares a sort for");
                continue;
            }
            conjuncts.add("(= " + guard.getKey() + " " + literal + ")");
        }
        for (String symbol : symbols) {
            if (symbol == null || symbol.isEmpty()) continue;
            lowering.declareStated(symbol, delivered.sort);
            conjuncts.add("(= " + symbol + " " + delivered.text + ")");
        }
        if (!arm.attested()) {
            Set<String> held = unattestedRoots.get(arm.slotId());
            if (held == null) {
                held = new LinkedHashSet<String>();
                unattestedRoots.put(arm.slotId(), held);
            }
            held.addAll(declaredRootsIn(delivered.text));
            composer.gap(GapKind.UNATTESTED_ARM, GapClass.DIAGNOSTIC, arm.slotId(),
                    "the producer ran concretely in session "
                            + arm.sessionId() + ": the arm states what was "
                            + "delivered, and no witness may move a root "
                            + "inside it");
        }
        return VmTermLowering.and(conjuncts);
    }

    /**
     * The producer path's prefix, in the producer session's own scope.
     *
     * <p>Null when a conjunct of it cannot be stated: an arm missing one
     * of the decisions its producer took claims a delivery under weaker
     * conditions than the run had, and a family is a disjunction -- one
     * arm fewer refuses a witness, one arm too wide invents one.</p>
     */
    private List<String> prefix(Arms.Arm arm) {
        List<String> conjuncts = new ArrayList<String>();
        String session = arm.sessionId();
        lowering.begin(session, SmtLowering.joinOf(corpus.session(session)),
                corpus.expressions(session));
        boolean stated = true;
        for (String term : arm.pi()) {
            String conjunct = lowering.statedTerm(term,
                    "arm-pi:" + arm.slotId());
            if (!Arms.predicate(conjunct)) continue;
            if (composer.unknown(conjunct, null, "")) {
                stated = false;
                break;
            }
            conjuncts.add(conjunct);
        }
        stated = stated && lowering.openRefusals().isEmpty();
        conjuncts.addAll(lowering.end());
        return stated ? conjuncts : null;
    }

    /** One arm as the manifest states it. */
    private static Arm row(Arms.Arm arm) {
        return Arm.of(arm.producerPathId().isEmpty() ? arm.sessionId()
                        : arm.producerPathId(), arm.producerPathId(),
                arm.expressionRef(), arm.guardRoots(), arm.attested());
    }

    /** Growth is not an event; the skeleton names what it has not opened. */
    private void slotOpened(String slotId, Interaction slot) {
        SlotTable slots = composer.slots();
        if (slots == null || !slots.stated()) return;
        if (slots.opened(slot.consumer().id())) return;
        if (!slotNamed.add(slotId)) return;
        composer.gap(GapKind.TOPOLOGY_DIVERGENCE, GapClass.DIAGNOSTIC, slotId,
                "this epoch's skeleton has opened no slot for this "
                        + "interaction yet; its arms are composed and the "
                        + "slot table will name it when exploration opens "
                        + "it");
    }

    private static <T> void add(Map<String, List<T>> index, String key,
                                T value) {
        List<T> held = index.get(key);
        if (held == null) {
            held = new ArrayList<T>();
            index.put(key, held);
        }
        held.add(value);
    }

    /**
     * Every interaction the corpus records that this anchor does not reach.
     *
     * <p>Recorded, never a refusal: an interaction outside the anchor's
     * closure says nothing about this anchor's disjunction, and a run that
     * exercised more of the system than this question needs has not gone
     * wrong.  It is named so that a reader comparing the skeleton with the
     * rows can see which pairs the composition had no use for.</p>
     */
    void outsideTheClosure(List<Composer.Disjunct> disjuncts) {
        Set<String> reached = new LinkedHashSet<String>();
        for (Composer.Disjunct disjunct : disjuncts) {
            reached.addAll(disjunct.interactionIds());
        }
        for (String interactionId : corpus.interactions().keySet()) {
            if (reached.contains(interactionId)) continue;
            if (!slotNamed.add(interactionId)) continue;
            composer.gap(GapKind.TOPOLOGY_DIVERGENCE, GapClass.DIAGNOSTIC,
                    interactionId, "no path admitted at this anchor reaches "
                            + "this interaction, so the composition records "
                            + "it and uses nothing from it");
        }
    }

    /**
     * An attach whose producer the recording does not name.
     *
     * <p>Two different absences, and the row says which.  A producer
     * endpoint that exists but could not be addressed in full is
     * LINEAGE_LOST -- the interaction is there and the naming failed.  An
     * attach with no producer at all is an UNSTATED_VALUE: the recording
     * does not say the delivery happened, only that a value arrived.</p>
     */
    void unpaired(String session, AttachRow attach) {
        if (!unpairedNamed.add(session + "|" + attach.endpoint().id())) {
            return;
        }
        Endpoint producer = attach.producer();
        boolean degraded = producer != null
                && producer.occurrence() != null
                && producer.occurrence().lineageLost();
        gaps.add(GapRow.of(session,
                producer == null && !degraded ? GapKind.UNSTATED_VALUE
                        : GapKind.LINEAGE_LOST,
                GapClass.DIAGNOSTIC, attach.endpoint().toString(),
                "this attach names no producer endpoint, so the value it "
                        + "received joins no interaction and has no family; "
                        + "the arrival this session recorded is all the "
                        + "composition states about it"));
    }

    Set<String> stateFamilies(Corpus.RecordedPath path,
                                      int ordinal, String selector,
                                      List<ReadRow> joined,
                                      Set<String> reached) {
        String session = path.sessionId;
        Set<String> chosen = new LinkedHashSet<String>();
        // One choice per (reader occurrence, location): a writer's writes to
        // it move as a BLOCK, and every read of that location inside this
        // occurrence takes the same arm -- never a writer interposed between
        // two reads of one occurrence.
        Map<String, List<ReadRow>> byLocation =
                new LinkedHashMap<String, List<ReadRow>>();
        for (ReadRow read : joined) {
            add(byLocation, SmtLowering.locationKey(read.location()), read);
        }
        for (Map.Entry<String, List<ReadRow>> entry
                : byLocation.entrySet()) {
            List<ReadRow> reads = entry.getValue();
            // Alternatives need an owner that NAMES the storage
            // ({@link Arms#namedOwner}).  A class on a heap location is
            // every instance of it at once, which turns "another writer of
            // L" into "a writer of something else", so such a read keeps
            // the delivery its own run gave it and is named here.
            if (!Arms.namedOwner(reads.get(0).location())) {
                if (aliasingNamed.add(entry.getKey())) {
                    composer.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                            entry.getKey(), "the owner on this location's "
                                    + "rows is a class and not the rid of "
                                    + "one object, so it names every "
                                    + "instance of that class at once: "
                                    + "this read is delivered as its own "
                                    + "run delivered it and gets no "
                                    + "alternative writers");
                }
                continue;
            }
            List<String> symbols = new ArrayList<String>();
            for (ReadRow read : reads) symbols.add(read.symbol());
            List<String> armTerms = new ArrayList<String>();
            for (Arms.Arm arm : arms.stateArms(reads.get(0).endpoint(),
                    session, entry.getKey(),
                    reads.get(0).observedVersion())) {
                if (replacing.contains(arm.sessionId())) continue;
                String text = render(arm, symbols);
                if (text.isEmpty()) continue;
                armTerms.add(text);
                reached.add(arm.slotId());
                families.put(arm.slotId(), Family.of(arm.slotId(),
                        Collections.singletonList(row(arm))));
            }
            // One arm is the run's own interleaving and says nothing the
            // join has not already said.
            if (armTerms.size() < 2) continue;
            chosen.addAll(symbols);
            lowering.assertNamed("state_family__" + ordinal + "__"
                            + ArtifactIO.digest(entry.getKey(), 12),
                    "(=> " + selector + " "
                            + VmTermLowering.or(armTerms) + ")");
        }
        return chosen;
    }

    /**
     * One export's expression, lowered in its own session's scope.
     *
     * <p>Its own session: the identities inside it are that execution's
     * objects, and the reads inside it join to that execution's write log.
     * An arm lowered in the consumer's scope would state one replay's
     * history of another replay's objects.</p>
     */
    Term lower(String session, ExportRow export, String origin) {
        return lower(session, export.expressionRef(), origin);
    }

    Term lower(String session, String expressionRef, String origin) {
        SessionReader reader = corpus.session(session);
        if (reader == null) return null;
        JsonObject expression = reader.expressions()
                .expression(expressionRef);
        if (expression == null) {
            // Same inconsistency as the state join's, and the same class:
            // a row of this corpus cites an expression the corpus does not
            // contain, so what it stands for is not composable from these
            // sessions at all.
            composer.gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING, expressionRef,
                    "a row of session " + session + " cites an expression "
                            + "its session's table does not hold");
            return null;
        }
        lowering.begin(session,
                SmtLowering.joinOf(corpus.session(session)));
        Term value = lowering.term(expression, null, origin);
        List<String> refused = new ArrayList<String>(
                lowering.openRefusals());
        lowering.end();
        if (value == null || !refused.isEmpty()) {
            for (String refusal : refused) {
                composer.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, refusal,
                        "an arm of this corpus rests on a value the "
                                + "recording does not state");
            }
            return null;
        }
        return value;
    }
}

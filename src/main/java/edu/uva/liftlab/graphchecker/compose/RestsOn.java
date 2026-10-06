package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.explore.Corpus;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.ExpressionWalk;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.smt.VmRows;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * WHAT A DELIVERY RESTS ON in one session (PIPELINE §8 P3, §7.2): the
 * occurrences the joins from its prefix reach, each with the seq its prefix
 * runs to ({@link #closure}), their decisions before those seqs ({@link
 * #reachedConditions}), and among those and their reads the ones that rest
 * on what moves ({@link #independence}).  The one notion COMPOSE states a
 * path's and an arm's closure by ({@code Composer}, {@code ComposedFamilies})
 * and EXPLORE demands by ({@link #named}, {@code
 * explore.ClosurePlanner#demanded}): a handoff a kept decision of a reached
 * occurrence names is one COMPOSE binds by its family, so its producer is
 * planned (hdfs-11741: the balancer's KeyManager, reached by the SASL
 * producer's closure, decides on the expiry dates of nn0's
 * updateBlockKeys@1 response, whose handler no session ran).
 */
public final class RestsOn {
    private final Corpus corpus;
    private final StaticScopeMap scope;
    /** The occurrence whose prefix is the question's: never reached by a
     *  join, its reads all its own. */
    private final OccurrenceAddress anchor;
    /** kind|session|start|cutoff|seed terms -> the symbols it rests on
     *  ({@link #named}): EXPLORE asks once per walk of a demand. */
    private final Map<String, Set<String>> cache =
            new LinkedHashMap<String, Set<String>>();

    public RestsOn(Corpus corpus, StaticScopeMap scope,
                   OccurrenceAddress anchor) {
        this.corpus = corpus;
        this.scope = scope;
        this.anchor = anchor;
    }

    /**
     * THE ADMITTED PATHS, COMPOSE's disjuncts and EXPLORE's demand alike
     * (PIPELINE §7.2, §8), each refusal a row of {@code gaps}: every
     * session's path that reached the anchor, or, where none did,
     * every session's path that ran the occurrence and left the way to the
     * throw (its fatal arm the constant healthy decision).  The declared
     * occurrence is always the anchor; a corpus without a target row for it
     * never ran it, a defect, never a reason to elect another occurrence.
     */
    public List<Corpus.RecordedPath> admitted(List<GapRow> gaps) {
        List<Corpus.RecordedPath> admitted =
                new ArrayList<Corpus.RecordedPath>();
        List<TargetRow> targets = corpus.targetsOn(anchor);
        if (targets.isEmpty()) {
            gap(gaps, GapKind.DECLARATION_MISSING, GapClass.BLOCKING,
                    anchor.render(), "the declared occurrence never ran: no "
                            + "session of this corpus published a target row "
                            + "for it");
            return admitted;
        }
        // Where no session reached the anchor, each that ran the occurrence
        // and left the way to the throw at a guard is a path: its fatal arm
        // is the constant healthy decision ({@link #compose}).  Beside a
        // path that reached it, such a disjunct adds nothing.
        boolean reached = false;
        for (TargetRow target : targets) reached |= target.reachedAnchor();
        for (TargetRow target : targets) {
            Corpus.RecordedPath path = corpus.path(target.sessionId(),
                    anchor);
            if (reached && !target.reachedAnchor()) {
                gap(gaps, GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        target.sessionId(), "this session ran the occurrence "
                                + "and did not reach the anchor");
                continue;
            }
            if (path == null) {
                gap(gaps, GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        target.sessionId(), "this session ran the occurrence "
                                + "and published no path at it");
                continue;
            }
            if (!settled(target.sessionId(), gaps)) continue;
            admitted.add(path);
        }
        return admitted;
    }

    /**
     * Whether this session's OWN rows admit the obligation it ran (the
     * replay owns the verdict).  A refused obligation's path is the
     * recording again under a valuation the run did not take, so it is no
     * disjunct.  A SEED admits itself; an obligation the manifest names and
     * no row settles is BLOCKING.
     */
    private boolean settled(String session, List<GapRow> gaps) {
        SessionReader reader = corpus.session(session);
        if (reader == null || reader.seed()) return true;
        Set<String> stated = new LinkedHashSet<String>();
        // {@link SessionReader#admitted} decides; this only names refusals.
        boolean admitted = reader.admitted();
        for (ObligationResult result : reader.obligations()) {
            stated.add(result.obligationId());
            if (result.verdict() == Verdict.ADMITTED) continue;
            gap(gaps, GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC, session,
                    "this replay states " + result.verdict() + " for the "
                            + "obligation it ran (" + result.obligationId()
                            + "): " + result.detail());
        }
        List<String> asked = reader.manifest() == null
                ? Collections.<String>emptyList()
                : reader.manifest().obligationIds();
        for (String obligation : asked) {
            if (stated.contains(obligation)) continue;
            admitted = false;
            gap(gaps, GapKind.UNSTATED_VALUE, GapClass.BLOCKING, obligation,
                    "session " + session + " states it ran this obligation "
                            + "and publishes no verdict for it, so what it "
                            + "settled is not in this corpus");
        }
        return admitted;
    }

    /** One admission row, as COMPOSE names it ({@code Composer#gap}). */
    private void gap(List<GapRow> gaps, GapKind kind, GapClass cls,
                     String subject, String detail) {
        gaps.add(GapRow.of(Composer.COMPOSITION, kind, cls,
                subject == null || subject.trim().isEmpty()
                        ? anchor.render() : subject, detail));
    }

    /** Where one path decided, and on what (Composer#compose). */
    static final class Decided {
        /** The guard it left the way to the throw at, or null. */
        final DecisionRow way;
        /** Whether that guard decided on a symbol. */
        final boolean symbolicWay;
        /** Its prefix runs to here: the target row, the way guard, or the
         *  whole path. */
        final long cutoff;
        /** Its fatal arm: phi; a symbolic way guard's other arm, the way to
         *  the throw; else (a concrete one) the constant false. */
        final String fatalTerm;

        private Decided(DecisionRow way, boolean symbolicWay, long cutoff,
                        String fatalTerm) {
            this.way = way;
            this.symbolicWay = symbolicWay;
            this.cutoff = cutoff;
            this.fatalTerm = fatalTerm;
        }
    }

    /**
     * Where a path decided: at its target row, or, where it never reached
     * the anchor, at the guard it left the way to the throw at (a row that
     * did not reach the anchor stands at no point of it).
     */
    Decided decided(String session, TargetRow target,
                    List<DecisionRow> decisions) {
        DecisionRow way = target.reachedAnchor() ? null : wayGuard(decisions);
        boolean symbolicWay = way != null
                && !corpus.termSymbols(session, way.term()).isEmpty();
        long cutoff = target.reachedAnchor() ? target.seq()
                : way == null ? Long.MAX_VALUE : way.seq();
        String fatalTerm = target.reachedAnchor() ? target.phiTerm()
                : symbolicWay ? Arms.conjunct(way.term(), !way.outcome())
                : "false";
        return new Decided(way, symbolicWay, cutoff, fatalTerm);
    }

    /** The last decision a path took at a site on the way to the throw
     *  (the target sites' path sites), or null. */
    DecisionRow wayGuard(List<DecisionRow> decisions) {
        Set<String> way = new LinkedHashSet<String>();
        for (StaticScopeMap.Site target : scope.targetSites()) {
            way.addAll(target.pathSites());
        }
        DecisionRow last = null;
        for (DecisionRow decision : decisions) {
            if (way.contains(decision.siteId())) last = decision;
        }
        return last;
    }

    /**
     * WHAT EXPLORE DEMANDS of one delivery {@code start} made in this
     * session, the last at {@code cutoff}, of the expressions {@code
     * delivered}: what COMPOSE keeps of the arm it is ({@link #named}).
     */
    public Set<String> ofDelivery(String session, OccurrenceAddress start,
                                  long cutoff, List<String> delivered) {
        return named("delivery", session, start, cutoff, delivered,
                seedWrites(session, delivered),
                Collections.<DecisionRow>emptyList());
    }

    /**
     * WHAT EXPLORE DEMANDS of one admitted path at the anchor: what COMPOSE
     * keeps of it ({@link #named}), its own decisions before where it
     * decided ({@link #decided}) among them, over its fatal arm.
     */
    public Set<String> ofPath(String session, TargetRow target,
                              List<DecisionRow> decisions) {
        Decided at = decided(session, target, decisions);
        // Unseeded, as COMPOSE's path closure (Composer#compose).
        return named("path", session, anchor, at.cutoff,
                Collections.singletonList(at.fatalTerm), null,
                before(decisions, at.cutoff));
    }

    /**
     * The symbols the kept items name -- the decisions and reads a path or
     * a delivery rests on: the closure from {@code start}'s prefix to
     * {@code cutoff} ({@code seeds}: a delivery's, the writes its terms
     * read, {@link #seedWrites}; a path's none, as COMPOSE's), its
     * conditions -- the anchor's {@code own} decisions, which no join
     * reaches, and every reached occurrence's before its cutoff -- and the
     * reads of the reached occurrences, each kept over {@code seedTerms} and
     * what moves; never a root the session minted that nothing kept reads.
     * No family binds anything here: the session's received values, roots
     * and clocks move by the binding rule ({@link
     * SmtLowering.SessionJoin#moves}).  Once per (kind, session, start,
     * cutoff, terms).
     */
    private Set<String> named(String kind, String session,
                              OccurrenceAddress start, long cutoff,
                              List<String> seedTerms, List<WriteRow> seeds,
                              List<DecisionRow> own) {
        String key = kind + "|" + session + "|" + start.id() + "|" + cutoff
                + "|" + seedTerms;
        Set<String> held = cache.get(key);
        if (held != null) return held;
        Map<String, Long> reached = closure(session, start, cutoff, seeds);
        List<DecisionRow> conditions = new ArrayList<DecisionRow>(own);
        conditions.addAll(reachedConditions(session, reached));
        Independence kept = independence(session, seedTerms,
                Collections.<String>emptySet(), reached, conditions);
        Set<String> symbols = new LinkedHashSet<String>();
        for (DecisionRow decision : conditions) {
            if (kept.keeps(decision)) {
                symbols.addAll(corpus.termSymbols(session, decision.term()));
            }
        }
        for (String occurrenceId : reached.keySet()) {
            OccurrenceAddress at = corpus.occurrence(occurrenceId);
            if (at == null) continue;
            for (ReadRow read : corpus.readsOn(session, at)) {
                if (kept.keeps(read) && read.symbol() != null
                        && !read.symbol().isEmpty()) {
                    symbols.add(read.symbol());
                }
            }
        }
        cache.put(key, symbols);
        return symbols;
    }

    /**
     * The container VERSIONS delivered expressions read: a projection
     * names the read, but the closure needs the write the producer had in
     * hand (latest version at or before the read).  Resolved only by
     * {@link Corpus#expressionStateReads}, the edge exploration grows by
     * too (PIPELINE §7.2), so arms and waves agree on what a delivery is made
     * of.
     */
    List<WriteRow> seedWrites(String session, Collection<String> refs) {
        List<WriteRow> writes = new ArrayList<WriteRow>();
        Set<String> seen = new LinkedHashSet<String>();
        for (String ref : refs) {
            for (Corpus.StateRead read
                    : corpus.expressionStateReads(session, ref)) {
                if (!seen.add(read.locationKey() + "#"
                        + read.write().version())) {
                    continue;
                }
                writes.add(read.write());
            }
        }
        return writes;
    }

    /**
     * Every row of this session that states a value a symbol of this path
     * may be: every MINT ROW of the session wherever published (a mint is
     * identified by its version, see {@link SmtLowering#mintedReadSymbol};
     * a sibling activation may publish it under its own address), then the
     * reads of the reached occurrences.
     */
    List<ReadRow> statedRows(String session, Set<String> occurrences) {
        List<ReadRow> rows = new ArrayList<ReadRow>();
        Set<String> stated = new LinkedHashSet<String>();
        SessionReader reader = corpus.session(session);
        // Mint rows first: other reads resolve to the symbols they state.
        if (reader != null) {
            for (ReadRow read : reader.reads()) {
                if (read.mintVersion() >= 0L && read.symbol() != null
                        && !read.symbol().isEmpty()
                        && stated.add(read.symbol())) {
                    rows.add(read);
                }
            }
        }
        // Then the anchor, then reached occurrences in closure order (P3);
        // a symbol is stated by the first row met.
        for (String occurrenceId : occurrences) {
            OccurrenceAddress at = corpus.occurrence(occurrenceId);
            if (at == null) continue;
            for (ReadRow read : corpus.readsOn(session, at)) {
                if (read.symbol() == null || stated.add(read.symbol())) {
                    rows.add(read);
                }
            }
        }
        return rows;
    }

    /**
     * The occurrences this path's joins reach, and each one's cutoff seq:
     * P3, a row-level fixed point over ONE session's log.
     *
     * <p>The start keeps its cutoff (the target observation; widening it
     * would include the anchor decision phi negates).  Any other occurrence
     * is reached at the seq of the write a read joined to, widened by later
     * writes; its reads before the cutoff are joined in turn.</p>
     *
     * <p>P3 (PIPELINE §8): EARLIER VERSIONS of a reached write's location
     * are reached too, since a state is the result of every earlier mutation (e.g. what
     * a map lacks was removed earlier under a clock comparison).  Each
     * (location, version) is handled once.</p>
     */
    Map<String, Long> closure(String session, OccurrenceAddress start,
                              long cutoff, List<WriteRow> seeds) {
        return closure(log(session), anchor, start, cutoff, seeds, true,
                null);
    }

    /** One session's rows as a closure reads them: this corpus's. */
    private Log log(String session) {
        return new Log() {
            @Override
            public List<ReadRow> readsOn(String occurrenceId) {
                OccurrenceAddress at = corpus.occurrence(occurrenceId);
                return at == null ? Collections.<ReadRow>emptyList()
                        : corpus.readsOn(session, at);
            }

            @Override
            public WriteRow writeOf(String locationKey, long version) {
                return corpus.writeOf(session, locationKey, version);
            }

            @Override
            public List<WriteRow> writesOf(String locationKey) {
                return corpus.writesOf(session, locationKey);
            }
        };
    }

    /** One session's rows, as a closure reads them. */
    public interface Log {
        /** The reads one occurrence made, in order. */
        List<ReadRow> readsOn(String occurrenceId);

        /** The write of one version of one location, or null. */
        WriteRow writeOf(String locationKey, long version);

        /** Every write of one location. */
        List<WriteRow> writesOf(String locationKey);
    }

    /** What a closure tells its reader of each read it met. */
    public interface Reads {
        /** A read before its occurrence's cutoff, and the write its version
         *  was (null: a store outside every region, which joins nothing). */
        void joined(ReadRow read, WriteRow write);

        /** A read at or past its occurrence's cutoff: nothing joins it. */
        void past(ReadRow read);
    }

    /**
     * THE CLOSURE (P3), COMPOSE's, EXPLORE's and CONFIRM's alike: the
     * occurrences {@code start}'s prefix to {@code cutoff} reaches through
     * the writes its reads joined, each with the seq its own prefix runs to.
     * The anchor's reads are taken whole where {@code anchorWhole} --
     * COMPOSE joins all of them as its inputs -- and cut at its cutoff where
     * not: a run that takes the fatal arm throws there, and no edge after it
     * can be taken (CONFIRM's ORDER, adhoc token-pw-expired: the key map is
     * read after the expiry check).  {@code reads}, when given, hears each
     * read met.
     */
    public static Map<String, Long> closure(Log log,
                                            OccurrenceAddress anchor,
                                            OccurrenceAddress start,
                                            long cutoff,
                                            List<WriteRow> seeds,
                                            boolean anchorWhole,
                                            Reads reads) {
        Map<String, Long> reached = new LinkedHashMap<String, Long>();
        reached.put(start.id(), cutoff);
        List<String> pending = new ArrayList<String>();
        pending.add(start.id());
        List<WriteRow> versions = new ArrayList<WriteRow>();
        Set<String> handled = new LinkedHashSet<String>();
        if (seeds != null) {
            for (WriteRow seed : seeds) {
                reach(seed, anchor, start, reached, pending, versions,
                        handled);
            }
        }
        while (!pending.isEmpty() || !versions.isEmpty()) {
            while (!pending.isEmpty()) {
                String at = pending.remove(0);
                boolean whole = anchorWhole && anchor.id().equals(at);
                long cut = reached.get(at);
                for (ReadRow read : log.readsOn(at)) {
                    if (!whole && read.seq() >= cut) {
                        if (reads != null) reads.past(read);
                        continue;
                    }
                    if (read.observedVersion() < 0L) continue;
                    WriteRow write = log.writeOf(SmtLowering.locationKey(
                            read.location()), read.observedVersion());
                    if (reads != null) reads.joined(read, write);
                    if (write == null) continue;
                    reach(write, anchor, start, reached, pending, versions,
                            handled);
                }
            }
            if (versions.isEmpty()) continue;
            WriteRow write = versions.remove(0);
            for (WriteRow under : log.writesOf(SmtLowering.locationKey(
                    write.location()))) {
                if (under.version() >= write.version()) continue;
                reach(under, anchor, start, reached, pending, versions,
                        handled);
            }
        }
        return reached;
    }

    /**
     * One write this path rests on (joined or an earlier version): its
     * writer is reached and its location's earlier versions queued.  An
     * INITIAL has neither: no occurrence wrote it.
     */
    private static void reach(WriteRow write, OccurrenceAddress anchor,
                              OccurrenceAddress start,
                              Map<String, Long> reached,
                              List<String> pending, List<WriteRow> versions,
                              Set<String> handled) {
        String writer = write.endpoint().occurrence().id();
        // Never the anchor or the start: their cutoff is fixed.
        if (write.initial() || anchor.id().equals(writer)
                || start.id().equals(writer)) {
            return;
        }
        if (handled.add(SmtLowering.locationKey(write.location()) + "#"
                + write.version())) {
            versions.add(write);
        }
        Long held = reached.get(writer);
        if (held != null && held.longValue() >= write.seq()) return;
        reached.put(writer, write.seq());
        pending.add(writer);
    }

    /** The decisions of every reached occurrence but the anchor, each
     *  before its cutoff: what {@link #closureConditions} may state. */
    List<DecisionRow> reachedConditions(String session,
                                        Map<String, Long> reached) {
        List<DecisionRow> conditions = new ArrayList<DecisionRow>();
        for (Map.Entry<String, Long> entry : reached.entrySet()) {
            if (anchor.id().equals(entry.getKey())) continue;
            OccurrenceAddress at = corpus.occurrence(entry.getKey());
            if (at == null) continue;
            conditions.addAll(before(corpus.decisionsOf(session, at),
                    entry.getValue().longValue()));
        }
        return conditions;
    }

    /** The decisions strictly before {@code seq}. */
    static List<DecisionRow> before(List<DecisionRow> decisions,
                                            long seq) {
        List<DecisionRow> earlier = new ArrayList<DecisionRow>();
        for (DecisionRow decision : decisions) {
            if (decision.seq() < seq) earlier.add(decision);
        }
        return earlier;
    }

    /** What {@code seeds} and the variables a family binds ({@code
     *  bound}) rest on among these conditions and the reads of the reached
     *  occurrences ({@link Independence}); a read brings the construction
     *  guard of the write it observed. */
    Independence independence(String session, List<String> seeds,
                              Collection<String> bound,
                              Map<String, Long> reached,
                              List<DecisionRow> conditions) {
        return Independence.of(corpus, session, seeds, bound, conditions,
                statedRows(session, reached.keySet()),
                read -> constructionGuards(session, corpus.writeOf(session,
                        read.location(), read.observedVersion())));
    }

    /** The construction guards already found, by session and write. */
    private final Map<String, List<DecisionRow>> built =
            new LinkedHashMap<String, List<DecisionRow>>();

    /**
     * THE CONSTRUCTION GUARD of a reference write (R3-REFCONT §1.6, D5):
     * the decisions its occurrence took before it at the guard sites of the
     * mutations its method made on a container it then published
     * ({@link StaticScopeMap#constructionGuards}).  A referent rests on
     * every decision that shaped it, the ones that skipped a mutation
     * included, and those leave no node in its state: an arm delivering the
     * write, or a read joined to it, conjoins them in the polarity they took
     * ({@link Independence} keeps them), and the reads they name are joined
     * in turn.  A decision whose condition guards a conditional mutation of
     * the referent's chain (REMOVE_IF, PUT_IF, APPEND_IF) stays free, as
     * that node states it both ways.  None for a write that stored no
     * container's state.
     */
    List<DecisionRow> constructionGuards(String session, WriteRow write) {
        if (write == null || write.referentState() == null) {
            return Collections.<DecisionRow>emptyList();
        }
        return built.computeIfAbsent(session + "|" + write.location() + "@"
                + write.version(), unused -> {
            String site = write.endpoint().site();
            Set<String> sites = new LinkedHashSet<String>();
            for (String carrier : scope.carriersAt(site,
                    write.javaType(), write.location().kind())) {
                for (StaticScopeMap.Guard guard
                        : scope.constructionGuards(site, carrier)) {
                    sites.add(guard.siteId());
                }
            }
            List<DecisionRow> guards = new ArrayList<DecisionRow>();
            if (sites.isEmpty()) return guards;
            Set<JsonElement> free = mutationGuards(session,
                    write.referentState());
            for (DecisionRow decision : corpus.decisionsOf(session,
                    write.endpoint().occurrence())) {
                if (decision.seq() < write.seq()
                        && sites.contains(decision.siteId())
                        && !decides(session, decision, free)) {
                    guards.add(decision);
                }
            }
            return guards;
        });
    }

    /**
     * The guards of the conditional mutations of one container's chain
     * ({@link ContainerSmtCodec#conditionalMutation}), down to its base:
     * each version's mutation and, through the read it rests on, the
     * version before.
     */
    private Set<JsonElement> mutationGuards(String session,
                                            WriteRow.Referent state) {
        Set<JsonElement> guards = ExpressionWalk.identitySet();
        Set<JsonElement> walked = ExpressionWalk.identitySet();
        List<JsonElement> pending = new ArrayList<JsonElement>();
        WriteRow first = corpus.writeOf(session, state.location(),
                state.version());
        if (first != null) {
            pending.add(corpus.expression(session, first.expressionRef()));
        }
        while (!pending.isEmpty()) {
            for (ExpressionWalk walk = ExpressionWalk.of(pending.remove(
                    pending.size() - 1), walked); walk.hasNext(); ) {
                JsonObject node = walk.next();
                String type = JsonFields.optionalString(node, "_type");
                if ("ContainerRelation".equals(type)
                        && ContainerSmtCodec.conditionalMutation(
                        JsonFields.optionalString(node, "operation"))) {
                    guards.add(unwrapped(node.get("guard")));
                } else if (VmRows.GUARDED_READ_TYPE.equals(type)) {
                    WriteRow below = corpus.writeOf(session,
                            SmtLowering.locationKey(JsonFields.object(node,
                                    "location")), VmRows.recordedVersion(
                                    node));
                    if (below != null) {
                        pending.add(corpus.expression(session,
                                below.expressionRef()));
                    }
                }
            }
        }
        return guards;
    }

    /**
     * Whether a decision's condition is one of these guards: the node
     * itself, or its complement over the same operands (the arm a removal
     * that did not fire states).
     */
    private boolean decides(String session, DecisionRow decision,
                            Set<JsonElement> guards) {
        if (guards.isEmpty()) return false;
        for (String reference : SmtNames.symbols(decision.term(),
                new LinkedHashSet<String>())) {
            JsonElement condition = unwrapped(corpus.expression(session,
                    reference));
            if (guards.contains(condition)) return true;
            for (JsonElement guard : guards) {
                if (condition != null && condition.isJsonObject()
                        && guard != null && guard.isJsonObject()
                        && condition.getAsJsonObject().get("_left")
                        == guard.getAsJsonObject().get("_left")
                        && condition.getAsJsonObject().get("_right")
                        == guard.getAsJsonObject().get("_right")) {
                    return true;
                }
            }
        }
        return false;
    }

    /** A value beneath the consumer boundaries around it. */
    static JsonElement unwrapped(JsonElement value) {
        JsonElement found = value;
        while (VmExpressionIr.consumerBoundary(found)) {
            found = found.getAsJsonObject().get(VmExpressionIr.EXPRESSION);
        }
        return found;
    }
}

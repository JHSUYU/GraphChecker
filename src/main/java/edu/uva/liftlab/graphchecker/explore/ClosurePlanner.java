package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The target's closure: what its failure can depend on, and the branches
 * exploration may flip in it (CLOSURE-V2 SS1-SS2).
 *
 * <p>Demand starts at the ANNOTATED TARGET: the fatal predicate's operands and
 * the target's guard set ({@link StaticScopeMap}). Deliveries no demanded value
 * rests on are not followed. Each boundary variable grows it:</p>
 * <ul>
 *   <li>by ROWS: the paired producer, the writers a read could have
 * observed;</li>
 *   <li>by the STATIC MAP: occurrences of regions holding a write/export
 *       site of that location/port -- what the recording cannot state (a writer
 *       the seed's arm never ran, e.g. hdfs-17960's deferred decrement);</li>
 *   <li>by STATED READS ({@link #statedReads}, E2): shared state a
 *       contributed value rests on appears only inside its expression.</li>
 * </ul>
 *
 * <p>Static candidates are ON ONE NODE: the READER's for a write site (N1,
 * {@link #writers}), the PAIRED PRODUCER's for an export site (N2, {@link
 * #producers}); a class field exists in every JVM, but only one heap or sender
 * is the real one. A candidate is flipped only at its own guards; a region no
 * session activated is named (INTERACTION-ID SS8 case 2), not a task.</p>
 */
public final class ClosurePlanner {
    /** How many tasks one anchor may open, before the closure is truncated. */
    public static final int DEFAULT_MAX_TASKS = 64;

    /** Connected by rows. */
    public static final String CLOSURE_MEMBER = "CLOSURE_MEMBER";
    /** Sent the message a member served. */
    public static final String CONTROL_PRODUCER = "CONTROL_PRODUCER";
    /** Holds a static write site of a demanded location. */
    public static final String STATIC_CANDIDATE_WRITER =
            "STATIC_CANDIDATE_WRITER";
    /** Holds a static export site of a demanded port. */
    public static final String STATIC_CANDIDATE_PRODUCER =
            "STATIC_CANDIDATE_PRODUCER";

    private ClosurePlanner() {
    }

    /** The closure of one anchor, and what could not be named in it. */
    public static final class Plan {
        public final List<Task> tasks;
        public final List<GapRow> gaps;
        /** task id -> why it is in the closure. */
        public final Map<String, String> why;
        /** task id -> site ids this wave may flip. */
        public final Map<String, Set<String>> flipSites;

        private Plan(List<Task> tasks, List<GapRow> gaps,
                     Map<String, String> why,
                     Map<String, Set<String>> flipSites) {
            this.tasks = Collections.unmodifiableList(tasks);
            this.gaps = Collections.unmodifiableList(gaps);
            this.why = Collections.unmodifiableMap(why);
            this.flipSites = Collections.unmodifiableMap(flipSites);
        }
    }

    public static Plan plan(Corpus corpus, OccurrenceAddress anchor,
                            int maxTasks, StaticScopeMap scope) {
        List<GapRow> gaps = new ArrayList<GapRow>();
        Map<String, Demand> demands = new LinkedHashMap<String, Demand>();
        Deque<String> pending = new ArrayDeque<String>();
        Demand start = new Demand(anchor, CLOSURE_MEMBER, true);
        // The anchor flips only the target's guard set (CLOSURE-V2 SS1); the
        // throw itself is no branch.
        for (StaticScopeMap.Site target : scope.targetSites()) {
            start.flipSites.addAll(target.guards);
        }
        demands.put(anchor.id(), start);
        pending.add(anchor.id());
        Set<String> truncated = new LinkedHashSet<String>();
        while (!pending.isEmpty()) {
            Demand demand = demands.get(pending.remove());
            demand.dirty = false;
            for (Demand next : successors(corpus, scope, demand, gaps)) {
                Demand held = demands.get(next.occurrence.id());
                if (held != null) {
                    if (held.absorb(next) && !held.dirty) {
                        held.dirty = true;
                        pending.add(held.occurrence.id());
                    }
                    continue;
                }
                if (demands.size() >= maxTasks) {
                    truncated.add(next.occurrence.render());
                    continue;
                }
                demands.put(next.occurrence.id(), next);
                pending.add(next.occurrence.id());
            }
        }
        if (!truncated.isEmpty()) {
            // A truncated closure misses arms: unsound, so BLOCKING, naming
            // what was left out.
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION, GapKind.ADMISSION_GAP,
                    GapClass.BLOCKING, anchor.render(),
                    "closure truncated at " + maxTasks + " tasks; "
                            + truncated.size() + " occurrences were not "
                            + "planned, so this anchor's closure is "
                            + "incomplete: " + truncated));
        }
        List<Task> tasks = new ArrayList<Task>();
        Map<String, String> why = new LinkedHashMap<String, String>();
        Map<String, Set<String>> flips =
                new LinkedHashMap<String, Set<String>>();
        for (Demand demand : demands.values()) {
            String seed = seedSession(corpus, demand.occurrence);
            if (seed.isEmpty()) {
                // No session ran it: no replay to focus; BLOCKING, as an
                // unattested arm.
                gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                        GapKind.ADMISSION_GAP, GapClass.BLOCKING,
                        demand.occurrence.render(),
                        "no session of this corpus activated this occurrence "
                                + "or recorded a decision of it, so no replay "
                                + "can be focused on it and it is not a task"));
                continue;
            }
            String taskId = taskId(demand.occurrence);
            tasks.add(Task.of(taskId, demand.occurrence,
                    stateConnected(corpus, demand.occurrence), seed));
            why.put(taskId, demand.why);
            // Flip sites: the demanded guards plus every FAULT decision
            // (DESIGN4 SS1.4).
            Set<String> sites = new LinkedHashSet<String>(demand.flipSites);
            sites.addAll(corpus.faultSites(demand.occurrence));
            flips.put(taskId, sites);
        }
        return new Plan(tasks, gaps, why, flips);
    }

    /** One task's id: the occurrence it focuses and nothing else. */
    public static String taskId(OccurrenceAddress focused) {
        return ArtifactIO.digest("task|" + focused.id(), 16);
    }

    /** The task one published obligation names, recovered from the corpus. */
    public static Task taskOf(Corpus corpus, String taskId) {
        if (taskId == null || taskId.isEmpty()) return null;
        for (OccurrenceAddress occurrence : corpus.occurrences()) {
            if (!taskId.equals(taskId(occurrence))) continue;
            String seed = seedSession(corpus, occurrence);
            // The wave published no task for it (BLOCKING gap), so none here
            // either.
            if (seed.isEmpty()) return null;
            return Task.of(taskId, occurrence, stateConnected(corpus,
                    occurrence), seed);
        }
        return null;
    }

    /** What one occurrence is demanded for, and where its flips may be. */
    private static final class Demand {
        private final OccurrenceAddress occurrence;
        /** session|expressionRef of values this occurrence contributed. */
        private final Set<String> contributed = new LinkedHashSet<String>();
        private final Set<String> flipSites = new LinkedHashSet<String>();
        private final boolean anchor;
        private String why;
        private boolean dirty;

        private Demand(OccurrenceAddress occurrence, String why,
                       boolean anchor) {
            this.occurrence = occurrence;
            this.why = why;
            this.anchor = anchor;
        }

        /**
         * Folds another reason to demand this occurrence; {@code
         * CLOSURE_MEMBER} wins over static reasons.
         *
         * @return whether this demand grew
         */
        private boolean absorb(Demand other) {
            boolean grew = contributed.addAll(other.contributed);
            grew |= flipSites.addAll(other.flipSites);
            if (CLOSURE_MEMBER.equals(other.why)
                    && !CLOSURE_MEMBER.equals(why)) {
                why = CLOSURE_MEMBER;
                grew = true;
            }
            return grew;
        }
    }

    /** Everything one demand reaches, by rows and by the static map. */
    private static List<Demand> successors(Corpus corpus, StaticScopeMap map,
                                           Demand demand, List<GapRow> gaps) {
        List<OccurrenceAddress> group = new ArrayList<OccurrenceAddress>();
        group.add(demand.occurrence);
        group.addAll(stateConnected(corpus, demand.occurrence));
        // The group (occurrence + state-connected factor) is ONE symbolic unit:
        // demand is asked of the group, not each member.
        Set<String> demanded = demanded(corpus, demand, group);
        List<Demand> next = new ArrayList<Demand>();
        for (OccurrenceAddress member : group) {
            if (!member.equals(demand.occurrence)) {
                // A factor member inherits the reason; being a factor is not
                // its own.
                next.add(new Demand(member, demand.why, false));
            }
            for (AttachRow attach : corpus.attachesOn(member)) {
                if (!demanded.contains(attach.symbol())) {
                    unread(gaps, attach.sessionId(), attach.endpoint()
                            .toString(), "handoff");
                    continue;
                }
                producers(corpus, map, attach, next, gaps);
            }
            for (ReadRow row : corpus.readsOn(member)) {
                if (!demanded.contains(row.symbol())) {
                    unread(gaps, row.sessionId(), row.endpoint().toString(),
                            "state read");
                    continue;
                }
                writers(corpus, map, row, next, gaps);
            }
        }
        statedReads(corpus, map, demand, next, gaps);
        controlProducer(corpus, demand, next);
        return next;
    }

    /** Both doors of the message a demanded occurrence served join as control
     *  producers: they contribute no value, but their fault points decide
     *  whether the message exists (DESIGN4 SS1.2, SS1.4). Paired via the served
     *  occurrence's ANCHOR (the producer endpoint). */
    private static void controlProducer(Corpus corpus, Demand demand,
                                        List<Demand> next) {
        if (!(demand.occurrence.context() instanceof CausalContext.Anchor)) {
            return;
        }
        String endpoint = ((CausalContext.Anchor) demand.occurrence.context())
                .producerEndpointId();
        for (OccurrenceAddress door : new OccurrenceAddress[] {
                corpus.senderOf(endpoint), corpus.receiverOf(endpoint)}) {
            if (door == null || door.equals(demand.occurrence)) continue;
            next.add(new Demand(door, CONTROL_PRODUCER, false));
        }
    }

    /**
     * E2 -- A DEMANDED EXPORT STATES THE SHARED STATE IT RESTS ON.
     *
     * <p>The VM publishes a contributed value's shared-state reads only inside
     * its expression; no ReadRow names them. Each resolved read grows the
     * closure like a read row (writer of that version, static write sites on
     * the producer's node, N1); writers recurse the same way. {@link
     * Corpus#expressionStateReads} is the one resolution, shared with {@code
     * ComposedFamilies.expressionWrites}. Never the anchor (it contributes no
     * delivery).</p>
     */
    private static void statedReads(Corpus corpus, StaticScopeMap map,
                                    Demand demand, List<Demand> into,
                                    List<GapRow> gaps) {
        if (demand.anchor) return;
        for (String contributed : demand.contributed) {
            int split = contributed.indexOf('|');
            if (split < 0) continue;
            String sessionId = contributed.substring(0, split);
            for (Corpus.StateRead read : corpus.expressionStateReads(
                    sessionId, contributed.substring(split + 1))) {
                writersOfVersion(corpus, map, sessionId, demand.occurrence,
                        read.locationKey(), read.write().version(),
                        demand.occurrence.render(),
                        read.locationKey() + " (read at event "
                                + read.readEventId() + ")", into, gaps);
            }
        }
    }

    /** The symbols one occurrence's demanded values name: the anchor's fatal
     *  predicate, decisions at its guard-set sites, and its contributed
     *  expressions -- then the fixed point over reads and the writes they could
     *  observe. Terms are EXPR references, resolved by the ONE lowering
     *  (CONTRACT-SPEC). */
    private static Set<String> demanded(Corpus corpus, Demand demand,
                                        List<OccurrenceAddress> group) {
        Set<String> named = new LinkedHashSet<String>();
        List<ReadRow> reads = new ArrayList<ReadRow>();
        for (OccurrenceAddress member : group) {
            for (Corpus.RecordedPath path : corpus.pathsOf(member)) {
                for (DecisionRow decision : path.decisions) {
                    if (!demand.flipSites.contains(decision.siteId())) {
                        continue;
                    }
                    reaches(corpus, path.sessionId, FlipQuery.statedTerm(
                            corpus, path.sessionId, decision.term()), named);
                }
            }
            if (demand.anchor) {
                for (TargetRow target : corpus.targetsOn(member)) {
                    reaches(corpus, target.sessionId(),
                            FlipQuery.statedTerm(corpus, target.sessionId(),
                                    target.phiTerm()), named);
                }
            }
            reads.addAll(corpus.readsOn(member));
        }
        for (String contributed : demand.contributed) {
            int split = contributed.indexOf('|');
            if (split < 0) continue;
            String sessionId = contributed.substring(0, split);
            SmtLowering lowering = corpus.lowering(sessionId);
            if (lowering == null) continue;
            reaches(corpus, sessionId, lowering.lower(
                    contributed.substring(split + 1)).text(), named);
        }
        Set<String> settled = new LinkedHashSet<String>();
        boolean grew = true;
        while (grew) {
            grew = false;
            for (String symbol : new ArrayList<String>(named)) {
                if (!settled.add(symbol)) continue;
                for (ReadRow row : reads) {
                    if (!symbol.equals(row.symbol())) continue;
                    for (WriteRow write : corpus.eligibleWrites(
                            row.sessionId(),
                            SmtLowering.locationKey(row.location()),
                            row.observedVersion(),
                            row.endpoint().occurrence())) {
                        grew |= reaches(corpus, write.sessionId(),
                                corpus.lowering(write.sessionId())
                                        .lower(write.expressionRef()).text(),
                                named);
                    }
                }
            }
        }
        return named;
    }

    /**
     * The recorded symbols one lowered term REACHES (not merely spells), into
     * {@code named}: {@link SmtLowering#reachedSymbols}, as the flip query
     * uses. Trap: {@code SmtLowering.symbols} sees only a {@code
     * container_dag__} name that matches no row. Includes the state behind a
     * container name (the v_C rule, CLOSURE-V2).
     *
     * @return whether the set grew
     */
    private static boolean reaches(Corpus corpus, String sessionId,
                                   String text, Set<String> named) {
        SmtLowering lowering = corpus.lowering(sessionId);
        if (lowering == null) return false;
        Set<String> reached = new LinkedHashSet<String>();
        lowering.reachedSymbols(text, reached, reached);
        return named.addAll(reached);
    }

    /** A delivery this anchor's paths never read: recorded, not planned. */
    private static void unread(List<GapRow> gaps, String sessionId,
                               String subject, String what) {
        gaps.add(GapRow.of(sessionId, GapKind.ADMISSION_GAP,
                GapClass.DIAGNOSTIC, subject,
                "no demanded value of this occurrence rests on this " + what
                        + ", so its producer is not a task"));
    }

    /**
     * Who could have produced one demanded attach: the paired endpoint, and the
     * port's static export sites. Nested handoffs need no walk: the producer is
     * demanded for its export, and its own attaches follow.
     *
     * <p><b>N2 -- a message was sent by ONE process:</b> static candidates only
     * on the paired producer's node. An unpaired attach restricts nothing (and
     * is reported LINEAGE_LOST).</p>
     */
    private static void producers(Corpus corpus, StaticScopeMap map,
                                  AttachRow attach, List<Demand> into,
                                  List<GapRow> gaps) {
        String portId = attach.endpoint().site();
        List<StaticScopeMap.Site> exports = map.exportsOf(portId);
        Set<String> guards = new LinkedHashSet<String>();
        for (StaticScopeMap.Site site : exports) {
            guards.addAll(site.guards);
        }
        if (attach.producer() == null) {
            gaps.add(GapRow.of(attach.sessionId(), GapKind.LINEAGE_LOST,
                    GapClass.DIAGNOSTIC, attach.endpoint().toString(),
                    "attach is unpaired: no producer endpoint to close over"));
        } else {
            crossCheck(attach, gaps);
            Demand paired = new Demand(attach.producer().occurrence(),
                    CLOSURE_MEMBER, false);
            paired.flipSites.addAll(guards);
            for (ExportRow export : corpus.exportsOf(attach.producer())) {
                paired.contributed.add(export.sessionId() + "|"
                        + export.expressionRef());
            }
            into.add(paired);
        }
        // N2: null (unpaired) means every node.
        NodeId sender = attach.producer() == null ? null
                : attach.producer().occurrence().node();
        for (StaticScopeMap.Site site : exports) {
            candidates(corpus, map, site, STATIC_CANDIDATE_PRODUCER, guards,
                    into, gaps, attach.sessionId(), "port " + portId, sender);
        }
    }

    /**
     * Who could have written one demanded read: the eligible row writers, and
     * the static write sites of its carrier (joined through a write the
     * recording did observe; no such write = no carrier, said).
     *
     * <p><b>N1 -- a concrete location lives in ONE process:</b> static
     * candidates only on the reader's node (Writers_W(l) is per concrete
     * object, SS4).</p>
     */
    private static void writers(Corpus corpus, StaticScopeMap map,
                                ReadRow row, List<Demand> into,
                                List<GapRow> gaps) {
        writersOfVersion(corpus, map, row.sessionId(),
                row.endpoint().occurrence(),
                SmtLowering.locationKey(row.location()),
                row.observedVersion(), row.endpoint().toString(),
                String.valueOf(row.location()), into, gaps);
    }

    /**
     * The closure's growth by one read of one version of one location, whether
     * the runtime stated it as a row or only in an expression (E2).
     *
     * @param subject what a diagnostic about this read is addressed at
     * @param located how the location reads in that diagnostic
     */
    private static void writersOfVersion(Corpus corpus, StaticScopeMap map,
                                         String sessionId,
                                         OccurrenceAddress reader,
                                         String locationKey,
                                         long observedVersion,
                                         String subject, String located,
                                         List<Demand> into,
                                         List<GapRow> gaps) {
        Set<String> carriers = carriersOf(corpus, map, locationKey);
        for (WriteRow write : corpus.eligibleWrites(sessionId, locationKey,
                observedVersion, reader)) {
            Demand paired = new Demand(write.endpoint().occurrence(),
                    CLOSURE_MEMBER, false);
            paired.contributed.add(write.sessionId() + "|"
                    + write.expressionRef());
            paired.flipSites.addAll(guardsAt(map, write.endpoint().site()));
            into.add(paired);
        }
        if (carriers.isEmpty() && map.stated()) {
            gaps.add(GapRow.of(sessionId, GapKind.DECLARATION_MISSING,
                    GapClass.DIAGNOSTIC, subject,
                    "no recorded write of " + located + " matches a "
                            + "write site of the static map, so this "
                            + "location's carrier is unnamed and no static "
                            + "candidate writer of it can be"));
            return;
        }
        // N1: the heap this read observed is the reader JVM's.
        for (String carrier : carriers) {
            for (StaticScopeMap.Site site : map.writersOf(carrier)) {
                candidates(corpus, map, site, STATIC_CANDIDATE_WRITER,
                        new LinkedHashSet<String>(site.guards), into, gaps,
                        sessionId, "carrier " + carrier, reader.node());
            }
        }
    }

    /** Every carrier the static map names for one location key. */
    private static Set<String> carriersOf(Corpus corpus, StaticScopeMap map,
                                          String locationKey) {
        Set<String> carriers = new LinkedHashSet<String>();
        for (SessionReader session : corpus.sessions()) {
            for (WriteRow write : corpus.writesOf(session.sessionId(),
                    locationKey)) {
                carriers.addAll(map.carriersAt(write.endpoint().site(),
                        write.javaType()));
            }
        }
        return carriers;
    }

    /** A writer's flip sites: guards of every static write site in the METHOD
     *  it wrote from (bci vs unit index do not compare); may be one too many.
     */
    private static Set<String> guardsAt(StaticScopeMap map,
                                        String recordedSite) {
        Set<String> guards = new LinkedHashSet<String>();
        for (StaticScopeMap.Site site : map.sitesAt(recordedSite)) {
            guards.addAll(site.guards);
        }
        return guards;
    }

    /** Every activated occurrence of the region holding one static site, on
     *  {@code node} (N1/N2; null = any). None: named (INTERACTION-ID SS8 case
     *  2), scoped to that node, and no task. */
    private static void candidates(Corpus corpus, StaticScopeMap map,
                                   StaticScopeMap.Site site,
                                   String why, Set<String> guards,
                                   List<Demand> into, List<GapRow> gaps,
                                   String sessionId, String what,
                                   NodeId node) {
        boolean ran = false;
        for (OccurrenceAddress occurrence : corpus.occurrences()) {
            if (!holds(map, occurrence.regionId(), site)
                    || (node != null && !node.equals(occurrence.node()))
                    || !activated(corpus, occurrence)) {
                continue;
            }
            ran = true;
            Demand candidate = new Demand(occurrence, why, false);
            candidate.flipSites.addAll(guards);
            into.add(candidate);
        }
        if (ran) return;
        gaps.add(GapRow.of(sessionId, GapKind.ADMISSION_GAP,
                GapClass.DIAGNOSTIC, site.regionId,
                "a static " + (STATIC_CANDIDATE_WRITER.equals(why)
                        ? "write" : "export") + " site of " + what + " is in "
                        + site.siteId + ", and no session of this corpus "
                        + "activated that region"
                        + (node == null ? "" : " on " + node.render())
                        + ": the retained set would have "
                        + "to grow before it can be a task (INTERACTION-ID "
                        + "SS8 case 2)"));
    }

    /** Whether an occurrence's region would RUN a static site: by HOLDING its
     *  method, not region-id equality. Under the fold rule a site of R is
     *  recorded under an enclosing R', while the map names only the innermost
     *  holder. Falls back to id equality when the map knows no method set. */
    private static boolean holds(StaticScopeMap map, String regionId,
                                 StaticScopeMap.Site site) {
        Set<String> methods = map == null
                ? Collections.<String>emptySet() : map.methodsOf(regionId);
        return methods.isEmpty()
                ? site.regionId.equals(regionId)
                : methods.contains(SiteId.methodOf(site.siteId));
    }

    /** Whether some session of this corpus ran one occurrence. */
    private static boolean activated(Corpus corpus,
                                     OccurrenceAddress occurrence) {
        for (SessionReader session : corpus.sessions()) {
            if (corpus.activation(session.sessionId(), occurrence) != null) {
                return true;
            }
        }
        return false;
    }

    /** Cross-checks the recorded pairing against the consumer's Anchor context
     *  (identity v3 states it twice). The row is authoritative; a mismatch is
     *  the runtime's defect, reported. Root/Lost contexts raise nothing. */
    private static void crossCheck(AttachRow attach, List<GapRow> gaps) {
        CausalContext context = attach.endpoint().occurrence().context();
        if (!(context instanceof CausalContext.Anchor)) return;
        String anchored = ((CausalContext.Anchor) context)
                .producerEndpointId();
        String recorded = attach.producer().id();
        if (anchored.equals(recorded)) return;
        gaps.add(GapRow.of(attach.sessionId(), GapKind.TOPOLOGY_DIVERGENCE,
                GapClass.DIAGNOSTIC, attach.endpoint().toString(),
                "the recorded pairing names producer endpoint " + recorded
                        + " and the consumer's causal anchor names "
                        + anchored + "; the closure follows the recorded "
                        + "pairing"));
    }

    /** Co-occurrences state-connected to one occurrence (writers/readers of its
     *  locations). */
    private static List<OccurrenceAddress> stateConnected(
            Corpus corpus, OccurrenceAddress occurrence) {
        Set<LocationId> locations = new LinkedHashSet<LocationId>();
        for (ReadRow read : corpus.readsOn(occurrence)) {
            locations.add(read.location());
        }
        for (WriteRow write : corpus.writesOn(occurrence)) {
            locations.add(write.location());
        }
        Set<String> connected = new LinkedHashSet<String>();
        for (LocationId location : locations) {
            connected.addAll(corpus.touching(occurrence, location));
        }
        connected.remove(occurrence.id());
        List<OccurrenceAddress> factor = new ArrayList<OccurrenceAddress>();
        for (String id : connected) {
            OccurrenceAddress member = corpus.occurrence(id);
            if (member != null) factor.add(member);
        }
        return factor;
    }

    /** The session a task is planned from: the SEED if it ran the occurrence,
     *  else the first ADMITTED one that did, else "". */
    private static String seedSession(Corpus corpus,
                                      OccurrenceAddress occurrence) {
        String seed = corpus.seedSessionId();
        if (!seed.isEmpty() && ran(corpus, seed, occurrence)) return seed;
        for (SessionReader session : corpus.sessions()) {
            if (session.admitted()
                    && ran(corpus, session.sessionId(), occurrence)) {
                return session.sessionId();
            }
        }
        return "";
    }

    /** Whether one session activated or decided at one occurrence. */
    private static boolean ran(Corpus corpus, String sessionId,
                               OccurrenceAddress occurrence) {
        return corpus.activation(sessionId, occurrence) != null
                || !corpus.decisionsOf(sessionId, occurrence).isEmpty();
    }
}

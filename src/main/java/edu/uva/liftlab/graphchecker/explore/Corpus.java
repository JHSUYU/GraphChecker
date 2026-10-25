package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.ByIdentity;
import edu.uva.liftlab.graphchecker.contract.ContentPort;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.JvmNames;
import edu.uva.liftlab.graphchecker.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.Flip;
import edu.uva.liftlab.graphchecker.contract.FrozenSet;
import edu.uva.liftlab.graphchecker.contract.Held;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Parallel;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.contract.RootDomain;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowOrder;
import edu.uva.liftlab.graphchecker.contract.RowHold;
import edu.uva.liftlab.graphchecker.contract.RunSpellings;
import edu.uva.liftlab.graphchecker.contract.Task;
import com.google.common.collect.Interner;
import com.google.common.collect.Interners;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.JavaSmtSorts;
import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.compose.SmtNames;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.ExpressionWalk;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.smt.VmRows;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.WorldRefutation;
import edu.uva.liftlab.graphchecker.contract.WriteRow;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.AbstractSet;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.DoubleSupplier;
import java.util.function.Supplier;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public final class Corpus implements Arms.Rows {
    public static final class RecordedPath {
        public final String pathId;
        public final String sessionId;
        public final OccurrenceAddress occurrence;
        public final List<DecisionRow> decisions;

        private RecordedPath(String sessionId, OccurrenceAddress occurrence,
                             List<DecisionRow> decisions) {
            this.pathId = pathId(sessionId, occurrence);
            this.sessionId = sessionId;
            this.occurrence = occurrence;
            this.decisions = Collections.unmodifiableList(decisions);
        }
    }

    public enum SymbolKind { ROOT, HANDOFF, READ, UNKNOWN }

    public static final class World {
        public final Map<String, String> rootAssignments;
        public final Map<String, String> clockDeltas;
        public final Map<String, String> answers;
        public final Map<String, String> pairings;
        public final List<Flip> flips;

        World(Map<String, String> rootAssignments,
              Map<String, String> clockDeltas,
              Map<String, String> answers,
              Map<String, String> pairings,
              List<Flip> flips) {
            this.rootAssignments =
                    Collections.unmodifiableMap(rootAssignments);
            this.clockDeltas = Collections.unmodifiableMap(clockDeltas);
            this.answers = Collections.unmodifiableMap(answers);
            this.pairings = Collections.unmodifiableMap(pairings);
            this.flips = Collections.unmodifiableList(flips);
        }

        static World empty() {
            return new World(new LinkedHashMap<String, String>(),
                    new LinkedHashMap<String, String>(),
                    new LinkedHashMap<String, String>(),
                    new LinkedHashMap<String, String>(),
                    new ArrayList<Flip>());
        }
    }

    private final Path iteration;
    private final List<SessionReader> sessions;
    private final Map<String, SessionReader> sessionById =
            new LinkedHashMap<String, SessionReader>();
    private final Set<String> clientNodes = ConcurrentHashMap.newKeySet();
    private final Map<String, SmtLowering> loweringById =
            new ConcurrentHashMap<String, SmtLowering>();
    private final RowHold hold;
    private final Map<String, Derived> bySession =
            new LinkedHashMap<String, Derived>();
    private final Map<String, List<ActivationRow>> activations =
            new LinkedHashMap<String, List<ActivationRow>>();
    private final Map<String, List<ExportRow>> exports =
            new LinkedHashMap<String, List<ExportRow>>();
    private final Set<String> handoffSymbols = new LinkedHashSet<String>();
    private final ByOccurrence<AttachRow> attachesOn =
            new ByOccurrence<AttachRow>();
    private final ByOccurrence<TargetRow> targetsOn =
            new ByOccurrence<TargetRow>();
    private final Map<String, Set<String>> readersOn =
            new LinkedHashMap<String, Set<String>>();
    private final Map<String, Set<String>> writersOn =
            new LinkedHashMap<String, Set<String>>();
    private final Map<String, Set<String>> readLocations =
            new LinkedHashMap<String, Set<String>>();
    private final Map<String, Set<String>> writtenLocations =
            new LinkedHashMap<String, Set<String>>();
    private final Map<String, Map<List<String>, WriteRow>>
            writeSitesByLocation =
            new LinkedHashMap<String, Map<List<String>, WriteRow>>();
    private final Map<String, List<AttachRow>> attachesByInteraction =
            new LinkedHashMap<String, List<AttachRow>>();
    private final Map<String, Interaction> interactions =
            new LinkedHashMap<String, Interaction>();
    private final Map<String, Sort> declaredSymbols =
            new LinkedHashMap<String, Sort>();
    private final Map<String, Boolean> varied =
            new ConcurrentHashMap<String, Boolean>();
    private final Map<String, Boolean> derived =
            new ConcurrentHashMap<String, Boolean>();
    private Map<String, List<RootMintRow>> roots;
    private final Map<String, Set<String>> rootIdsBySymbol =
            new LinkedHashMap<String, Set<String>>();
    private final Map<String, OccurrenceAddress> occurrenceByEndpoint =
            new HashMap<String, OccurrenceAddress>();
    private final Map<String, Set<String>> locationTouches =
            new LinkedHashMap<String, Set<String>>();
    private final Map<String, Map<String, RootMintRow>> rootsById =
            new LinkedHashMap<String, Map<String, RootMintRow>>();
    private final Map<String, OccurrenceAddress> occurrenceById =
            new LinkedHashMap<String, OccurrenceAddress>();
    private final Map<String, Set<String>> occurrencesByStance =
            new HashMap<String, Set<String>>();
    private final Map<String, Set<String>> namedBy =
            new LinkedHashMap<String, Set<String>>();
    private final Map<String, Seen> seen = new HashMap<String, Seen>();
    private final Map<String, RootDomain> declaredDomains =
            new LinkedHashMap<String, RootDomain>();

    private final Map<String, World> worlds =
            new LinkedHashMap<String, World>();

    public static final class Refuted {
        public final String obligationId;
        public final String sessionId;
        public final World world;
        public final String digest;
        public final WorldRefutation refutation;

        Refuted(String obligationId, String sessionId, World world,
                WorldRefutation refutation) {
            this.obligationId = obligationId;
            this.sessionId = sessionId;
            this.world = world;
            this.digest = ObligationFactory.wholeWorldDigest(world);
            this.refutation = refutation;
        }
    }

    private final Map<String, List<Refuted>> refuted =
            new LinkedHashMap<String, List<Refuted>>();
    private final Map<String, Map<String, ObligationResult>> waveVerdicts =
            new LinkedHashMap<String, Map<String, ObligationResult>>();
    private final Map<String, Path> landedIn =
            new LinkedHashMap<String, Path>();
    private final Map<String, ContextShape.Stance> senderStanceByEndpoint =
            new HashMap<String, ContextShape.Stance>();
    private final Map<String, String> senderByEndpoint =
            new LinkedHashMap<String, String>();
    private final Map<String, String> receiverByEndpoint =
            new LinkedHashMap<String, String>();
    private final Map<String, Set<String>> receivingStances =
            new LinkedHashMap<String, Set<String>>();
    private final Map<String, Set<String>> handlerStances =
            new LinkedHashMap<String, Set<String>>();
    private final Map<String, Set<String>> takenInByStance =
            new HashMap<String, Set<String>>();
    private final Map<String, Set<String>> sentByOccurrence =
            new HashMap<String, Set<String>>();
    private final Map<String, Set<String>> repliesByRequest =
            new HashMap<String, Set<String>>();
    private final Map<String, Set<String>> readersByEndpoint =
            new HashMap<String, Set<String>>();

    private final Arms arms;

    private final List<SessionReader> forcedSessions;
    private final Map<String, Long> forcedFrom = new HashMap<String, Long>();

    private static final class Derived {
        final SessionReader session;
        volatile StateRows state;
        final List<Fact> schedule;
        final Map<String, Set<String>> symbolsByExpression =
                new ConcurrentHashMap<String, Set<String>>();
        final Map<String, Set<String>> leaves =
                new ConcurrentHashMap<String, Set<String>>();
        final Map<String, Set<String>> readLocations =
                new ConcurrentHashMap<String, Set<String>>();
        final Map<String, Set<Long>> readEvents =
                new ConcurrentHashMap<String, Set<Long>>();
        final Set<Long> sharedSeqs;
        final Map<String, ReadRow> sharedBy =
                new ConcurrentHashMap<String, ReadRow>();
        final Map<String, ActivationRow> activationByOccurrence =
                new HashMap<String, ActivationRow>();
        final Map<String, List<DecisionRow>> decisions =
                new LinkedHashMap<String, List<DecisionRow>>();
        final Map<String, AttachRow> attachBySymbol =
                new HashMap<String, AttachRow>();
        final Map<String, RootMintRow> rootBySymbol =
                new LinkedHashMap<String, RootMintRow>();
        final Map<String, List<AttachRow>> ownAttaches =
                new HashMap<String, List<AttachRow>>();
        final Map<String, List<ExportRow>> ownExports =
                new HashMap<String, List<ExportRow>>();

        Derived(SessionReader session, boolean state) {
            this.session = session;
            this.state = state ? new StateRows(session) : null;
            this.schedule = facts(session);
            for (ActivationRow row : session.activations()) {
                activationByOccurrence.putIfAbsent(row.occurrence().id(),
                        row);
            }
            for (DecisionRow row : session.decisions()) {
                add(decisions, row.occurrence().id(), row);
            }
            Held.trimmed(decisions);
            for (AttachRow row : session.attaches()) {
                attachBySymbol.put(row.symbol(), row);
            }
            for (RootMintRow row : session.roots()) {
                rootBySymbol.put(row.symbol(), row);
            }
            if (session.forced()) {
                long world = Long.MAX_VALUE;
                for (TargetRow row : session.targets()) {
                    if (row.isForced()) world = Math.min(world, row.seq());
                }
                for (ExportRow row : session.exports()) {
                    if (row.seq() < world) {
                        add(ownExports, row.endpoint().id(), row);
                    }
                }
                for (AttachRow row : session.attaches()) {
                    if (row.interaction() != null && row.seq() < world) {
                        add(ownAttaches, row.interaction().id(), row);
                    }
                }
            }
            Set<Long> seen = new HashSet<Long>();
            Set<Long> shared = new HashSet<Long>();
            for (ReadRow read : session.reads()) {
                if (read != null && !seen.add(read.seq())) {
                    shared.add(read.seq());
                }
            }
            this.sharedSeqs = shared;
        }
    }

    private static final class StateRows {
        final SmtLowering.SessionJoin join;
        final Map<String, ReadRow> readBySymbol =
                new HashMap<String, ReadRow>();
        final Map<String, List<ReadRow>> readsOn =
                new HashMap<String, List<ReadRow>>();
        final Map<String, List<WriteRow>> writesOn =
                new HashMap<String, List<WriteRow>>();
        final Map<String, List<WriteRow>> eligible =
                new ConcurrentHashMap<String, List<WriteRow>>();
        final Map<String, List<StateRead>> stateReads =
                new ConcurrentHashMap<String, List<StateRead>>();

        private StateRows() {
            this.join = SmtLowering.NO_JOIN;
        }

        StateRows(SessionReader session) {
            this.join = SmtLowering.joinOf(session);
            for (WriteRow row : session.writes()) {
                add(writesOn, row.endpoint().occurrence().id(), row);
            }
            for (ReadRow row : session.reads()) {
                if (!row.symbol().isEmpty()) {
                    readBySymbol.put(row.symbol(), row);
                }
                add(readsOn, row.endpoint().occurrence().id(), row);
            }
            Held.trimmed(readsOn);
            Held.trimmed(writesOn);
        }
    }

    private static final StateRows NO_STATE = new StateRows();

    private StateRows state(String sessionId) {
        Derived of = bySession.get(sessionId);
        if (of == null) return NO_STATE;
        StateRows held = of.state;
        if (held != null) {
            if (hold != null) hold.used(of.session);
            return held;
        }
        synchronized (of) {
            held = of.state;
            if (held == null) {
                held = new StateRows(of.session);
                of.state = held;
            }
        }
        return held;
    }

    private static final class Fact {
        enum Kind { TAKEN_IN, SENDER_STANCE, SENDER, RECEIVER,
            RECEIVING_STANCE, HANDLER_STANCE, REPLY }

        final Kind kind;
        final String key;
        final String occurrence;
        final ContextShape.Stance stance;

        Fact(Kind kind, String key, String occurrence,
             ContextShape.Stance stance) {
            this.kind = kind;
            this.key = key;
            this.occurrence = occurrence;
            this.stance = stance;
        }
    }

    private Corpus(Path iteration, List<SessionReader> read,
                   Corpus previous) {
        this.iteration = iteration;
        this.hold = null;
        List<SessionReader> real = new ArrayList<SessionReader>();
        List<SessionReader> forced = new ArrayList<SessionReader>();
        for (SessionReader session : read) {
            if (!session.forced()) {
                real.add(session);
            } else if (forcedTarget(session)) {
                forced.add(session);
            }
        }
        this.sessions = Collections.unmodifiableList(real);
        this.forcedSessions = Collections.unmodifiableList(forced);
        List<SessionReader> every = new ArrayList<SessionReader>(real);
        every.addAll(forced);
        List<Derived> derived = derived(every, previous);
        for (int at = 0; at < every.size(); at++) {
            bySession.put(every.get(at).sessionId(), derived.get(at));
            index(derived.get(at), at >= real.size());
        }
        this.arms = new Arms(this);
    }

    private Corpus(Path iteration, List<SessionDir> dirs,
                   DoubleSupplier swept) throws IOException {
        this.iteration = iteration;
        this.hold = new RowHold(swept, this::released);
        List<SessionReader> real = new ArrayList<SessionReader>();
        List<Derived> forced = new ArrayList<Derived>();
        SessionReader.Pooled reader = new SessionReader.Pooled();
        List<Derived> read = derived(reader, dirs, 0);
        for (int from = 0; from < dirs.size(); from += Parallel.READS) {
            int next = from + Parallel.READS;
            List<List<Derived>> ahead = new ArrayList<List<Derived>>();
            Parallel.Beside reading = Parallel.beside("corpus-read",
                    () -> ahead.add(derived(reader, dirs, next)));
            try {
                for (Derived of : read) {
                    if (of.session.forced()) {
                        if (forcedTarget(of.session)) forced.add(of);
                        continue;
                    }
                    real.add(of.session);
                    indexHeld(of, false);
                }
            } finally {
                reading.await();
            }
            reading.join();
            read = ahead.get(0);
        }
        List<SessionReader> apart = new ArrayList<SessionReader>();
        for (Derived of : forced) {
            apart.add(of.session);
            indexHeld(of, true);
        }
        this.sessions = Collections.unmodifiableList(real);
        this.forcedSessions = Collections.unmodifiableList(apart);
        this.arms = new Arms(this);
    }

    private static List<Derived> derived(SessionReader.Pooled reader,
                                         List<SessionDir> dirs, int from)
            throws IOException {
        if (from >= dirs.size()) return Collections.<Derived>emptyList();
        return Parallel.map(dirs.subList(from, Math.min(dirs.size(),
                from + Parallel.READS)), dir -> {
            SessionReader session = reader.read(dir);
            digestIds(session);
            return new Derived(session, false);
        }, Parallel.READS);
    }

    private void indexHeld(Derived of, boolean apart) {
        bySession.put(of.session.sessionId(), of);
        index(of, apart);
        hold.take(of.session);
    }

    public static Corpus holding(Path iteration, Path rootDomains,
                                 DoubleSupplier swept) throws IOException {
        Corpus corpus = new Corpus(iteration,
                SessionDir.sessionsIn(iteration), swept);
        corpus.domains(rootDomains);
        corpus.indexWorlds(iteration);
        corpus.indexRecordedTicks(iteration);
        corpus.uncaptured.addAll(SessionDir.uncaptured(iteration));
        return corpus;
    }

    private void released(SessionReader session) {
        Derived of = bySession.get(session.sessionId());
        if (of != null && of.session == session) of.state = null;
        loweringById.remove(session.sessionId());
    }

    public long held() {
        return hold == null ? 0L : hold.holding();
    }

    public void letGo() {
        if (hold != null) hold.letGo();
    }

    public long[] readAgain() {
        return hold == null ? new long[2] : hold.readAgain();
    }

    private static List<Derived> derived(List<SessionReader> sessions,
                                         Corpus previous) {
        try {
            return Parallel.map(sessions, session -> {
                Derived kept = previous == null ? null
                        : previous.bySession.get(session.sessionId());
                if (kept != null && kept.session == session) return kept;
                digestIds(session);
                return new Derived(session, true);
            }, Parallel.READS);
        } catch (IOException unreadable) {
            throw new UncheckedIOException(unreadable);
        }
    }

    private static void digestIds(SessionReader session) {
        for (ActivationRow row : session.activations()) {
            row.occurrence().id();
            if (row.anchorProducer() != null) row.anchorProducer().id();
        }
        for (ExportRow row : session.exports()) row.endpoint().id();
        for (AttachRow row : session.attaches()) {
            row.endpoint().id();
            if (row.producer() != null) row.producer().id();
        }
        for (WriteRow row : session.writes()) row.endpoint().id();
        for (ReadRow row : session.reads()) row.endpoint().id();
    }

    private static boolean forcedTarget(SessionReader session) {
        for (TargetRow row : session.targets()) {
            if (row.isForced()) return true;
        }
        return false;
    }

    public static Corpus read(Path iteration, Path rootDomains)
            throws IOException {
        return read(iteration, rootDomains, null, null);
    }

    public static Corpus read(Path iteration, Path rootDomains,
                              Corpus previous, Collection<String> named)
            throws IOException {
        Corpus corpus = new Corpus(iteration, SessionReader.readAll(
                iteration, previous == null
                        ? Collections.<SessionReader>emptyList()
                        : previous.everySession(), named), previous);
        corpus.domains(rootDomains);
        corpus.indexWorlds(iteration);
        corpus.indexRecordedTicks(iteration);
        corpus.uncaptured.addAll(SessionDir.uncaptured(iteration));
        return corpus;
    }

    private void domains(Path rootDomains) throws IOException {
        if (rootDomains != null && Files.isRegularFile(rootDomains)) {
            declaredDomains.putAll(RootDomain.declared(rootDomains));
        }
    }

    private final Set<String> uncaptured = new HashSet<String>();

    public boolean uncaptured(String sessionId) {
        return uncaptured.contains(sessionId);
    }

    public static final String RECORDED_SCHEDULE = "recorded_schedule.jsonl";

    private Map<String, Integer> recordedTicks;

    private void indexRecordedTicks(Path iteration) throws IOException {
        Path recorded = iteration.resolve(RECORDED_SCHEDULE);
        if (!Files.isRegularFile(recorded)) return;
        recordedTicks = new HashMap<String, Integer>();
        for (ScheduleEvent event : SessionReader.readSchedule(recorded)) {
            if (event.kind() == ScheduleEvent.Kind.PUBLISH) continue;
            String[] stance = event.context().split("\\|", 3);
            if (stance.length < 2) continue;
            CausalContext.Root tick = daemonTick(CausalContext.parse(stance[1]));
            if (tick != null) {
                recordedTicks.merge(stance[0] + "|" + tick.role().name(),
                        tick.windowIndex(), Math::max);
            }
        }
    }

    private static CausalContext.Root daemonTick(CausalContext context) {
        if (!(context instanceof CausalContext.Root)) return null;
        CausalContext.Root root = (CausalContext.Root) context;
        return root.api().isEmpty() ? root : null;
    }

    public TickPast tickPastRecording(OccurrenceAddress occurrence) {
        if (recordedTicks == null) return null;
        String node = occurrence.node().render();
        CausalContext context = occurrence.context();
        Set<String> walked = new HashSet<String>();
        while (context instanceof CausalContext.Anchor) {
            String producer =
                    ((CausalContext.Anchor) context).producerEndpointId();
            ContextShape.Stance stance = senderStanceByEndpoint.get(producer);
            if (stance == null || !walked.add(producer)) break;
            node = stance.node();
            context = stance.context();
        }
        CausalContext.Root tick = daemonTick(context);
        if (tick == null) return null;
        int last = recordedTicks.getOrDefault(node + "|" + tick.role().name(),
                0);
        return tick.windowIndex() <= last ? null
                : new TickPast(node + " " + tick.render(), last);
    }

    public static final class TickPast {
        public final String tick;
        public final int last;

        TickPast(String tick, int last) {
            this.tick = tick;
            this.last = last;
        }

        @Override
        public String toString() {
            return tick + ", the recording's last being #" + last;
        }
    }

    public List<String> contextShape(CausalContext context) {
        return ContextShape.of(context, producer -> {
            OccurrenceAddress sender = occurrenceByEndpoint.get(producer);
            return sender == null ? senderStanceByEndpoint.get(producer)
                    : new ContextShape.Stance(sender.node().render(),
                            sender.context());
        });
    }

    private void indexWorlds(Path iteration) throws IOException {
        List<ObligationDir> workers = ObligationDir.workersIn(iteration);
        for (Map.Entry<String, JsonObject> world
                : ObligationDir.worlds(workers).entrySet()) {
            worlds.put(world.getKey(), ExploreCodec.readWorld(
                    world.getValue()));
        }
        for (ObligationDir worker : workers) {
            landedIn.put(worker.sessionId(), worker.dir().getParent());
            for (ObligationResult result : worker.results()) {
                waveVerdicts.computeIfAbsent(worker.sessionId(),
                        key -> new LinkedHashMap<String, ObligationResult>())
                        .put(result.obligationId(), result);
                if (result.refutation() == null || worker.focus().isEmpty()) {
                    continue;
                }
                JsonObject focus = worker.focus().get(0);
                JsonObject flip = JsonFields.object(focus, "flip");
                if (!flip.has("siteId")) continue;
                refuted.computeIfAbsent(ObligationFactory.flip(
                        JsonFields.optionalString(focus, "taskId"),
                        JsonFields.optionalString(focus, "pathId"),
                        JsonFields.optionalString(flip, "siteId"),
                        flip.get("ordinal").getAsInt(),
                        flip.get("outcome").getAsBoolean()),
                        key -> new ArrayList<Refuted>()).add(new Refuted(
                        result.obligationId(), worker.sessionId(),
                        ExploreCodec.readWorld(focus), result.refutation()));
            }
        }
    }

    public Map<String, Path> landedIn() {
        return Collections.unmodifiableMap(landedIn);
    }

    public static int distinctWorlds(List<Refuted> refuted) {
        Set<String> digests = new LinkedHashSet<String>();
        for (Refuted world : refuted) digests.add(world.digest);
        return digests.size();
    }

    public List<Refuted> refutedWorlds(String flip) {
        List<Refuted> worlds = refuted.get(flip == null ? "" : flip);
        return worlds == null ? Collections.<Refuted>emptyList()
                : Collections.unmodifiableList(worlds);
    }

    public Set<String> openArmAsks(OccurrenceAddress anchor) {
        Set<String> asks = new LinkedHashSet<String>();
        for (TargetRow row : targetsOn(anchor)) {
            TargetRow.OpenArm open = row.openArm();
            if (row.reachedAnchor() && open != null
                    && !open.askedSiteId().isEmpty()) {
                asks.add(FlipQuery.asked(open.askedSiteId(),
                        open.askedOrdinal()));
            }
        }
        return asks;
    }

    public boolean openArmFlip(OccurrenceAddress anchor, String siteId,
                               int ordinal, boolean flippedOutcome) {
        for (TargetRow row : targetsOn(anchor)) {
            TargetRow.OpenArm open = row.openArm();
            if (!row.reachedAnchor() || open == null
                    || !open.askedSiteId().equals(siteId)
                    || open.askedOrdinal() != ordinal) {
                continue;
            }
            Boolean ran = null;
            for (DecisionRow decision : decisionsOf(row.sessionId(),
                    anchor)) {
                if (decision.siteId().equals(siteId)
                        && decision.ordinal() == ordinal) {
                    ran = decision.outcome();
                }
            }
            if (ran == null && open.siteId().equals(siteId)
                    && open.ordinal() == ordinal) {
                ran = !open.outcome();
            }
            if (ran != null && ran != flippedOutcome) return true;
        }
        return false;
    }

    public World world(String sessionId) {
        World stated = worlds.get(sessionId == null ? "" : sessionId);
        return stated == null ? World.empty() : stated;
    }

    public String inputShape(String sessionId, OccurrenceAddress occurrence,
                             List<OccurrenceAddress> factor,
                             Set<String> locations, List<String> stated) {
        Set<String> members = new TreeSet<String>(BY_SHAPE);
        for (OccurrenceAddress member : factor) {
            if (member.equals(occurrence)) continue;
            Set<String> writes = writeSites(sessionId, member, occurrence,
                    locations);
            Set<String> messages = handoffs(sessionId, member, false);
            if (writes.isEmpty() && messages.isEmpty()) continue;
            members.add(classOf(member) + ':'
                    + (activation(sessionId, member) != null)
                    + messages + writes);
        }
        List<String> guard = new ArrayList<String>();
        Set<String> kept = new TreeSet<String>(BY_SHAPE);
        for (int at = 0; at < stated.size(); at++) {
            for (String symbol : termSymbols(sessionId, stated.get(at))) {
                if (symbolKind(sessionId, symbol) != SymbolKind.HANDOFF) {
                    continue;
                }
                String bound = tokenName(sessionId, "handoff|" + sessionId
                        + "|" + symbol, () -> handoffName(attach(sessionId,
                        symbol), new Naming()));
                if (at == 0) {
                    guard.add(bound);
                } else {
                    kept.add(bound);
                }
            }
        }
        StringBuilder text = new StringBuilder();
        text.append(occurrence.id()).append(':')
                .append(activation(sessionId, occurrence) != null)
                .append(handoffs(sessionId, occurrence, false)).append(guard)
                .append(kept);
        for (String member : members) text.append('\n').append(member);
        return ArtifactIO.digest(numbered(text.toString(),
                new LinkedHashMap<String, String>()), 16);
    }

    private static final class OfTask {
        volatile List<OccurrenceAddress> feeders;
        final Map<String, String> dependence =
                new ConcurrentHashMap<String, String>();
    }

    private final Map<ByIdentity<Task>, OfTask> ofTask =
            new ConcurrentHashMap<ByIdentity<Task>, OfTask>();

    private OfTask ofTask(Task task) {
        return ofTask.computeIfAbsent(new ByIdentity<Task>(task),
                key -> new OfTask());
    }

    String dependence(Task task, String decision, Supplier<String> compute) {
        OfTask of = ofTask(task);
        String held = of.dependence.get(decision);
        if (held != null) return held;
        String keyed = compute.get();
        of.dependence.put(decision, keyed);
        return keyed;
    }

    public List<OccurrenceAddress> feeders(Task task) {
        OfTask of = ofTask(task);
        List<OccurrenceAddress> held = of.feeders;
        if (held == null) {
            held = Collections.unmodifiableList(feeders(task.focused(),
                    task.factor()));
            of.feeders = held;
        }
        return held;
    }

    public List<OccurrenceAddress> feeders(OccurrenceAddress occurrence,
                                           List<OccurrenceAddress> factor) {
        Set<String> read = readLocations.getOrDefault(occurrence.id(),
                Collections.<String>emptySet());
        List<OccurrenceAddress> feeders = new ArrayList<OccurrenceAddress>();
        for (OccurrenceAddress member : factor) {
            if (!Collections.disjoint(read, writtenLocations.getOrDefault(
                    member.id(), Collections.<String>emptySet()))) {
                feeders.add(member);
            }
        }
        return feeders;
    }

    private Set<String> handoffs(String sessionId,
                                 OccurrenceAddress occurrence,
                                 boolean stores) {
        Map<String, Set<String>> handoffsOf = names(sessionId).handoffs;
        String key = occurrence.id() + "|" + stores;
        Set<String> held = handoffsOf.get(key);
        if (held != null) return held;
        Set<String> fed = new TreeSet<String>(BY_SHAPE);
        for (AttachRow attach : attachesOn(sessionId, occurrence)) {
            if (!stores && ContentPort.is(attach.endpoint().site())) {
                continue;
            }
            Endpoint producer = attach.producer();
            String from = producer == null ? ""
                    : "<-" + (producer.occurrence() == null
                    ? handle("endpoint", producer.id())
                    : classOf(producer.occurrence()) + "@"
                    + sequences(producer.site()) + "#"
                    + handle("export", producer.id()));
            fed.add(sequences(attach.endpoint().site()) + from);
        }
        fed = Collections.unmodifiableSet(fed);
        handoffsOf.put(key, fed);
        return fed;
    }


    static String sequences(String text) {
        if (text == null || text.isEmpty()) return "";
        Matcher counter = RunSpellings.SEQUENCE.matcher(text);
        StringBuffer out = new StringBuffer();
        while (counter.find()) {
            counter.appendReplacement(out, Matcher.quoteReplacement(
                    handle(counter.group(1), "seq:" + counter.group())));
        }
        return counter.appendTail(out).toString();
    }

    String classOf(OccurrenceAddress occurrence) {
        return classes.computeIfAbsent(occurrence.id(), id -> {
            List<String> shape = contextShape(occurrence.context());
            return shape.contains(ContextShape.UNKNOWN_HOP) ? id
                    : occurrence.node().render() + "|"
                            + occurrence.regionId() + "|" + shape;
        });
    }

    private final Map<String, String> classes =
            new java.util.concurrent.ConcurrentHashMap<String, String>();

    private Set<String> writeSites(String sessionId, OccurrenceAddress member,
                                   OccurrenceAddress task,
                                   Set<String> locations) {
        Set<String> sites = new TreeSet<String>(BY_SHAPE);
        for (WriteRow write : writesOn(sessionId, member)) {
            if (write.initial() || !locations.contains(
                    SmtLowering.locationKey(write.location()))) {
                continue;
            }
            sites.add(write.endpoint().site() + "="
                    + written(sessionId, write, task));
        }
        return sites;
    }

    private String written(String sessionId, WriteRow write,
                           OccurrenceAddress task) {
        String term = term(sessionId, write.expressionRef(), new Naming());
        if (term != null && !UNSUPPORTED.equals(term)) return term;
        String location = SmtLowering.locationKey(write.location());
        Set<String> values = new TreeSet<String>(BY_SHAPE);
        for (ReadRow read : readsOn(sessionId, task)) {
            if (read.observedVersion() == write.version() && location.equals(
                    SmtLowering.locationKey(read.location()))) {
                values.add(observed(sessionId, read.concreteValue()));
            }
        }
        return values.isEmpty() ? UNSUPPORTED : UNSUPPORTED + values;
    }

    private String observed(String sessionId, String value) {
        String text = String.valueOf(value);
        String[] object = VmRows.objectHandle(text);
        return object != null ? handle(object[0], "rid:" + object[1])
                : programNames(sessionId, text);
    }

    private String programNames(String sessionId, String text) {
        SessionReader session = sessionById.get(sessionId);
        String named = sequences((session == null
                || session.manifest() == null ? RunSpellings.NONE
                : session.manifest().runSpellings()).name(text));
        if (named.indexOf('@') < 0) return named;
        Matcher hash = RunSpellings.IDENTITY.matcher(named);
        StringBuffer out = new StringBuffer();
        while (hash.find()) {
            hash.appendReplacement(out, Matcher.quoteReplacement(
                    handle(hash.group(1) + "@", hash.group())));
        }
        return hash.appendTail(out).toString();
    }

    private static final char MARK = '\u0001';
    private static final char HANDLE = '\u0002';
    private static final Pattern MARKED = Pattern.compile(
            "\u0001([^\u0001\u0002]*)\u0002([^\u0001]*)\u0001");

    static String handle(String prefix, String handle) {
        return MARK + prefix + HANDLE + handle + MARK;
    }

    static String numbered(String text, Map<String, String> order) {
        if (text.indexOf(MARK) < 0) return text;
        Map<String, Integer> number = new HashMap<String, Integer>();
        Matcher handle = MARKED.matcher(text);
        StringBuffer out = new StringBuffer();
        while (handle.find()) {
            order.putIfAbsent(handle.group(2), handle.group());
            int at = number.computeIfAbsent(handle.group(2),
                    key -> number.size() + 1);
            handle.appendReplacement(out, Matcher.quoteReplacement(
                    handle.group(1) + at));
        }
        return handle.appendTail(out).toString();
    }

    private static String unmarked(String text) {
        return text.indexOf(MARK) < 0 ? text
                : MARKED.matcher(text).replaceAll("$1");
    }

    private static String unopened(String text) {
        return text.indexOf(OPEN) < 0 ? text
                : OPENED.matcher(text).replaceAll(String.valueOf(OPEN));
    }

    private static final Comparator<String> BY_SHAPE = Comparator
            .comparing((String text) -> unmarked(unopened(text)))
            .thenComparing(Corpus::unopened);

    private static String unit(String text) {
        Map<String, String> order = new LinkedHashMap<String, String>();
        String digest = ArtifactIO.digest(numbered(text, order), 16);
        return order.isEmpty() ? digest : digest + order.values();
    }

    private static final class Naming {
        final Map<String, Integer> entered = new HashMap<String, Integer>();
        final List<String> open = new ArrayList<String>();
        final Map<String, Unit> units = new HashMap<String, Unit>();
        int next;
        int low = Integer.MAX_VALUE;
        boolean unsupported;
        Set<String> taints = new HashSet<String>();
    }

    private static final class Unit {
        final boolean taints;
        String text;
        boolean unsupported;
        Set<String> takes;

        Unit(boolean taints) {
            this.taints = taints;
        }
    }

    String decisionShape(String sessionId, String term) {
        return SmtNames.substitute(FlipQuery.statedTerm(this, sessionId,
                term), token -> {
                    switch (symbolKind(sessionId, token)) {
                        case ROOT:
                            return "root:" + rootBySymbol(sessionId, token)
                                    .rootId();
                        case HANDOFF:
                            return "handoff:" + attach(sessionId, token)
                                    .endpoint().site();
                        case READ:
                            return "read:" + SmtLowering.locationKey(
                                    read(sessionId, token).location());
                        default:
                            return null;
                    }
                });
    }

    private static final String UNLOWERED = "!";
    private static final String UNSUPPORTED = "?";

    private String term(String sessionId, String expressionRef,
                        Naming naming) {
        if (expressionRef == null || expressionRef.isEmpty()) return null;
        String name = step(sessionId, "term|" + sessionId + "|"
                + expressionRef, naming, false, () -> {
                    SmtLowering lowering = lowering(sessionId);
                    SmtLowering.Lowered lowered = lowering == null ? null
                            : lowering.lower(expressionRef);
                    if (lowered == null || !lowered.ok()
                            || FlipQuery.undeclared(this, sessionId,
                            lowered.text()) != null) {
                        return null;
                    }
                    return canonical(sessionId, lowered.text(), naming);
                });
        return UNLOWERED.equals(name) ? null : name;
    }

    private static final char OPEN = '\u0004';
    private static final Pattern OPENED = Pattern.compile(
            "\u0004(\\d+)\u0004");
    static final long NAMING_BUDGET = 1L << 26;

    private String step(String sessionId, String key, Naming naming,
                        boolean taints, Supplier<String> body) {
        Map<String, String> canonicalNames = names(sessionId).canonical;
        String held = canonicalNames.get(key);
        if (held != null) {
            naming.unsupported |= taints && held.charAt(0) == 'U';
            return held.substring(1);
        }
        Integer entered = naming.entered.get(key);
        if (entered != null) {
            naming.low = Math.min(naming.low, entered);
            if (taints) naming.taints.add(key);
            return OPEN + entered.toString() + OPEN;
        }
        int number = naming.next++;
        naming.entered.put(key, number);
        naming.open.add(key);
        int low = naming.low;
        boolean unsupported = naming.unsupported;
        Set<String> outer = naming.taints;
        naming.low = number;
        naming.unsupported = false;
        naming.taints = new HashSet<String>();
        Unit unit = new Unit(taints);
        try {
            unit.text = body.get();
        } finally {
            unit.unsupported = naming.unsupported;
            unit.takes = naming.taints;
            naming.units.put(key, unit);
            naming.unsupported = unsupported;
            naming.taints = outer;
        }
        int reached = naming.low;
        naming.low = Math.min(low, reached);
        if (reached < number) {
            if (taints) naming.taints.add(key);
            return OPEN + Integer.toString(number) + OPEN;
        }
        List<String> cycle = naming.open.subList(naming.open.indexOf(key),
                naming.open.size());
        Map<String, String> names = close(new ArrayList<String>(cycle),
                naming);
        for (String member : cycle) {
            naming.entered.remove(member);
            naming.units.remove(member);
        }
        cycle.clear();
        String name = names.get(key);
        canonicalNames.putAll(names);
        naming.unsupported |= taints && name.charAt(0) == 'U';
        return name.substring(1);
    }

    private Map<String, String> close(List<String> cycle, Naming naming) {
        Map<String, Unit> units = new HashMap<String, Unit>();
        Map<Integer, String> byNumber = new HashMap<Integer, String>();
        for (String member : cycle) {
            units.put(member, naming.units.get(member));
            byNumber.put(naming.entered.get(member), member);
        }
        Set<String> unsupported = new HashSet<String>();
        for (boolean grew = true; grew; ) {
            grew = false;
            for (String member : cycle) {
                if (unsupported.contains(member)) continue;
                Unit unit = units.get(member);
                boolean tainted = unit.unsupported;
                for (String taken : unit.takes) {
                    tainted |= unsupported.contains(taken);
                }
                if (tainted) grew = unsupported.add(member);
            }
        }
        Map<String, String> fixed = new HashMap<String, String>();
        for (String member : cycle) {
            Unit unit = units.get(member);
            if (unit.text == null) {
                fixed.put(member, UNLOWERED);
            } else if (!unit.taints && unsupported.contains(member)) {
                fixed.put(member, UNSUPPORTED);
            }
        }
        long cost = 0;
        for (String member : cycle) {
            String text = units.get(member).text;
            cost += text == null ? 0 : text.length();
        }
        boolean cut = cycle.size() > 1 && cost * cycle.size() > NAMING_BUDGET;
        if (cut) {
            namingCuts.merge(cycle.size(), 1, Integer::sum);
        }
        Map<String, String> names = new HashMap<String, String>();
        for (String member : cycle) {
            String name = fixed.get(member);
            if (name == null) {
                name = cut ? unit("cut:" + member)
                        : unit(cycleText(member, units, byNumber, fixed));
            }
            names.put(member, (unsupported.contains(member) ? "U" : "S")
                    + name);
        }
        return names;
    }

    private static String cycleText(String from, Map<String, Unit> units,
                                    Map<Integer, String> byNumber,
                                    Map<String, String> fixed) {
        List<String> order = new ArrayList<String>();
        Map<String, Integer> number = new HashMap<String, Integer>();
        order.add(from);
        number.put(from, 1);
        StringBuilder out = new StringBuilder();
        for (int at = 0; at < order.size(); at++) {
            if (at > 0) out.append(OPEN);
            Matcher open = OPENED.matcher(units.get(order.get(at)).text);
            StringBuffer text = new StringBuffer();
            while (open.find()) {
                String member = byNumber.get(Integer.parseInt(open.group(1)));
                String name = fixed.get(member);
                if (name == null) {
                    Integer seen = number.get(member);
                    if (seen == null) {
                        seen = order.size() + 1;
                        number.put(member, seen);
                        order.add(member);
                    }
                    name = "cycle" + seen;
                }
                open.appendReplacement(text, Matcher.quoteReplacement(name));
            }
            out.append(open.appendTail(text));
        }
        return out.toString();
    }

    private final Map<Integer, Integer> namingCuts =
            new ConcurrentHashMap<Integer, Integer>();

    public String namingCut() {
        if (namingCuts.isEmpty()) return null;
        return "ARM_KEY_NAMING_CUT: " + new TreeMap<Integer, Integer>(
                namingCuts) + " (cycle size -> cycles) were past the naming"
                + " budget of " + NAMING_BUDGET + " characters: each of"
                + " their units is named by its own reference, so no world"
                + " folds through them and their arms are asked again";
    }

    private static final char PLACE = '\u0003';

    private String canonical(String sessionId, String text, Naming naming) {
        SmtLowering lowering = lowering(sessionId);
        List<String> names = new ArrayList<String>();
        String program = programNames(sessionId, SmtNames.substitute(text,
                token -> {
                    String name = tokenName(sessionId, lowering, token,
                            naming);
                    if (name == null) return null;
                    names.add(name);
                    return PLACE + String.valueOf(names.size() - 1) + PLACE;
                }));
        StringBuilder out = new StringBuilder();
        int at = 0;
        for (int open = program.indexOf(PLACE); open >= 0;
             open = program.indexOf(PLACE, at)) {
            int close = program.indexOf(PLACE, open + 1);
            out.append(program, at, open).append(names.get(
                    Integer.parseInt(program.substring(open + 1, close))));
            at = close + 1;
        }
        return out.append(program.substring(at)).toString();
    }

    private String tokenName(String sessionId, SmtLowering lowering,
                             String token, Naming naming) {
        if (SmtNames.BUILTIN.contains(token)) return null;
        String body = lowering == null ? null : lowering.sharedBody(token);
        if (body != null) {
            return "dag:" + step(sessionId, "dag|" + sessionId + "|" + token,
                    naming, true, () -> canonical(sessionId, body, naming));
        }
        switch (symbolKind(sessionId, token)) {
            case ROOT: {
                RootMintRow root = rootBySymbol(sessionId, token);
                return (root.kind() == RootKind.CLOCK ? "clock:" : "root:")
                        + root.rootId();
            }
            case HANDOFF:
                return tokenName(sessionId, "handoff|" + sessionId + "|"
                        + token, () -> handoffName(attach(sessionId, token),
                        naming));
            case READ:
                return tokenName(sessionId, "read|" + sessionId + "|" + token,
                        () -> readName(sessionId, read(sessionId, token),
                                naming));
            default:
                if (lowering == null || !lowering.minted(token)) return null;
                if (token.startsWith("unsupported__")) {
                    naming.unsupported = true;
                }
                String[] object = VmRows.objectHandle(
                        lowering.identityOf(token));
                return handle(token.replaceAll("__[0-9a-f]+$", "__"),
                        object == null ? token : "rid:" + object[1]);
        }
    }

    private String readName(String sessionId, ReadRow row, Naming naming) {
        String location = "read:" + row.location().kind() + ":"
                + sequences(row.location().slot());
        String sort = JavaSmtSorts.sortOfJava(row.javaType()).smt;
        List<Arms.Arm> eligible = arms().stateArms(row.endpoint(), sessionId,
                SmtLowering.locationKey(row.location()),
                row.observedVersion(), !row.unnamedWriter());
        arms().drainRefusals();
        List<String> writers = new ArrayList<String>();
        boolean binds = false;
        for (Arms.Arm arm : eligible) {
            WriteRow write = arm.write();
            boolean seen = write != null
                    && write.version() == row.observedVersion();
            String who = write == null ? classOf(arm.producer())
                    : write.initial() ? "initial"
                    : classOf(arm.producer()) + "@" + write.endpoint().site();
            SmtLowering lowering = lowering(arm.sessionId());
            SmtLowering.Lowered lowered = lowering == null ? null
                    : lowering.lower(arm.expressionRef());
            if (lowered != null && lowered.ok()
                    && !lowered.value().sort.smt.equals(sort)) {
                writers.add(who + "=/");
                continue;
            }
            String term = term(arm.sessionId(), arm.expressionRef(), naming);
            binds |= term != null;
            writers.add(who + "=" + (term == null || UNSUPPORTED.equals(term)
                    ? "?" + (seen ? observed(sessionId, row.concreteValue())
                    : "") : term));
        }
        if (!binds) {
            return location + "=" + observed(sessionId, row.concreteValue());
        }
        writers.sort(BY_SHAPE);
        return location + "<-" + writers;
    }

    private String handoffName(AttachRow attach, Naming naming) {
        String port = "handoff:" + sequences(attach.endpoint().site());
        List<String> arms = new ArrayList<String>();
        if (attach.producer() != null) {
            String sessionId = attach.sessionId();
            SmtLowering lowering = lowering(sessionId);
            for (Arms.Arm arm : arms().ownArmsAt(Interaction.of(
                    InteractionKind.WIRE, attach.producer(),
                    attach.endpoint()), attach.symbol(), sessionId)) {
                SmtLowering.Lowered lowered = lowering == null ? null
                        : lowering.lower(arm.expressionRef());
                if (lowered == null || !lowered.ok()
                        || FlipQuery.malformed(lowered.text())) {
                    continue;
                }
                String term = term(sessionId, arm.expressionRef(), naming);
                if (term == null) continue;
                boolean unsupported = naming.unsupported;
                Set<String> taints = new HashSet<String>(naming.taints);
                List<String> conditions = new ArrayList<String>();
                for (String conjunct : arm.pi()) {
                    if (!Arms.predicate(conjunct)) continue;
                    String stated = FlipQuery.statedTerm(this, sessionId,
                            conjunct);
                    if (FlipQuery.malformed(stated) || FlipQuery.undeclared(
                            this, sessionId, stated) != null) {
                        continue;
                    }
                    conditions.add(canonical(sessionId, stated, naming));
                }
                naming.unsupported = unsupported;
                naming.taints = taints;
                arms.add(classOf(arm.producer()) + "@"
                        + attach.producer().site() + "=" + term + "|"
                        + conditions + "|" + new TreeMap<String, String>(
                        arm.guard()));
            }
            arms().drainRefusals();
        }
        if (arms.isEmpty()) {
            return port + "=" + observed(attach.sessionId(), attach.arrival());
        }
        arms.sort(BY_SHAPE);
        return port + "<-" + arms;
    }

    private String tokenName(String sessionId, String key,
                             Supplier<String> name) {
        Map<String, String> tokenNames = names(sessionId).tokens;
        String held = tokenNames.get(key);
        if (held != null) return held;
        String named = name.get();
        if (named.indexOf(OPEN) >= 0) return named;
        String unit = unit(named);
        tokenNames.put(key, unit);
        return unit;
    }

    private static final class Names {
        final Map<String, String> canonical =
                new ConcurrentHashMap<String, String>();
        final Map<String, String> tokens =
                new ConcurrentHashMap<String, String>();
        final Map<String, Set<String>> handoffs =
                new ConcurrentHashMap<String, Set<String>>();
    }

    private final Map<String, Names> names =
            new ConcurrentHashMap<String, Names>();

    private Names names(String sessionId) {
        return names.computeIfAbsent(sessionId, any -> new Names());
    }

    void keysDone(String sessionId) {
        names.remove(sessionId);
        loweringById.remove(sessionId);
    }

    public ObligationResult waveVerdict(String sessionId,
                                        String obligationId) {
        return waveVerdicts.getOrDefault(sessionId,
                Collections.<String, ObligationResult>emptyMap())
                .get(obligationId);
    }

    public Path iteration() {
        return iteration;
    }

    public OccurrenceAddress senderOf(String producerEndpointId) {
        String sender = senderByEndpoint.get(producerEndpointId);
        return sender == null ? null : occurrenceById.get(sender);
    }

    public Set<String> startedBy(OccurrenceAddress occurrence) {
        return occurrence.context() instanceof CausalContext.Anchor
                ? Collections.singleton(((CausalContext.Anchor)
                        occurrence.context()).producerEndpointId())
                : takenInByStance.getOrDefault(
                        ContextShape.Stance.of(occurrence).render(),
                        Collections.<String>emptySet());
    }

    public List<OccurrenceAddress> replyLegsOf(OccurrenceAddress occurrence) {
        Set<String> legs = new LinkedHashSet<String>();
        Deque<String> pending = new ArrayDeque<String>();
        pending.add(occurrence.id());
        for (String other : occurrencesByStance.getOrDefault(
                ContextShape.Stance.of(occurrence).render(),
                Collections.<String>emptySet())) {
            if (occurrenceById.get(other).standsUnder(occurrence)) {
                pending.add(other);
            }
        }
        while (!pending.isEmpty()) {
            for (String request : sentByOccurrence.getOrDefault(
                    pending.poll(), Collections.<String>emptySet())) {
                for (String reply : repliesByRequest.getOrDefault(request,
                        Collections.<String>emptySet())) {
                    for (String reader : readersByEndpoint.getOrDefault(
                            reply, Collections.<String>emptySet())) {
                        if (!reader.equals(occurrence.id())
                                && legs.add(reader)) {
                            pending.add(reader);
                        }
                    }
                }
            }
        }
        List<OccurrenceAddress> readers = new ArrayList<OccurrenceAddress>();
        for (String reader : legs) {
            OccurrenceAddress address = occurrenceById.get(reader);
            if (address != null) readers.add(address);
        }
        return readers;
    }

    public OccurrenceAddress receiverOf(String producerEndpointId) {
        String receiver = receiverByEndpoint.get(producerEndpointId);
        return receiver == null ? null : occurrenceById.get(receiver);
    }

    public List<OccurrenceAddress> doorsOf(String producerEndpointId,
                                           OccurrenceAddress served,
                                           Map<String, Integer> cut,
                                           List<OccurrenceAddress> earlier) {
        List<OccurrenceAddress> doors = new ArrayList<OccurrenceAddress>();
        for (OccurrenceAddress door : new OccurrenceAddress[] {
                senderOf(producerEndpointId),
                receiverOf(producerEndpointId)}) {
            if (door != null && !doors.contains(door)) doors.add(door);
        }
        Set<String> stances = new HashSet<String>(receivingStances
                .getOrDefault(producerEndpointId,
                        Collections.<String>emptySet()));
        ContextShape.Stance sentFrom =
                senderStanceByEndpoint.get(producerEndpointId);
        if (sentFrom != null) stances.add(sentFrom.render());
        Set<String> handlers = handlerStances.getOrDefault(
                producerEndpointId, Collections.<String>emptySet());
        if (stances.isEmpty() && handlers.isEmpty()) return doors;
        String own = ContextShape.Stance.of(served).render();
        StanceIndex index = stanceIndex();
        Set<String> asked = new HashSet<String>(stances);
        asked.addAll(handlers);
        asked.add(own);
        int count = 0;
        List<int[]> standing = new ArrayList<int[]>();
        for (String stance : asked) {
            int[] places = index.places.get(stance);
            if (places == null) continue;
            standing.add(places);
            count += places.length;
        }
        int[] places = new int[count];
        int next = 0;
        for (int[] each : standing) {
            System.arraycopy(each, 0, places, next, each.length);
            next += each.length;
        }
        Arrays.sort(places);
        for (int place : places) {
            OccurrenceAddress occurrence = index.occurrences.get(place);
            if (occurrence.equals(served)) continue;
            String stance = index.stances[place];
            if (stance.equals(own)) {
                if (ranBefore(occurrence, served)) {
                    if (!earlier.contains(occurrence)) earlier.add(occurrence);
                    cut.merge(EARLIER_IN_TURN, 1, Integer::sum);
                } else {
                    cut.merge(OWN_TURN, 1, Integer::sum);
                }
            } else if (stances.contains(stance)) {
                if (!doors.contains(occurrence)) doors.add(occurrence);
            } else if (handlers.contains(stance)) {
                cut.merge(HANDLER_TURN, 1, Integer::sum);
            }
        }
        return doors;
    }

    private boolean ranBefore(OccurrenceAddress occurrence,
                              OccurrenceAddress served) {
        Seen at = seen.get(occurrence.id());
        Seen of = seen.get(served.id());
        return at != null && of != null && at.session.equals(of.session)
                && at.first < of.last;
    }

    private static final class Seen {
        final String session;
        final long first;
        final long last;

        Seen(String session, long first, long last) {
            this.session = session;
            this.first = first;
            this.last = last;
        }
    }

    private static void seenAt(Map<String, long[]> at,
                               OccurrenceAddress occurrence, long seq) {
        if (occurrence == null || seq <= 0L) return;
        long[] span = at.get(occurrence.id());
        if (span == null) {
            at.put(occurrence.id(), new long[] {seq, seq});
        } else {
            span[0] = Math.min(span[0], seq);
            span[1] = Math.max(span[1], seq);
        }
    }

    private static final class StanceIndex {
        final List<OccurrenceAddress> occurrences;
        final String[] stances;
        final Map<String, int[]> places = new HashMap<String, int[]>();

        StanceIndex(Collection<OccurrenceAddress> all) {
            occurrences = new ArrayList<OccurrenceAddress>(all);
            stances = new String[occurrences.size()];
            Map<String, List<Integer>> at =
                    new HashMap<String, List<Integer>>();
            for (int place = 0; place < stances.length; place++) {
                stances[place] = ContextShape.Stance.of(
                        occurrences.get(place)).render();
                at.computeIfAbsent(stances[place],
                        stance -> new ArrayList<Integer>()).add(place);
            }
            for (Map.Entry<String, List<Integer>> each : at.entrySet()) {
                int[] held = new int[each.getValue().size()];
                for (int index = 0; index < held.length; index++) {
                    held[index] = each.getValue().get(index);
                }
                places.put(each.getKey(), held);
            }
        }
    }

    private volatile StanceIndex stanceIndex;

    private StanceIndex stanceIndex() {
        StanceIndex held = stanceIndex;
        if (held != null) return held;
        synchronized (this) {
            if (stanceIndex == null) {
                stanceIndex = new StanceIndex(occurrenceById.values());
            }
            return stanceIndex;
        }
    }

    public static final String OWN_TURN = "own turn";
    public static final String EARLIER_IN_TURN = "earlier in its turn";
    public static final String HANDLER_TURN = "handlers";

    private static List<Fact> facts(SessionReader session) {
        List<ScheduleEvent> events;
        try {
            events = session.schedule();
        } catch (IOException unreadable) {
            throw new UncheckedIOException(unreadable);
        }
        List<Fact> facts = new ArrayList<Fact>();
        Map<String, ContextShape.Stance> stances =
                new HashMap<String, ContextShape.Stance>();
        Map<String, String> renders = new HashMap<String, String>();
        for (ScheduleEvent event : events) {
            ContextShape.Stance stance = stance(stances, event.context());
            String received = NAMES.intern(event.received());
            String endpoint = NAMES.intern(event.endpoint());
            String occurrence = NAMES.intern(event.occurrence());
            if (!received.isEmpty() && stance != null
                    && !(stance.context() instanceof CausalContext.Anchor)) {
                facts.add(new Fact(Fact.Kind.TAKEN_IN, renders
                        .computeIfAbsent(stance.render(), NAMES::intern),
                        received, null));
            }
            if (event.kind() == ScheduleEvent.Kind.SEND
                    && !endpoint.isEmpty() && stance != null) {
                facts.add(new Fact(Fact.Kind.SENDER_STANCE, endpoint, "",
                        stance));
                if (stance.context() instanceof CausalContext.Anchor
                        && Endpoint.replySite(event.site())) {
                    facts.add(new Fact(Fact.Kind.REPLY, NAMES.intern(
                            ((CausalContext.Anchor) stance.context())
                                    .producerEndpointId()), endpoint, null));
                }
            }
            if (occurrence.isEmpty()) {
                if (!received.isEmpty() && stance != null) {
                    facts.add(new Fact(stance.context() instanceof
                            CausalContext.Anchor ? Fact.Kind.HANDLER_STANCE
                            : Fact.Kind.RECEIVING_STANCE, received, "",
                            stance));
                }
                continue;
            }
            if (event.kind() == ScheduleEvent.Kind.SEND
                    && !endpoint.isEmpty()) {
                facts.add(new Fact(Fact.Kind.SENDER, endpoint, occurrence,
                        null));
            } else if (!received.isEmpty()) {
                facts.add(new Fact(Fact.Kind.RECEIVER, received, occurrence,
                        null));
            }
        }
        return facts;
    }

    private static final Interner<String> NAMES =
            Interners.newWeakInterner();

    private static ContextShape.Stance stance(
            Map<String, ContextShape.Stance> stances, String sendContext) {
        int first = sendContext.indexOf('|');
        int second = first < 0 ? -1 : sendContext.indexOf('|', first + 1);
        String key = second < 0 ? sendContext
                : sendContext.substring(0, second);
        if (stances.containsKey(key)) return stances.get(key);
        ContextShape.Stance stance = ContextShape.Stance.ofSend(key);
        stances.put(key, stance == null ? null : new ContextShape.Stance(
                NAMES.intern(stance.node()), stance.context()));
        return stances.get(key);
    }

    private void indexSchedule(String sessionId, List<Fact> facts) {
        for (Fact fact : facts) {
            switch (fact.kind) {
                case TAKEN_IN:
                    takenInByStance.computeIfAbsent(fact.key,
                            key -> new LinkedHashSet<String>())
                            .add(fact.occurrence);
                    break;
                case SENDER_STANCE:
                    senderStanceByEndpoint.put(fact.key, fact.stance);
                    break;
                case SENDER:
                    senderByEndpoint.put(fact.key, fact.occurrence);
                    sentByOccurrence.computeIfAbsent(fact.occurrence,
                            key -> new LinkedHashSet<String>()).add(fact.key);
                    named(sessionId, fact.occurrence);
                    break;
                case REPLY:
                    repliesByRequest.computeIfAbsent(fact.key,
                            key -> new LinkedHashSet<String>())
                            .add(fact.occurrence);
                    break;
                case RECEIVING_STANCE:
                    receivingStances.computeIfAbsent(fact.key,
                            key -> new LinkedHashSet<String>())
                            .add(fact.stance.render());
                    break;
                case HANDLER_STANCE:
                    handlerStances.computeIfAbsent(fact.key,
                            key -> new LinkedHashSet<String>())
                            .add(fact.stance.render());
                    break;
                default:
                    receiverByEndpoint.put(fact.key, fact.occurrence);
                    break;
            }
        }
    }

    private void index(Derived of, boolean apart) {
        SessionReader session = of.session;
        long world = Long.MAX_VALUE;
        if (apart) {
            for (TargetRow row : session.targets()) {
                if (row.isForced()) world = Math.min(world, row.seq());
            }
        } else {
            indexSchedule(session.sessionId(), of.schedule);
        }
        sessionById.put(session.sessionId(), session);
        Map<String, long[]> spans = new HashMap<String, long[]>();
        if (session.manifest() != null) {
            clientNodes.addAll(session.manifest().clientNodes());
        }
        for (ActivationRow row : session.activations()) {
            if (apart) continue;
            remember(session.sessionId(), row.occurrence());
            if (row.anchorProducer() != null) {
                occurrenceByEndpoint.put(row.anchorProducer().id(),
                        row.anchorProducer().occurrence());
                remember(session.sessionId(),
                        row.anchorProducer().occurrence());
            }
            add(activations, row.occurrence().id(), row);
        }
        for (DecisionRow row : session.decisions()) {
            if (!apart) remember(session.sessionId(), row.occurrence());
            seenAt(spans, row.occurrence(), row.seq());
            for (String cell : row.clockReadings().keySet()) {
                declaredSymbols.put(cell, Sort.INT);
            }
        }
        for (ExportRow row : session.exports()) {
            if (row.seq() >= world || apart) continue;
            add(exports, row.endpoint().id(), row);
            remember(session.sessionId(), row.endpoint().occurrence());
            seenAt(spans, row.endpoint().occurrence(), row.seq());
            occurrenceByEndpoint.put(row.endpoint().id(),
                    row.endpoint().occurrence());
        }
        for (AttachRow row : session.attaches()) {
            handoffSymbols.add(row.symbol());
            attachesOn.add(row.endpoint().occurrence().id(), row.sessionId(),
                    row, apart);
            declaredSymbols.put(row.symbol(),
                    JavaSmtSorts.sortOfJava(row.javaType()));
            Interaction interaction = row.interaction();
            if (interaction != null && !apart) {
                interactions.put(interaction.id(), interaction);
                add(attachesByInteraction, interaction.id(), row);
            }
            if (apart) continue;
            remember(session.sessionId(), row.endpoint().occurrence());
            seenAt(spans, row.endpoint().occurrence(), row.seq());
            occurrenceByEndpoint.put(row.endpoint().id(),
                    row.endpoint().occurrence());
            if (row.producer() != null) {
                occurrenceByEndpoint.put(row.producer().id(),
                        row.producer().occurrence());
                remember(session.sessionId(), row.producer().occurrence());
            }
        }
        for (RootMintRow row : session.roots()) {
            if (!apart) remember(session.sessionId(), row.occurrence());
            rootsById.computeIfAbsent(row.rootId(),
                    key -> new LinkedHashMap<String, RootMintRow>())
                    .put(session.sessionId(), row);
            rootIdsBySymbol.computeIfAbsent(row.symbol(),
                    key -> new LinkedHashSet<String>()).add(row.rootId());
            declaredSymbols.put(row.symbol(),
                    row.kind() == RootKind.MARKER ? Sort.BOOL : Sort.INT);
        }
        for (WriteRow row : session.writes()) {
            if (apart) continue;
            String location = SmtLowering.locationKey(row.location());
            located(writersOn, row.endpoint().occurrence(),
                    session.sessionId());
            remember(session.sessionId(), row.endpoint().occurrence());
            seenAt(spans, row.endpoint().occurrence(), row.seq());
            if (!row.initial()) {
                located(writtenLocations, row.endpoint().occurrence(),
                        location);
                writeSitesByLocation.computeIfAbsent(location,
                        ignored -> new LinkedHashMap<List<String>,
                                WriteRow>())
                        .putIfAbsent(Arrays.asList(row.endpoint().site(),
                                row.javaType()), row);
            }
            occurrenceByEndpoint.put(row.endpoint().id(),
                    row.endpoint().occurrence());
            touch(row.endpoint().occurrence(), row.location());
        }
        for (TargetRow row : session.targets()) {
            targetsOn.add(row.occurrence().id(), row.sessionId(), row, apart);
            if (apart) {
                if (row.isForced()) {
                    forcedFrom.merge(session.sessionId(), row.seq(),
                            Math::min);
                }
                continue;
            }
            remember(session.sessionId(), row.occurrence());
            seenAt(spans, row.occurrence(), row.seq());
        }
        for (ReadRow row : session.reads()) {
            if (apart) continue;
            located(readersOn, row.endpoint().occurrence(),
                    session.sessionId());
            remember(session.sessionId(), row.endpoint().occurrence());
            seenAt(spans, row.endpoint().occurrence(), row.seq());
            located(readLocations, row.endpoint().occurrence(),
                    SmtLowering.locationKey(row.location()));
            occurrenceByEndpoint.put(row.endpoint().id(),
                    row.endpoint().occurrence());
            touch(row.endpoint().occurrence(), row.location());
        }
        for (Map.Entry<String, long[]> span : spans.entrySet()) {
            if (apart) break;
            seen.putIfAbsent(span.getKey(), new Seen(session.sessionId(),
                    span.getValue()[0], span.getValue()[1]));
        }
    }

    private void touch(OccurrenceAddress occurrence, LocationId location) {
        locationTouches.computeIfAbsent(touchKey(occurrence, location),
                key -> new LinkedHashSet<String>()).add(occurrence.id());
    }

    private static String touchKey(OccurrenceAddress occurrence,
                                   LocationId location) {
        return occurrence.node().render() + "|"
                + SmtLowering.locationKey(location);
    }

    private void remember(String sessionId, OccurrenceAddress occurrence) {
        if (occurrence == null) return;
        occurrenceById.put(occurrence.id(), occurrence);
        occurrencesByStance.computeIfAbsent(
                ContextShape.Stance.of(occurrence).render(),
                key -> new LinkedHashSet<String>()).add(occurrence.id());
        if (occurrence.context() instanceof CausalContext.Anchor) {
            readersByEndpoint.computeIfAbsent(((CausalContext.Anchor)
                    occurrence.context()).producerEndpointId(),
                    key -> new LinkedHashSet<String>()).add(occurrence.id());
        }
        named(sessionId, occurrence.id());
    }

    private void named(String sessionId, String occurrenceId) {
        namedBy.computeIfAbsent(occurrenceId,
                key -> new LinkedHashSet<String>()).add(sessionId);
    }

    private static <T> void add(Map<String, List<T>> into, String key, T row) {
        into.computeIfAbsent(key, ignored -> new ArrayList<T>()).add(row);
    }

    private static void located(Map<String, Set<String>> into,
                                OccurrenceAddress occurrence, String location) {
        into.computeIfAbsent(occurrence.id(),
                ignored -> new LinkedHashSet<String>()).add(location);
    }

    private static final class ByOccurrence<T> {
        private final Map<String, Map<String, List<T>>> rows =
                new LinkedHashMap<String, Map<String, List<T>>>();
        private final Set<String> apart = new HashSet<String>();

        void add(String occurrenceId, String sessionId, T row,
                 boolean forced) {
            if (forced) apart.add(sessionId);
            rows.computeIfAbsent(occurrenceId,
                            ignored -> new LinkedHashMap<String, List<T>>())
                    .computeIfAbsent(sessionId, ignored -> new ArrayList<T>())
                    .add(row);
        }

        List<T> of(String occurrenceId, String sessionId) {
            Map<String, List<T>> bySession = rows.get(occurrenceId);
            List<T> own = bySession == null ? null : bySession.get(sessionId);
            return own == null ? Collections.<T>emptyList()
                    : Collections.unmodifiableList(own);
        }

        List<T> all(String occurrenceId) {
            Map<String, List<T>> bySession = rows.get(occurrenceId);
            if (bySession == null) return Collections.<T>emptyList();
            List<T> all = new ArrayList<T>();
            for (Map.Entry<String, List<T>> own : bySession.entrySet()) {
                if (!apart.contains(own.getKey())) all.addAll(own.getValue());
            }
            return all;
        }
    }

    public static String pathId(String sessionId,
                                OccurrenceAddress occurrence) {
        return ArtifactIO.digest(sessionId + "|" + occurrence.id(), 16);
    }

    public String seedSessionId() {
        String seed = SessionReader.seedSessionId(sessions);
        return seed == null ? "" : seed;
    }

    public List<String> seedSessionIds() {
        return SessionReader.seedSessionIds(sessions);
    }

    public SmtLowering lowering(String sessionId) {
        Asking question = asking.get();
        Map<String, SmtLowering> lowerings = question == null
                ? loweringById : question.lowerings;
        SmtLowering held = lowerings.get(sessionId);
        if (held != null) return held;
        SessionReader session = sessionById.get(sessionId);
        if (session == null) return null;
        SmtLowering made = SmtLowering.forSession(session, join(sessionId));
        SmtLowering first = lowerings.putIfAbsent(sessionId, made);
        return first != null ? first : made;
    }

    private static final class Asking {
        final Map<String, SmtLowering> lowerings =
                new HashMap<String, SmtLowering>();
        final Map<String, Set<java.math.BigInteger>> compared =
                new HashMap<String, Set<java.math.BigInteger>>();
    }

    private final ThreadLocal<Asking> asking = new ThreadLocal<Asking>();

    public interface Question<T> {
        T ask() throws IOException;
    }

    public <T> T asking(Question<T> question) throws IOException {
        Asking before = asking.get();
        asking.set(new Asking());
        try {
            return question.ask();
        } finally {
            if (before == null) {
                asking.remove();
            } else {
                asking.set(before);
            }
        }
    }

    public SmtLowering.SessionJoin join(String sessionId) {
        return state(sessionId).join;
    }

    public List<SessionReader> sessions() {
        return sessions;
    }

    boolean client(NodeId node) {
        return node != null && clientNodes.contains(node.render());
    }

    List<SessionReader> everySession() {
        List<SessionReader> every = new ArrayList<SessionReader>(sessions);
        every.addAll(forcedSessions);
        return every;
    }

    public List<RecordedPath> forcedPaths(OccurrenceAddress occurrence) {
        List<RecordedPath> paths = new ArrayList<RecordedPath>();
        for (SessionReader session : forcedSessions) {
            TargetRow target = target(session.sessionId(), occurrence);
            if (target == null || !target.isForced()
                    || !target.reachedAnchor()
                    || !session.incomplete().isEmpty()
                    || !forcedReached(session)) {
                continue;
            }
            RecordedPath path = path(session.sessionId(), occurrence);
            if (path != null) paths.add(path);
        }
        return paths;
    }

    private static boolean forcedReached(SessionReader session) {
        if (session.obligations().isEmpty()) return false;
        for (ObligationResult result : session.obligations()) {
            if (result.verdict() != Verdict.ADMITTED) return false;
        }
        return true;
    }

    public boolean forced(String sessionId) {
        return forcedFrom.containsKey(sessionId)
                || sessionById.containsKey(sessionId)
                && sessionById.get(sessionId).forced();
    }

    @Override
    public long forcedFrom(String sessionId) {
        Long from = forcedFrom.get(sessionId);
        return from == null ? Long.MAX_VALUE : from.longValue();
    }

    public SessionReader session(String sessionId) {
        return sessionById.get(sessionId);
    }

    public OccurrenceAddress occurrence(String occurrenceId) {
        return occurrenceById.get(occurrenceId);
    }

    public List<OccurrenceAddress> occurrences() {
        return new ArrayList<OccurrenceAddress>(occurrenceById.values());
    }

    public List<RecordedPath> pathsOf(OccurrenceAddress occurrence) {
        List<RecordedPath> paths = new ArrayList<RecordedPath>();
        for (SessionReader session : sessions) {
            RecordedPath path = path(session.sessionId(), occurrence);
            if (path != null) paths.add(path);
        }
        return paths;
    }

    public RecordedPath path(String sessionId, OccurrenceAddress occurrence) {
        ActivationRow activation = activation(sessionId, occurrence);
        Derived of = bySession.get(sessionId);
        List<DecisionRow> taken = of == null ? null
                : of.decisions.get(occurrence.id());
        if (activation == null && taken == null
                && target(sessionId, occurrence) == null) {
            return null;
        }
        return new RecordedPath(sessionId, occurrence,
                taken == null ? new ArrayList<DecisionRow>() : taken);
    }

    public Set<String> namedBy(OccurrenceAddress occurrence) {
        Set<String> sessions = namedBy.get(occurrence.id());
        return sessions == null ? Collections.<String>emptySet()
                : Collections.unmodifiableSet(sessions);
    }

    public ActivationRow activation(String sessionId,
                                    OccurrenceAddress occurrence) {
        return activationOf(sessionId, occurrence.id());
    }

    public List<ActivationRow> activationsOf(OccurrenceAddress occurrence) {
        return activations.getOrDefault(occurrence.id(),
                Collections.<ActivationRow>emptyList());
    }

    public List<DecisionRow> decisionsOf(String sessionId,
                                         OccurrenceAddress occurrence) {
        Derived of = bySession.get(sessionId);
        List<DecisionRow> taken = of == null ? null
                : of.decisions.get(occurrence.id());
        return taken == null ? Collections.<DecisionRow>emptyList() : taken;
    }

    public List<AttachRow> attachesOn(OccurrenceAddress occurrence) {
        return attachesOn.all(occurrence.id());
    }

    public List<TargetRow> targetsOn(OccurrenceAddress occurrence) {
        return targetsOn.all(occurrence.id());
    }

    public TargetRow target(String sessionId, OccurrenceAddress occurrence) {
        List<TargetRow> own = targetsOn.of(occurrence.id(), sessionId);
        return own.isEmpty() ? null : own.get(0);
    }

    public List<ReadRow> readsOn(OccurrenceAddress occurrence) {
        List<ReadRow> all = new ArrayList<ReadRow>();
        for (String session : readersOn.getOrDefault(occurrence.id(),
                Collections.<String>emptySet())) {
            all.addAll(readsOn(session, occurrence));
        }
        return all;
    }

    public List<AttachRow> attachesOn(String sessionId,
                                      OccurrenceAddress occurrence) {
        return attachesOn.of(occurrence.id(), sessionId);
    }

    public List<ReadRow> readsOn(String sessionId,
                                 OccurrenceAddress occurrence) {
        List<ReadRow> own = state(sessionId).readsOn.get(occurrence.id());
        return own == null ? Collections.<ReadRow>emptyList()
                : Collections.unmodifiableList(own);
    }

    public List<WriteRow> writesOn(OccurrenceAddress occurrence) {
        List<WriteRow> all = new ArrayList<WriteRow>();
        for (String session : writersOn.getOrDefault(occurrence.id(),
                Collections.<String>emptySet())) {
            all.addAll(writesOn(session, occurrence));
        }
        return all;
    }

    public List<WriteRow> writesOn(String sessionId,
                                   OccurrenceAddress occurrence) {
        List<WriteRow> own = state(sessionId).writesOn.get(occurrence.id());
        return own == null ? Collections.<WriteRow>emptyList()
                : Collections.unmodifiableList(own);
    }

    public boolean rolePrefix(String sessionId, ReadRow read,
                              OccurrenceAddress occurrence) {
        OccurrenceAddress at = read.endpoint().occurrence();
        if (!at.role() || at.equals(occurrence)
                || !at.node().equals(occurrence.node())
                || !at.context().equals(occurrence.context())) {
            return false;
        }
        long openedSeq = Long.MAX_VALUE;
        int openedTie = 0;
        for (ReadRow row : readsOn(sessionId, occurrence)) {
            if (RowOrder.beforeCut(row.seq(), row.tie(), openedSeq,
                    openedTie)) {
                openedSeq = row.seq();
                openedTie = row.tie();
            }
        }
        for (WriteRow row : writesOn(sessionId, occurrence)) {
            if (RowOrder.beforeCut(row.seq(), row.tie(), openedSeq,
                    openedTie)) {
                openedSeq = row.seq();
                openedTie = row.tie();
            }
        }
        return RowOrder.beforeCut(read.seq(), read.tie(), openedSeq,
                openedTie);
    }


    public List<WriteRow> eligibleWrites(String sessionId, String locationKey,
                                         long observedVersion,
                                         OccurrenceAddress reader) {
        String key = locationKey + "|" + observedVersion + "|"
                + (reader == null ? "" : reader.id());
        StateRows state = state(sessionId);
        List<WriteRow> held = state.eligible.get(key);
        if (held != null) return held;
        List<WriteRow> found = Collections.unmodifiableList(eligibleOf(
                sessionId, locationKey, observedVersion, reader));
        if (state != NO_STATE) state.eligible.put(key, found);
        return found;
    }

    private List<WriteRow> eligibleOf(String sessionId, String locationKey,
                                      long observedVersion,
                                      OccurrenceAddress reader) {
        List<WriteRow> writes = writesOf(sessionId, locationKey);
        List<WriteRow> eligible = new ArrayList<WriteRow>();
        for (WriteRow write : writes) {
            if (arms.eligible(reader, sessionId, locationKey, writes,
                    observedVersion, write)) {
                eligible.add(write);
            }
        }
        return eligible;
    }

    public List<WriteRow> referentStates(WriteRow store, ReadRow read) {
        if (store.referentState() == null) {
            return Collections.<WriteRow>emptyList();
        }
        String session = store.sessionId();
        return SmtLowering.statesOf(writesOf(session, SmtLowering.locationKey(
                store.referentState().location())), store.referentState(),
                read, (reader, writer) -> arms.concurrent(reader, writer,
                        session));
    }

    public boolean fault(String sessionId, DecisionRow decision) {
        if (!Arms.predicate(decision.term())) return false;
        for (String symbol : termSymbols(sessionId, decision.term())) {
            RootMintRow root = rootBySymbol(sessionId, symbol);
            if (root != null && root.category() == RootCategory.FAULT) {
                return true;
            }
        }
        return false;
    }

    public Set<String> termSymbols(String sessionId, String term) {
        Set<String> reached = new LinkedHashSet<String>();
        if (term == null || term.isEmpty()) return reached;
        for (String name : SmtNames.names(term)) {
            if (symbolKind(sessionId, name) != SymbolKind.UNKNOWN) {
                reached.add(name);
            }
        }
        java.util.regex.Matcher refs = EXPRESSION_REF.matcher(term);
        while (refs.find()) {
            reached.addAll(expressionSymbols(sessionId, refs.group()));
        }
        return reached;
    }

    public Set<String> expressionSymbols(String sessionId,
                                         String expressionRef) {
        Derived of = bySession.get(sessionId);
        if (of == null || expressionRef == null) {
            return new LinkedHashSet<String>();
        }
        Set<String> found = of.symbolsByExpression.get(expressionRef);
        if (found != null) return found;
        Set<String> symbols = new LinkedHashSet<String>();
        SmtLowering.SessionJoin join = join(sessionId);
        Deque<JsonElement> roots = new ArrayDeque<JsonElement>();
        JsonElement start = expression(sessionId, expressionRef);
        if (start != null) roots.add(start);
        Set<JsonElement> walked = ExpressionWalk.identitySet();
        while (!roots.isEmpty()) {
            JsonElement root = roots.poll();
            for (ExpressionWalk walk = ExpressionWalk.of(root, walked);
                 walk.hasNext(); ) {
                JsonObject node = walk.next();
                String type = VmExpressionIr.typeOf(node);
                if (VmExpressionIr.SYMBOL_TYPE.equals(type)) {
                    String raw = JsonFields.optionalString(node, "_exp");
                    if (!raw.isEmpty()
                            && !VmExpressionIr.builtinSymbol(raw)) {
                        symbols.add(raw);
                    }
                }
                if (!VmRows.GUARDED_READ_TYPE.equals(type)
                        || !VmRows.joinable(node)) {
                    continue;
                }
                long version = VmRows.recordedVersion(node);
                JsonElement location = node.get("location");
                if (version < 0L || location == null
                        || !location.isJsonObject()) {
                    continue;
                }
                String at = SmtLowering.locationKey(
                        location.getAsJsonObject());
                JsonElement written = join.writeExpression(at, version);
                if (written == null) {
                    symbols.addAll(join.mintedReadSymbols(version));
                    continue;
                }
                if ("ContainerRelation".equals(
                        VmExpressionIr.typeOf(written))) {
                    symbols.addAll(join.readSymbols(at, version));
                }
                roots.add(written);
            }
        }
        Set<String> held = FrozenSet.of(symbols);
        of.symbolsByExpression.put(expressionRef, held);
        return held;
    }

    public Set<String> faultSites(OccurrenceAddress occurrence) {
        Set<String> sites = new LinkedHashSet<String>();
        for (RecordedPath path : pathsOf(occurrence)) {
            for (DecisionRow decision : path.decisions) {
                if (fault(path.sessionId, decision)) {
                    sites.add(decision.siteId());
                }
            }
        }
        return sites;
    }


    @Override
    public JsonObject expression(String sessionId, String expressionRef) {
        SessionReader session = sessionById.get(sessionId);
        return session == null || expressionRef == null ? null
                : session.expressions().expression(expressionRef);
    }

    public ExpressionTable expressions(String sessionId) {
        SessionReader session = sessionById.get(sessionId);
        return session == null ? null : session.expressions();
    }

    public Set<String> leaves(String sessionId, String key,
                              Supplier<Set<String>> compute) {
        Derived of = bySession.get(sessionId);
        if (of == null) return compute.get();
        Set<String> found = of.leaves.get(key);
        if (found == null) {
            found = new HeldLeaves(compute.get());
            of.leaves.put(key, found);
        }
        return found;
    }

    public Set<String> readLeaves(String sessionId, ReadRow read,
                                  Claims claims,
                                  Supplier<Set<String>> compute) {
        Derived of = bySession.get(sessionId);
        if (of == null) return compute.get();
        String key = "read " + read.seq();
        Set<String> found = of.leaves.get(key);
        if (found != null) return found;
        if (claims != null && of.sharedSeqs.contains(read.seq())) {
            return claims.claim(sessionId, read,
                    () -> new HeldLeaves(compute.get()));
        }
        found = new HeldLeaves(compute.get());
        if (of.sharedSeqs.contains(read.seq())) {
            of.sharedBy.put(key, read);
            of.leaves.put(key, found);
            return found;
        }
        Set<String> first = of.leaves.putIfAbsent(key, found);
        return first != null ? first : found;
    }

    public boolean take(Claims claims) {
        for (Claims.Claim claim : claims.claimed.values()) {
            Derived of = bySession.get(claim.sessionId);
            ReadRow by = of.sharedBy.get("read " + claim.read.seq());
            if (by != null && by != claim.read) return false;
        }
        for (Claims.Claim claim : claims.claimed.values()) {
            Derived of = bySession.get(claim.sessionId);
            String key = "read " + claim.read.seq();
            if (of.sharedBy.putIfAbsent(key, claim.read) == null) {
                of.leaves.put(key, claim.leaves);
            }
        }
        return true;
    }

    public static final class Claims {
        private final Map<String, Claim> claimed =
                new LinkedHashMap<String, Claim>();
        private boolean read;
        public final Map<String, Set<String>> held =
                new LinkedHashMap<String, Set<String>>();

        private Set<String> claim(String sessionId, ReadRow read,
                                  Supplier<Set<String>> leaves) {
            String key = sessionId + "|" + read.seq();
            Claim claim = claimed.get(key);
            if (claim == null) {
                claim = new Claim(sessionId, read, leaves.get());
                claimed.put(key, claim);
            }
            this.read = true;
            return claim.leaves;
        }

        public int size() {
            return claimed.size() + held.size();
        }

        public void readHeld() {
            read = true;
        }

        public boolean since() {
            boolean was = read;
            read = false;
            return was;
        }

        public boolean over(boolean was) {
            boolean over = read;
            read = was || over;
            return over;
        }

        public boolean follow(Claims later) {
            for (Map.Entry<String, Claim> each : later.claimed.entrySet()) {
                Claim mine = claimed.get(each.getKey());
                if (mine != null && mine.read != each.getValue().read) {
                    return false;
                }
            }
            for (Map.Entry<String, Claim> each : later.claimed.entrySet()) {
                claimed.putIfAbsent(each.getKey(), each.getValue());
            }
            held.putAll(later.held);
            read |= later.read;
            return true;
        }

        private static final class Claim {
            final String sessionId;
            final ReadRow read;
            final Set<String> leaves;

            Claim(String sessionId, ReadRow read, Set<String> leaves) {
                this.sessionId = sessionId;
                this.read = read;
                this.leaves = leaves;
            }
        }
    }

    static final class HeldLeaves extends AbstractSet<String> {
        private final String[] names;

        HeldLeaves(Set<String> computed) {
            names = new String[computed.size()];
            int at = 0;
            for (String name : computed) names[at++] = NAMES.intern(name);
        }

        @Override
        public Iterator<String> iterator() {
            return Arrays.asList(names).iterator();
        }

        @Override
        public int size() {
            return names.length;
        }
    }

    public static final class StateRead {
        private final String locationKey;
        private final long readEventId;
        private final WriteRow write;
        private final String site;
        private final String javaType;

        private StateRead(String locationKey, long readEventId,
                          WriteRow write, JsonObject node) {
            this.locationKey = locationKey;
            this.readEventId = readEventId;
            this.write = write;
            JsonObject at = node == null ? null : JsonFields.object(node,
                    "site");
            String className = at == null ? ""
                    : JsonFields.optionalString(at, "className");
            String method = at == null ? ""
                    : JsonFields.optionalString(at, "methodName");
            this.site = className.isEmpty() || method.isEmpty() ? ""
                    : Endpoint.stateSite(JvmNames.stable(className)
                            .replace('/', '.'), method,
                    JsonFields.optionalString(at, "methodDescriptor"),
                    Math.max(0, JsonFields.optionalInteger(at, "bci", 0)),
                    false);
            this.javaType = node == null ? ""
                    : JsonFields.optionalString(node, "_java_type");
        }

        public String site() {
            return site;
        }

        public String javaType() {
            return javaType;
        }

        public String locationKey() {
            return locationKey;
        }

        public long readEventId() {
            return readEventId;
        }

        public WriteRow write() {
            return write;
        }
    }

    public List<StateRead> expressionStateReads(String sessionId,
                                                String expressionRef) {
        if (expressionRef == null) return Collections.emptyList();
        StateRows state = state(sessionId);
        List<StateRead> held = state.stateReads.get(expressionRef);
        if (held != null) return held;
        List<StateRead> found = stateReadsOf(sessionId, expressionRef);
        if (state != NO_STATE) state.stateReads.put(expressionRef, found);
        return found;
    }

    private List<StateRead> stateReadsOf(String sessionId,
                                         String expressionRef) {
        List<StateRead> found = new ArrayList<StateRead>();
        JsonObject expression = expression(sessionId, expressionRef);
        if (expression == null) return Collections.unmodifiableList(found);
        Map<String, Long> read = new LinkedHashMap<String, Long>();
        Map<String, JsonObject> nodes = new HashMap<String, JsonObject>();
        readNodes(expression, read, ExpressionWalk.identitySet(), nodes);
        for (Map.Entry<String, Long> each : read.entrySet()) {
            WriteRow latest = null;
            for (WriteRow write : writesOf(sessionId, each.getKey())) {
                if (write.version() > each.getValue().longValue()) continue;
                if (latest == null || latest.version() < write.version()) {
                    latest = write;
                }
            }
            if (latest == null) continue;
            found.add(new StateRead(each.getKey(),
                    each.getValue().longValue(), latest,
                    nodes.get(each.getKey())));
        }
        return Collections.unmodifiableList(found);
    }

    public Set<String> readLocations(String sessionId, String term) {
        String key = term == null ? "" : term;
        Derived of = bySession.get(sessionId);
        Set<String> held = of == null ? null : of.readLocations.get(key);
        if (held != null) return held;
        Set<String> found = readLocationsOf(sessionId, key);
        if (of != null) of.readLocations.put(key, found);
        return found;
    }

    private Set<String> readLocationsOf(String sessionId, String term) {
        Map<String, Long> read = new LinkedHashMap<String, Long>();
        java.util.regex.Matcher refs = EXPRESSION_REF.matcher(
                term == null ? "" : term);
        Set<JsonElement> walked = ExpressionWalk.identitySet();
        while (refs.find()) {
            readNodes(expression(sessionId, refs.group()), read, walked,
                    null);
        }
        return FrozenSet.of(read.keySet());
    }

    public Set<Long> readEvents(String sessionId, String term) {
        String key = term == null ? "" : term;
        Derived of = bySession.get(sessionId);
        Set<Long> held = of == null ? null : of.readEvents.get(key);
        if (held != null) return held;
        Set<Long> found = readEventsOf(sessionId, key);
        if (of != null) of.readEvents.put(key, found);
        return found;
    }

    private Set<Long> readEventsOf(String sessionId, String term) {
        Set<Long> events = new LinkedHashSet<Long>();
        java.util.regex.Matcher refs = EXPRESSION_REF.matcher(
                term == null ? "" : term);
        Set<JsonElement> walked = ExpressionWalk.identitySet();
        while (refs.find()) {
            for (ExpressionWalk walk = ExpressionWalk.of(
                    expression(sessionId, refs.group()), walked);
                 walk.hasNext(); ) {
                JsonObject node = walk.next();
                JsonElement at = node.get("readEventId");
                if (node.get("location") != null && at != null
                        && at.isJsonPrimitive()) {
                    events.add(Long.valueOf(at.getAsLong()));
                }
            }
        }
        return FrozenSet.of(events);
    }

    static final java.util.regex.Pattern EXPRESSION_REF =
            java.util.regex.Pattern.compile("EXPR\\.[0-9a-f]+");

    private static void readNodes(JsonElement expression,
                                  Map<String, Long> into,
                                  Set<JsonElement> walked,
                                  Map<String, JsonObject> nodes) {
        for (ExpressionWalk walk = ExpressionWalk.of(expression, walked);
             walk.hasNext(); ) {
            JsonObject node = walk.next();
            JsonElement location = node.get("location");
            JsonElement at = node.get("readEventId");
            if (location == null || !location.isJsonObject() || at == null
                    || !at.isJsonPrimitive()) {
                continue;
            }
            String key = SmtLowering.locationKey(location.getAsJsonObject());
            long event = at.getAsLong();
            Long held = into.get(key);
            if (held == null || held.longValue() < event) {
                into.put(key, Long.valueOf(event));
                if (nodes != null) nodes.put(key, node);
            }
        }
    }

    public Map<String, Interaction> interactions() {
        return Collections.unmodifiableMap(interactions);
    }

    public Map<String, Sort> declaredSymbols() {
        return Collections.unmodifiableMap(declaredSymbols);
    }

    public Map<String, Set<String>> collidingRootSymbols() {
        Map<String, Set<String>> collisions =
                new LinkedHashMap<String, Set<String>>();
        for (Map.Entry<String, Set<String>> entry
                : rootIdsBySymbol.entrySet()) {
            if (entry.getValue().size() > 1) {
                collisions.put(entry.getKey(), entry.getValue());
            }
        }
        return collisions;
    }

    @Override
    public List<AttachRow> attachesOf(Interaction interaction) {
        return attachesByInteraction.getOrDefault(interaction.id(),
                Collections.<AttachRow>emptyList());
    }

    @Override
    public List<ExportRow> exportsOf(Endpoint producer) {
        if (producer == null) return Collections.emptyList();
        return exports.getOrDefault(producer.id(),
                Collections.<ExportRow>emptyList());
    }

    @Override
    public List<AttachRow> ownAttachesOf(String sessionId,
                                         Interaction interaction) {
        Derived of = bySession.get(sessionId);
        List<AttachRow> own = of == null ? null
                : of.ownAttaches.get(interaction.id());
        return own == null ? Collections.<AttachRow>emptyList() : own;
    }

    @Override
    public List<ExportRow> ownExportsOf(String sessionId, Endpoint producer) {
        Derived of = producer == null ? null : bySession.get(sessionId);
        List<ExportRow> own = of == null ? null
                : of.ownExports.get(producer.id());
        return own == null ? Collections.<ExportRow>emptyList() : own;
    }

    @Override
    public List<WriteRow> writesOf(String sessionId, String locationKey) {
        return join(sessionId).writes(locationKey);
    }

    @Override
    public List<ReadRow> readsOf(String sessionId, String locationKey) {
        return join(sessionId).reads(locationKey);
    }

    public Collection<WriteRow> writeSitesOf(String locationKey) {
        Map<List<String>, WriteRow> sites =
                writeSitesByLocation.get(locationKey);
        return sites == null ? Collections.<WriteRow>emptyList()
                : Collections.unmodifiableCollection(sites.values());
    }

    @Override
    public String pathIdOf(String sessionId, OccurrenceAddress occurrence) {
        return pathId(sessionId, occurrence);
    }

    @Override
    public RootMintRow root(String rootId, String sessionId) {
        return rootOf(sessionId, rootId);
    }

    @Override
    public boolean varied(String rootId) {
        return varied.computeIfAbsent(rootId, id -> {
            Set<String> values = new LinkedHashSet<String>();
            for (SessionReader session : sessions) {
                String value = rootValue(session.sessionId(), id);
                if (!value.isEmpty()) values.add(value);
            }
            return values.size() > 1;
        });
    }

    @Override
    public RootMintRow ranRoot(String rootId, String sessionId) {
        RootMintRow own = rootOf(sessionId, rootId);
        return own != null ? own : readAt(sessionId, rootId);
    }

    public boolean derived(String rootId) {
        return derived.computeIfAbsent(rootId, id -> {
            for (SessionReader session : sessions) {
                if (session.manifest() != null
                        && session.manifest().derivedRoots().contains(id)) {
                    return true;
                }
            }
            return false;
        });
    }

    private RootMintRow readAt(String sessionId, String rootId) {
        Map<String, String> readings = concreteReadings(sessionId, rootId);
        Map<String, RootMintRow> minted = rootsById.get(rootId);
        if (readings.isEmpty() || minted == null || derived(rootId)) {
            return null;
        }
        List<RootMintRow> order = new ArrayList<RootMintRow>();
        RootMintRow seed = minted.get(seedSessionId());
        if (seed != null) order.add(seed);
        order.addAll(minted.values());
        for (RootMintRow mint : order) {
            if (mint.occurrence() != null
                    && readings.containsKey(mint.occurrence().render())) {
                return mint;
            }
        }
        return null;
    }

    private Map<String, String> concreteReadings(String sessionId,
                                                 String rootId) {
        SessionReader session = sessionById.get(sessionId);
        Map<String, String> readings = session == null
                || session.manifest() == null ? null
                : session.manifest().concreteReadings().get(rootId);
        return readings == null ? Collections.<String, String>emptyMap()
                : readings;
    }

    @Override
    public synchronized Map<String, List<RootMintRow>> roots() {
        if (roots == null) {
            Map<String, List<RootMintRow>> byRoot =
                    new LinkedHashMap<String, List<RootMintRow>>();
            for (Map.Entry<String, Map<String, RootMintRow>> entry
                    : rootsById.entrySet()) {
                List<RootMintRow> rows = new ArrayList<RootMintRow>();
                for (RootMintRow row : entry.getValue().values()) {
                    if (row.seq() < forcedFrom(row.sessionId())) rows.add(row);
                }
                if (!rows.isEmpty()) {
                    byRoot.put(entry.getKey(),
                            Collections.unmodifiableList(rows));
                }
            }
            roots = Collections.unmodifiableMap(byRoot);
        }
        return roots;
    }

    @Override
    public AttachRow attachOfSymbol(String symbol, String sessionId) {
        return attach(sessionId, symbol);
    }

    @Override
    public OccurrenceAddress occurrenceOf(String endpointId) {
        return occurrenceByEndpoint.get(endpointId);
    }

    @Override
    public ActivationRow activationOf(String sessionId,
                                      String occurrenceId) {
        Derived of = bySession.get(sessionId);
        return of == null ? null : of.activationByOccurrence.get(occurrenceId);
    }

    public Arms arms() {
        return arms;
    }

    public WriteRow writeOf(String sessionId, LocationId location,
                            long version) {
        return writeOf(sessionId, SmtLowering.locationKey(location), version);
    }

    public WriteRow writeOf(String sessionId, String locationKey,
                            long version) {
        return version < 0 ? null : join(sessionId).write(locationKey,
                version);
    }

    public Set<String> touching(OccurrenceAddress occurrence,
                                LocationId location) {
        Set<String> found = locationTouches.get(touchKey(occurrence,
                location));
        return found == null ? Collections.<String>emptySet() : found;
    }

    public AttachRow attach(String sessionId, String symbol) {
        Derived of = bySession.get(sessionId);
        return of == null ? null : of.attachBySymbol.get(symbol);
    }

    public boolean handoffSymbol(String symbol) {
        return handoffSymbols.contains(symbol);
    }

    public RootMintRow rootBySymbol(String sessionId, String symbol) {
        Derived of = bySession.get(sessionId);
        return of == null ? null : of.rootBySymbol.get(symbol);
    }

    public ReadRow read(String sessionId, String symbol) {
        return state(sessionId).readBySymbol.get(symbol);
    }

    public SymbolKind symbolKind(String sessionId, String symbol) {
        Derived of = bySession.get(sessionId);
        if (of == null) return SymbolKind.UNKNOWN;
        if (of.rootBySymbol.containsKey(symbol)) return SymbolKind.ROOT;
        if (of.attachBySymbol.containsKey(symbol)) return SymbolKind.HANDOFF;
        if (state(sessionId).readBySymbol.containsKey(symbol)) {
            return SymbolKind.READ;
        }
        return SymbolKind.UNKNOWN;
    }

    @Override
    public String rootValue(String sessionId, String rootId) {
        String wave = world(sessionId).rootAssignments.get(rootId);
        if (wave != null && !wave.isEmpty()) return wave;
        if (rootOf(sessionId, rootId) != null) {
            return rootReading(sessionId, rootId);
        }
        RootMintRow read = readAt(sessionId, rootId);
        return read == null ? "" : concreteReadings(sessionId, rootId)
                .get(read.occurrence().render());
    }

    public String rootReading(String sessionId, String rootId) {
        RootMintRow row = rootOf(sessionId, rootId);
        return row == null || row.recordedValue() == null
                ? "" : row.recordedValue();
    }

    public RootMintRow rootOf(String sessionId, String rootId) {
        Map<String, RootMintRow> bySession = rootsById.get(rootId);
        return bySession == null ? null : bySession.get(sessionId);
    }

    public RootMintRow mintOf(String pathSessionId, String rootId) {
        RootMintRow seed = rootOf(seedSessionId(), rootId);
        return seed != null ? seed : rootOf(pathSessionId, rootId);
    }

    public RootMintRow anyRoot(String rootId) {
        Map<String, RootMintRow> bySession = rootsById.get(rootId);
        return bySession == null || bySession.isEmpty() ? null
                : bySession.values().iterator().next();
    }

    public RootDomain declaredDomain(String rootId) {
        return declaredDomains.get(rootId);
    }

    public RootDomain domainOf(RootMintRow root) {
        return RootDomain.resolved(root, declaredDomains,
                comparedLiterals(root.symbol()));
    }

    public RootDomain domainOf(RootMintRow root, String reading) {
        return RootDomain.resolved(root, reading, declaredDomains);
    }

    private final Map<String, Set<java.math.BigInteger>> compared =
            new ConcurrentHashMap<String, Set<java.math.BigInteger>>();

    void configurationLiterals() {
        Map<String, Pattern> roots = new LinkedHashMap<String, Pattern>();
        for (Derived of : bySession.values()) {
            for (RootMintRow mint : of.rootBySymbol.values()) {
                if (mint.kind() == RootKind.INTEGRAL
                        && mint.category() == RootCategory.CONFIG
                        && !compared.containsKey(mint.symbol())) {
                    roots.computeIfAbsent(mint.symbol(), Corpus::comparing);
                }
            }
        }
        List<Map.Entry<String, Map.Entry<String, DecisionRow>>> asked =
                new ArrayList<Map.Entry<String,
                        Map.Entry<String, DecisionRow>>>();
        for (String symbol : roots.keySet()) {
            for (Map.Entry<String, DecisionRow> decided : deciding(symbol)) {
                asked.add(new java.util.AbstractMap.SimpleImmutableEntry<
                        String, Map.Entry<String, DecisionRow>>(symbol,
                        decided));
            }
        }
        List<Set<java.math.BigInteger>> found;
        try {
            found = Parallel.grouped(asked, one -> one.getValue().getKey(),
                    one -> literals(roots.get(one.getKey()),
                            one.getValue().getKey(),
                            one.getValue().getValue()));
        } catch (IOException unreadable) {
            throw new UncheckedIOException(unreadable);
        }
        Map<String, Set<java.math.BigInteger>> literals =
                new LinkedHashMap<String, Set<java.math.BigInteger>>();
        for (String symbol : roots.keySet()) {
            literals.put(symbol, new java.util.TreeSet<java.math.BigInteger>());
        }
        for (int at = 0; at < asked.size(); at++) {
            literals.get(asked.get(at).getKey()).addAll(found.get(at));
        }
        compared.putAll(literals);
    }

    private Map<String, List<Map.Entry<String, DecisionRow>>> deciding;

    private synchronized List<Map.Entry<String, DecisionRow>> deciding(
            String symbol) {
        if (deciding == null) {
            Set<String> wanted = new HashSet<String>();
            for (Map<String, RootMintRow> mints : rootsById.values()) {
                for (RootMintRow mint : mints.values()) {
                    wanted.add(mint.symbol());
                }
            }
            deciding = new HashMap<String,
                    List<Map.Entry<String, DecisionRow>>>();
            for (Derived of : bySession.values()) {
                String sessionId = of.session.sessionId();
                for (List<DecisionRow> path : of.decisions.values()) {
                    for (DecisionRow decision : path) {
                        if (!Arms.predicate(decision.term())) continue;
                        for (String reached
                                : termSymbols(sessionId, decision.term())) {
                            if (!wanted.contains(reached)) continue;
                            deciding.computeIfAbsent(reached, k ->
                                    new ArrayList<Map.Entry<String,
                                            DecisionRow>>()).add(
                                    new java.util.AbstractMap
                                            .SimpleImmutableEntry<String,
                                            DecisionRow>(sessionId,
                                            decision));
                        }
                    }
                }
            }
        }
        List<Map.Entry<String, DecisionRow>> reaching = deciding.get(symbol);
        return reaching == null
                ? Collections.<Map.Entry<String, DecisionRow>>emptyList()
                : reaching;
    }

    Set<java.math.BigInteger> comparedLiterals(String symbol) {
        Asking question = asking.get();
        Map<String, Set<java.math.BigInteger>> memo = question == null
                ? compared : question.compared;
        Set<java.math.BigInteger> known = memo.get(symbol);
        if (known != null) return known;
        Set<java.math.BigInteger> literals =
                new java.util.TreeSet<java.math.BigInteger>();
        Pattern atom = comparing(symbol);
        for (Map.Entry<String, DecisionRow> decided : deciding(symbol)) {
            literals.addAll(literals(atom, decided.getKey(),
                    decided.getValue()));
        }
        memo.put(symbol, literals);
        return literals;
    }

    private static Pattern comparing(String symbol) {
        String name = Pattern.quote(symbol);
        String literal = "(-?[0-9]+|\\(-\\s+[0-9]+\\))";
        return Pattern.compile("\\((?:<=|>=|<|>|=)\\s+(?:" + literal
                + "\\s+\\|?" + name + "\\|?|\\|?" + name + "\\|?\\s+"
                + literal + ")\\)");
    }

    private Set<java.math.BigInteger> literals(Pattern atom, String sessionId,
                                               DecisionRow decision) {
        Set<java.math.BigInteger> literals =
                new java.util.TreeSet<java.math.BigInteger>();
        Matcher found = atom.matcher(FlipQuery.statedTerm(this, sessionId,
                decision.term()));
        while (found.find()) {
            String spelled = found.group(1) != null
                    ? found.group(1) : found.group(2);
            literals.add(new java.math.BigInteger(spelled
                    .replaceAll("[()\\s]", "")));
        }
        return literals;
    }
}

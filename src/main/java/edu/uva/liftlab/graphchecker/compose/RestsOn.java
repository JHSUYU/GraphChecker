package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.FrozenSet;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.JvmNames;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RowOrder;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.explore.Corpus;
import edu.uva.liftlab.graphchecker.plan.ForcingTable;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.ExpressionWalk;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.smt.VmRows;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Supplier;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public final class RestsOn {
    private final Corpus corpus;
    private final StaticScopeMap scope;
    private final OccurrenceAddress anchor;
    private final Map<String, Set<String>> cache =
            new ConcurrentHashMap<String, Set<String>>();

    public RestsOn(Corpus corpus, StaticScopeMap scope,
                   OccurrenceAddress anchor) {
        this.corpus = corpus;
        this.scope = scope;
        this.anchor = anchor;
    }

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
        boolean reached = reached();
        for (TargetRow target : targets) {
            String session = target.sessionId();
            Corpus.RecordedPath path = corpus.path(session, anchor);
            if (reached && !target.reachedAnchor()) {
                gap(gaps, GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        session, "this session ran the occurrence "
                                + "and did not reach the anchor");
                if (path != null && settled(session, null)) {
                    cut(gaps, session, decided(session, target,
                            path.decisions));
                }
                continue;
            }
            if (path == null) {
                gap(gaps, GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        session, "this session ran the occurrence and "
                                + "published no path at it");
                continue;
            }
            if (!settled(session, gaps)) {
                if (target.reachedAnchor()) {
                    gap(gaps, GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                            session, "this session reached the anchor"
                                    + (target.observedFatal()
                                    ? " and threw the target" : "")
                                    + " in a replay its own rows do not "
                                    + "admit: no disjunct, and it drops no "
                                    + "path (solr-adhoc-19 F2V4: such a "
                                    + "replay made COMPOSE drop 63)");
                }
                continue;
            }
            admitted.add(path);
        }
        admitted.addAll(corpus.forcedPaths(anchor));
        return admitted;
    }

    public boolean reached() {
        if (reached == null) {
            boolean any = false;
            for (TargetRow target : corpus.targetsOn(anchor)) {
                any |= target.reachedAnchor()
                        && corpus.path(target.sessionId(), anchor) != null
                        && settled(target.sessionId(), null);
            }
            reached = Boolean.valueOf(any);
        }
        return reached.booleanValue();
    }

    private Boolean reached;

    private boolean settled(String session, List<GapRow> gaps) {
        SessionReader reader = corpus.session(session);
        if (reader == null || reader.seed()) return true;
        Set<String> stated = new LinkedHashSet<String>();
        boolean admitted = reader.admitted();
        for (ObligationResult result : reader.obligations()) {
            stated.add(result.obligationId());
            if (result.verdict() == Verdict.ADMITTED || gaps == null) {
                continue;
            }
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
            if (gaps == null) continue;
            gap(gaps, GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, obligation,
                    "session " + session + " states it ran this obligation "
                            + "and publishes no verdict for it, so it is left"
                            + " out");
        }
        return admitted;
    }

    void cut(List<GapRow> gaps, String session, Decided decided) {
        if (!decided.defect.isEmpty()) {
            gap(gaps, GapKind.BOUND_INSUFFICIENT, GapClass.DIAGNOSTIC,
                    anchor.render(), "session " + session + ": the loop"
                            + " accounting at the anchor failed, an engine"
                            + " defect and no bound: " + decided.defect);
        }
        if (!decided.cut.isEmpty()) {
            gap(gaps, GapKind.BOUND_INSUFFICIENT, GapClass.DIAGNOSTIC,
                    anchor.render() + " " + Composer.LOOP_BODY_BOUND + "="
                            + boundOf(decided.cut), "session " + session
                            + " reached no point of the anchor and a loop"
                            + " bound cut its occurrence "
                            + (decided.way == null ? "before it left the way"
                            + " to the throw at any guard" : "after it left"
                            + " the way at " + decided.way.siteId() + "#"
                            + decided.way.ordinal()) + ": " + decided.cut);
        }
    }

    private void gap(List<GapRow> gaps, GapKind kind, GapClass cls,
                     String subject, String detail) {
        gaps.add(GapRow.of(Composer.COMPOSITION, kind, cls,
                subject == null || subject.trim().isEmpty()
                        ? anchor.render() : subject, detail));
    }

    static final class Decided {
        final DecisionRow way;
        final boolean symbolicWay;
        final long cutoff;
        final String fatalTerm;
        final String cut;
        final String defect;

        private Decided(DecisionRow way, boolean symbolicWay, long cutoff,
                        String fatalTerm, String cut, String defect) {
            this.way = way;
            this.symbolicWay = symbolicWay;
            this.cutoff = cutoff;
            this.fatalTerm = fatalTerm;
            this.cut = cut;
            this.defect = defect;
        }
    }

    Decided decided(String session, TargetRow target,
                    List<DecisionRow> decisions) {
        DecisionRow way = target.reachedAnchor() ? null
                : wayGuard(target, decisions);
        boolean symbolicWay = way != null
                && !corpus.termSymbols(session, way.term()).isEmpty();
        long cutoff = target.reachedAnchor() ? target.seq()
                : way == null ? Long.MAX_VALUE : way.seq();
        String fatalTerm = target.reachedAnchor() ? target.phiTerm()
                : symbolicWay ? Arms.conjunct(way.term(), !way.outcome())
                : "false";
        String cut = target.reachedAnchor() ? "" : cutOf(session);
        boolean defect = !cut.isEmpty() && !boundReached(cut);
        return new Decided(way, symbolicWay, cutoff, fatalTerm,
                defect ? "" : cut, defect ? cut : "");
    }

    static boolean boundReached(String cut) {
        for (String reason : LoopBoundPolicy.BOUND_REACHED) {
            if (cut.contains(reason)) return true;
        }
        return false;
    }

    DecisionRow wayGuard(TargetRow target, List<DecisionRow> decisions) {
        StaticScopeMap.Site own = scope.ownTarget(target.site());
        if (own == null) return null;
        Set<String> way = own.pathSites();
        Map<String, ForcingTable.Arm> table =
                ForcingTable.read(scope.forcing(own.siteId));
        for (int index = decisions.size() - 1; index >= 0; index--) {
            DecisionRow decision = decisions.get(index);
            if (!way.contains(decision.siteId())) continue;
            ForcingTable.Arm arm = table.get(decision.siteId());
            if (arm == null) return decision;
            if (!arm.via.isEmpty() && !decision.via().isEmpty()
                    && !JvmNames.stable(arm.via).equals(decision.via())) {
                continue;
            }
            if (!arm.passable && arm.arm != decision.outcome()) {
                return decision;
            }
        }
        return null;
    }

    String cutOf(String session) {
        SessionReader reader = corpus.session(session);
        if (reader == null) return "";
        for (GapRow gap : reader.gaps(GapKind.BOUND_INSUFFICIENT)) {
            try {
                if (OccurrenceAddress.parse(gap.subject()).id()
                        .equals(anchor.id())) {
                    return gap.detail();
                }
            } catch (IllegalArgumentException noOccurrence) {
            }
        }
        return "";
    }

    static int boundOf(String cut) {
        Matcher bound = CUT_BOUND.matcher(cut == null ? "" : cut);
        return bound.find() ? Integer.parseInt(bound.group(1) != null
                ? bound.group(1) : bound.group(2)) : 0;
    }

    private static final Pattern CUT_BOUND = Pattern.compile(
            "after (\\d+) loop body iterations|exceeds (\\d+)");

    public Set<String> ofDelivery(String session, OccurrenceAddress start,
                                  long cutoff, List<String> delivered,
                                  Corpus.Claims claims) {
        return named("delivery", session, start, cutoff, delivered,
                () -> seedWrites(session, delivered),
                Collections.<DecisionRow>emptyList(), claims);
    }

    public Set<String> ofPath(String session, TargetRow target,
                              List<DecisionRow> decisions,
                              Corpus.Claims claims) {
        Decided at = decided(session, target, decisions);
        return named("path", session, anchor, at.cutoff,
                Collections.singletonList(at.fatalTerm), () -> null,
                before(decisions, at.cutoff), claims);
    }

    private Set<String> named(String kind, String session,
                              OccurrenceAddress start, long cutoff,
                              List<String> seedTerms,
                              Supplier<List<WriteRow>> seeds,
                              List<DecisionRow> own, Corpus.Claims claims) {
        String key = kind + "|" + session + "|" + start.id() + "|" + cutoff
                + "|" + seedTerms;
        Set<String> held = cache.get(key);
        if (held != null) return held;
        if (claims != null) {
            held = claims.held.get(key);
            if (held != null) {
                claims.readHeld();
                return held;
            }
        }
        boolean around = claims != null && claims.since();
        Map<String, Long> reached = closure(session, start, cutoff,
                seeds.get());
        List<DecisionRow> conditions = new ArrayList<DecisionRow>(own);
        conditions.addAll(reachedConditions(session, reached));
        Independence kept = independence(session, seedTerms,
                Collections.<String>emptySet(), reached, conditions, claims);
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
        Set<String> answer = FrozenSet.of(symbols);
        if (claims != null && claims.over(around)) {
            claims.held.put(key, answer);
            return answer;
        }
        Set<String> first = cache.putIfAbsent(key, answer);
        return first != null ? first : answer;
    }

    public boolean take(Corpus.Claims claims) {
        if (!corpus.take(claims)) return false;
        for (Map.Entry<String, Set<String>> answer : claims.held.entrySet()) {
            cache.putIfAbsent(answer.getKey(), answer.getValue());
        }
        return true;
    }

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

    List<ReadRow> statedRows(String session, Set<String> occurrences) {
        List<ReadRow> rows = new ArrayList<ReadRow>();
        Set<String> stated = new LinkedHashSet<String>();
        SessionReader reader = corpus.session(session);
        if (reader != null) {
            for (ReadRow read : reader.reads()) {
                if (read.mintVersion() >= 0L && read.symbol() != null
                        && !read.symbol().isEmpty()
                        && stated.add(read.symbol())) {
                    rows.add(read);
                }
            }
        }
        for (String occurrenceId : occurrences) {
            OccurrenceAddress at = corpus.occurrence(occurrenceId);
            if (at == null) continue;
            for (ReadRow read : corpus.readsOn(session, at)) {
                if (read.location().kind() == LocationKind.STORE) continue;
                if (read.symbol() == null || stated.add(read.symbol())) {
                    rows.add(read);
                }
            }
        }
        return rows;
    }

    Set<String> storeLocations(String session, Reached reached) {
        Set<String> locations = new LinkedHashSet<String>();
        for (Map.Entry<String, Long> each : reached.entrySet()) {
            OccurrenceAddress at = corpus.occurrence(each.getKey());
            if (at == null) continue;
            for (ReadRow read : corpus.readsOn(session, at)) {
                if (read.location().kind() == LocationKind.STORE
                        && reached.before(each.getKey(), read)) {
                    locations.add(SmtLowering.locationKey(read.location()));
                }
            }
        }
        return locations;
    }

    Reached closure(String session, OccurrenceAddress start,
                    long cutoff, List<WriteRow> seeds) {
        return closure(log(session), anchor, start, cutoff, seeds, true,
                null);
    }

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

    public interface Log {
        List<ReadRow> readsOn(String occurrenceId);

        WriteRow writeOf(String locationKey, long version);

        List<WriteRow> writesOf(String locationKey);
    }

    public interface Reads {
        void joined(ReadRow read, WriteRow write);

        void past(ReadRow read);
    }

    public static Reached closure(Log log, OccurrenceAddress anchor,
                                 OccurrenceAddress start, long cutoff,
                                 List<WriteRow> seeds, boolean anchorWhole,
                                 Reads reads) {
        Reached reached = new Reached();
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
                for (ReadRow read : log.readsOn(at)) {
                    if (!whole && !reached.before(at, read)) {
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

    private static void reach(WriteRow write, OccurrenceAddress anchor,
                              OccurrenceAddress start, Reached reached,
                              List<String> pending, List<WriteRow> versions,
                              Set<String> handled) {
        String writer = write.endpoint().occurrence().id();
        if (write.initial() || anchor.id().equals(writer)
                || start.id().equals(writer)) {
            return;
        }
        if (handled.add(SmtLowering.locationKey(write.location()) + "#"
                + write.version())) {
            versions.add(write);
        }
        if (!reached.extend(writer, write)) return;
        pending.add(writer);
    }

    public static final class Reached extends LinkedHashMap<String, Long> {
        private static final long serialVersionUID = 1L;
        private final Map<String, Integer> ties = new HashMap<String, Integer>();

        boolean extend(String occurrence, WriteRow write) {
            Long held = get(occurrence);
            if (held != null && RowOrder.compare(write.seq(), write.tie(),
                    held, ties.getOrDefault(occurrence, 0)) <= 0) {
                return false;
            }
            put(occurrence, write.seq());
            if (write.tie() > 0) {
                ties.put(occurrence, write.tie());
            } else {
                ties.remove(occurrence);
            }
            return true;
        }

        public boolean before(String occurrence, ReadRow read) {
            Long cut = get(occurrence);
            return cut != null && RowOrder.beforeCut(read.seq(), read.tie(),
                    cut, ties.getOrDefault(occurrence, 0));
        }
    }

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

    static List<DecisionRow> before(List<DecisionRow> decisions,
                                            long seq) {
        List<DecisionRow> earlier = new ArrayList<DecisionRow>();
        for (DecisionRow decision : decisions) {
            if (decision.seq() < seq) earlier.add(decision);
        }
        return earlier;
    }

    Independence independence(String session, List<String> seeds,
                              Collection<String> bound,
                              Map<String, Long> reached,
                              List<DecisionRow> conditions) {
        return independence(session, seeds, bound, reached, conditions,
                null);
    }

    private Independence independence(String session, List<String> seeds,
                                      Collection<String> bound,
                                      Map<String, Long> reached,
                                      List<DecisionRow> conditions,
                                      Corpus.Claims claims) {
        return Independence.of(corpus, session, seeds, bound, conditions,
                statedRows(session, reached.keySet()),
                read -> constructionGuards(session, corpus.writeOf(session,
                        read.location(), read.observedVersion())), claims);
    }

    private final Map<String, List<DecisionRow>> built =
            new ConcurrentHashMap<String, List<DecisionRow>>();

    List<DecisionRow> constructionGuards(String session, WriteRow write) {
        if (write == null || write.referentState() == null) {
            return Collections.<DecisionRow>emptyList();
        }
        String key = session + "|" + write.location() + "@" + write.version();
        List<DecisionRow> held = built.get(key);
        if (held != null) return held;
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
        if (!sites.isEmpty()) {
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
        }
        held = built.putIfAbsent(key, guards);
        return held != null ? held : guards;
    }

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

    static JsonElement unwrapped(JsonElement value) {
        JsonElement found = value;
        while (VmExpressionIr.consumerBoundary(found)) {
            found = found.getAsJsonObject().get(VmExpressionIr.EXPRESSION);
        }
        return found;
    }
}

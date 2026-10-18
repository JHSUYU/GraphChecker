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
     *  ({@link #named}): EXPLORE asks once per walk of a demand, from any
     *  core its supersteps run on; a function of the corpus, the map and
     *  the key alone, so whichever core computes it first holds it, each
     *  answer a {@link FrozenSet} (SGF8-adhoc-05 round 5: 18 M symbols in
     *  53 K answers). */
    private final Map<String, Set<String>> cache =
            new ConcurrentHashMap<String, Set<String>>();

    public RestsOn(Corpus corpus, StaticScopeMap scope,
                   OccurrenceAddress anchor) {
        this.corpus = corpus;
        this.scope = scope;
        this.anchor = anchor;
    }

    /**
     * THE ADMITTED PATHS, COMPOSE's disjuncts and EXPLORE's demand alike
     * (PIPELINE §7.2, §8), each refusal a row of {@code gaps}: every
     * admitted session's path that reached the anchor, or, where none did
     * ({@link #reached}), every admitted session's path that ran the
     * occurrence (its way guard's other arm its fatal, or the constant
     * healthy decision).  A session its own rows do not admit is no disjunct
     * and drops none, even where it reached the anchor or threw there.  The
     * declared occurrence is always the anchor; a corpus without a target
     * row for it never ran it, a defect, never a reason to elect another
     * occurrence.
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
        // Beside an admitted path that reached the anchor, a path that left
        // the way to the throw adds no disjunct (its fatal arm is the
        // constant healthy decision, or the flip of a guard a reaching path
        // already holds).
        boolean reached = reached();
        for (TargetRow target : targets) {
            String session = target.sessionId();
            Corpus.RecordedPath path = corpus.path(session, anchor);
            if (reached && !target.reachedAnchor()) {
                gap(gaps, GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        session, "this session ran the occurrence "
                                + "and did not reach the anchor");
                // Its cut still bounds the search, where its own rows admit
                // it: the worlds it would have run on are not composed.
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
        // And each forced path (PIPELINE §7.10): the recording's world with
        // the anchor forced to the throw, its phi the forced path condition.
        admitted.addAll(corpus.forcedPaths(anchor));
        return admitted;
    }

    /**
     * Whether a session whose own rows admit it ({@link #settled}) reached
     * the anchor at a path it published: THE rule COMPOSE's admission and
     * EXPLORE's flip sites ({@code ClosurePlanner#plan}) read, once per
     * corpus.  A replay that refused its own obligation is the recording
     * again under a valuation it did not take: its reach states nothing.
     */
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

    /**
     * Whether this session's OWN rows admit the obligation it ran (the
     * replay owns the verdict).  A refused obligation's path is the
     * recording again under a valuation the run did not take, so it is no
     * disjunct.  A SEED admits itself; an obligation the manifest names and
     * no row settles is BLOCKING.  {@code gaps} null: asked quietly.
     */
    private boolean settled(String session, List<GapRow> gaps) {
        SessionReader reader = corpus.session(session);
        if (reader == null || reader.seed()) return true;
        Set<String> stated = new LinkedHashSet<String>();
        // {@link SessionReader#admitted} decides; this only names refusals.
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

    /**
     * Names what a path that never reached the anchor rests on, as a gap of
     * {@code gaps}: a loop bound's cut of its occurrence, a DIAGNOSTIC
     * {@code <anchor> loop-body-bound=<N>} row the case's {@code bounded}
     * counts (run_engine.sh campaign_bounds: {@code loop_body_bound}), so its
     * UNSAT is not done (CHECKING §1); a failure of the anchor's loop
     * accounting, a DIAGNOSTIC row: an engine defect, never a bound.
     */
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
         *  the throw; else (a concrete one, or none) the constant false. */
        final String fatalTerm;
        /** Where it reached the anchor at no point and a loop bound cut
         *  its occurrence -- before it left the way at a guard or after:
         *  a later turn of a loop, in its method or a caller's, may have
         *  come back to the way -- the cut; else "". */
        final String cut;
        /** Where the anchor's loop accounting itself failed (a policy
         *  mismatch, a hook failure: {@link #boundReached} false), its row;
         *  an engine defect, never a bound. */
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

    /**
     * Where a path decided: at its target row, or, where it never reached
     * the anchor, at the guard it left the way to the throw at (a row that
     * did not reach the anchor stands at no point of it).  One that left it
     * at none stopped on the way -- a loop bound cut its occurrence
     * ({@link #cutOf}), an exception or a return no table branch decided --
     * and states no arm toward the throw: its fatal is the constant false,
     * named with how it stopped (Composer: the WAY row, and a cut's bound).
     */
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

    /** Whether a cut's row says a bound was reached ({@code
     *  plan.LoopBoundPolicy#BOUND_REACHED}): the loop's K_L or the work
     *  cap, not the accounting's own failure. */
    static boolean boundReached(String cut) {
        for (String reason : LoopBoundPolicy.BOUND_REACHED) {
            if (cut.contains(reason)) return true;
        }
        return false;
    }

    /**
     * The guard a path left the way to the throw at: the last decision at a
     * site on the way (the anchor's own TARGET_SITE's path sites, {@link
     * StaticScopeMap#ownTarget}, never another throw's) that took an arm off
     * it.  Scanned back past the decisions that kept the way -- the arm its
     * forcing table names toward the throw, or a {@code passable} branch,
     * either arm of which leads on -- and past a decider ({@code via}
     * stated) decided in a call from elsewhere than its row's {@code via},
     * which is no decision of the way ({@code DecisionRow#via}); a decision
     * that states no caller (a corpus recorded before rows stated it) is
     * taken as one of the way, an over-approximation.  A site the
     * table names no arm for (a switch, a fault call) is taken as left.
     * None that left: the path stopped on the way, so null (solr-adhoc-19
     * SG2b: create's u9 `!inFlightCreations.add`, taken toward the throw
     * before a loop bound cut the occurrence, was composed as the CONFLICT
     * throw).  A path that left at G and later kept the way at another
     * decision before a normal return left at G.
     */
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

    /** Why a loop bound cut the anchor's occurrence in {@code session}
     *  (its {@code BOUND_INSUFFICIENT} row, runtime.LoopAccounting#endAtCut),
     *  or "". */
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
                // A port's bound (HandoffMint): no occurrence's cut.
            }
        }
        return "";
    }

    /** The number of bodies a cut's loop bound stood at (its message,
     *  LoopAccounting's two cuts), or 0. */
    static int boundOf(String cut) {
        Matcher bound = CUT_BOUND.matcher(cut == null ? "" : cut);
        return bound.find() ? Integer.parseInt(bound.group(1) != null
                ? bound.group(1) : bound.group(2)) : 0;
    }

    private static final Pattern CUT_BOUND = Pattern.compile(
            "after (\\d+) loop body iterations|exceeds (\\d+)");

    /**
     * WHAT EXPLORE DEMANDS of one delivery {@code start} made in this
     * session, the last at {@code cutoff}, of the expressions {@code
     * delivered}: what COMPOSE keeps of the arm it is ({@link #named}),
     * asked under {@code claims} ({@code Corpus#readLeaves}).
     */
    public Set<String> ofDelivery(String session, OccurrenceAddress start,
                                  long cutoff, List<String> delivered,
                                  Corpus.Claims claims) {
        return named("delivery", session, start, cutoff, delivered,
                () -> seedWrites(session, delivered),
                Collections.<DecisionRow>emptyList(), claims);
    }

    /**
     * WHAT EXPLORE DEMANDS of one admitted path at the anchor: what COMPOSE
     * keeps of it ({@link #named}), its own decisions before where it
     * decided ({@link #decided}) among them, over its fatal arm.
     */
    public Set<String> ofPath(String session, TargetRow target,
                              List<DecisionRow> decisions,
                              Corpus.Claims claims) {
        Decided at = decided(session, target, decisions);
        // Unseeded, as COMPOSE's path closure (Composer#compose).
        return named("path", session, anchor, at.cutoff,
                Collections.singletonList(at.fatalTerm), () -> null,
                before(decisions, at.cutoff), claims);
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
     * cutoff, terms); one that read a claim is held by the claims until they
     * are taken ({@link #take}).
     */
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

    /** Takes, in the order, what one computation of {@code claims} claimed
     *  ({@code Corpus#take}), and holds the answers computed over the
     *  claims: false, taking none, where it is not the computation the
     *  order makes. */
    public boolean take(Corpus.Claims claims) {
        if (!corpus.take(claims)) return false;
        for (Map.Entry<String, Set<String>> answer : claims.held.entrySet()) {
            cache.putIfAbsent(answer.getKey(), answer.getValue());
        }
        return true;
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
        // a symbol is stated by the first row met.  A store version's read
        // states no value a symbol of a path may be (IDENTITY §7.2): it is
        // the closure's, which the path rests on ({@link #storeLocations}).
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

    /**
     * The store locations this path's guards read a version of through a
     * decode (IDENTITY §7.2): every STORE read a reached occurrence made
     * before its cutoff.  No formula term names a store version, so
     * constraint independence keeps none; the witness rests on each all the
     * same -- the guard decided on what that version's decode held -- and
     * CONFIRM holds each read to the version the session read (a STATE row:
     * a run whose reader read another version, a lagging watch, does not
     * confirm it).
     */
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
    Reached closure(String session, OccurrenceAddress start,
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

    /**
     * One write this path rests on (joined or an earlier version): its
     * writer is reached and its location's earlier versions queued.  An
     * INITIAL has neither: no occurrence wrote it.
     */
    private static void reach(WriteRow write, OccurrenceAddress anchor,
                              OccurrenceAddress start, Reached reached,
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
        if (!reached.extend(writer, write)) return;
        pending.add(writer);
    }

    /**
     * The occurrences a closure reaches, each with the cut its prefix runs
     * to: a VM event's seq, or -- a writer reached through a store write the
     * engine stated -- that write's place, seq and tie ({@link RowOrder}),
     * so a read the writer stated after its write at the same seq is past
     * the cut.  Read as occurrence id -> cut seq wherever only the seq
     * matters (a decision is a VM row).
     */
    public static final class Reached extends LinkedHashMap<String, Long> {
        private static final long serialVersionUID = 1L;
        private final Map<String, Integer> ties = new HashMap<String, Integer>();

        /** Moves {@code occurrence}'s cut out to {@code write}, if later:
         *  whether it moved. */
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

        /** Whether {@code read} stands before {@code occurrence}'s cut. */
        public boolean before(String occurrence, ReadRow read) {
            Long cut = get(occurrence);
            return cut != null && RowOrder.beforeCut(read.seq(), read.tie(),
                    cut, ties.getOrDefault(occurrence, 0));
        }
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
        return independence(session, seeds, bound, reached, conditions,
                null);
    }

    /** {@link #independence}, under {@code claims} ({@code
     *  Corpus#readLeaves}): null for a computation in the order. */
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

    /** The construction guards already found, by session and write: a
     *  function of the write, asked from any core ({@link #cache}). */
    private final Map<String, List<DecisionRow>> built =
            new ConcurrentHashMap<String, List<DecisionRow>>();

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
        // Not computeIfAbsent: a JDK 8 ConcurrentHashMap holds the bin
        // while the function runs.
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

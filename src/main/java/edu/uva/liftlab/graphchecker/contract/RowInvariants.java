package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.Arms;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * The row contract, checked as a GATE over one epoch's recorded sessions.
 *
 * <p>Every rule here is one sentence of CONTRACT-SPEC SS2 or HANDOVER SS1.3,
 * cited in the gap it produces.  They are checked at IMPORT and nowhere else,
 * because a defect in a row is not one stage's problem: 17960 lost two whole
 * campaigns to rows that EXPLORE and COMPOSE each read as valid -- a decision
 * whose {@code outcome} was the complement of its term's truth value, and a
 * focused session whose expression table was empty -- and both are one line
 * of this class.  A row nobody can state cannot be a claim about anything, so
 * the stage fails closed on the BLOCKING ones and records the rest.</p>
 *
 * <p>Pure functions over rows: this class opens no file, runs no solver and
 * consults no plan.  Where a rule cannot be decided from the rows alone it
 * says so as a DIAGNOSTIC rather than guessing -- an invariant that reports a
 * violation it cannot substantiate is worse than one that reports nothing.</p>
 */
public final class RowInvariants {
    /** {@code EXPR.} plus sixteen lower-case hex digits, and nothing else. */
    private static final Pattern REFERENCE =
            Pattern.compile("EXPR\\.[0-9a-fA-F]{16}");
    /** Any token that starts like a reference, well spelled or not. */
    private static final Pattern REFERENCE_LIKE =
            Pattern.compile("EXPR\\.[0-9a-zA-Z_.\\-]*");
    /** A minted symbol: {@code M_<sort>_<name>}, sort {@code L'..'} or one. */
    private static final Pattern MINTED =
            Pattern.compile("^M_(L'[^']*'|[A-Z])_(.*)$");
    /** A VM literal: {@code Y_<sort>_<value>}. */
    private static final Pattern LITERAL =
            Pattern.compile("^Y_([A-Z])_(-?[0-9]+)$");
    /** A plain decimal, as an INTEGRAL or CLOCK reading is spelled. */
    private static final Pattern DECIMAL = Pattern.compile("^-?[0-9]+$");
    /** The site spelling a placeholder read carries. */
    private static final String PLACEHOLDER = "#" + Endpoint.PLACEHOLDER
            + "#";

    private RowInvariants() {
    }

    /**
     * Every violation one epoch's sessions state, in rule order.
     *
     * @param sessions the epoch's sessions
     * @param asks     session id to the FOCUS ROW the wave drove that session
     *                 with -- {@code rootAssignments} and {@code clockDeltas}
     *                 -- which is what a FOCUSED session RAN under.  A SEED
     *                 needs none: it read its roots and its mints state them.
     */
    public static List<GapRow> check(List<SessionReader> sessions,
                                     Map<String, JsonObject> asks) {
        List<GapRow> gaps = new ArrayList<GapRow>();
        if (sessions == null || sessions.isEmpty()) return gaps;
        sessionSet(sessions, gaps);
        for (SessionReader session : sessions) {
            complete(session, gaps);
            check(session, asks == null ? null
                    : asks.get(session.sessionId()), gaps);
        }
        attributed(sessions, gaps);
        return gaps;
    }

    private static void check(SessionReader session, JsonObject ask,
                              List<GapRow> gaps) {
        activated(session, gaps);
        neverNeither(session, gaps);
        references(session, gaps);
        onePerEvent(session, gaps);
        sorts(session, gaps);
        // ONE VALUATION, read once: every rule that judges a term judges it
        // at the values this session RAN the roots at, and two rules that
        // resolved a symbol differently would be two answers to "what did
        // this replay run under".
        Map<String, String> executed = executed(session, ask, gaps);
        decisions(session, executed, gaps);
        versions(session, gaps);
        roots(session, gaps);
        targets(session, executed, gaps);
    }

    // ---- 1. the session set -------------------------------------------

    /**
     * Exactly one session STATES it is the seed, and the seed states no
     * obligation.
     *
     * <p>Read off {@code manifest.json}, never inferred.  The rule used to
     * be "the seed is the session whose ActivationRows are all {@code
     * focused=false}", and that has no answer for a focused replay whose
     * occurrence never activated: on the 11741 campaign #2 corpus nine of
     * eighty-one sessions focused nothing -- the seed, seven replays the kill
     * cut, and one legitimately NOT_ADMITTED focused replay -- so COMPOSE
     * refused and the anchor degraded to {@code Lost:UNKNOWN}.  With no SEED
     * no declaration has a recording it was written about; with two, nothing
     * says which; and a session that states SEED while naming the
     * obligations it ran contradicts itself, because a replay handed an
     * obligation is a counterfactual and not the recording.</p>
     */
    private static void sessionSet(List<SessionReader> sessions,
                                   List<GapRow> gaps) {
        List<String> stated = SessionReader.seedSessionIds(sessions);
        for (SessionReader session : sessions) {
            SessionManifest manifest = session.manifest();
            if (manifest == null || !manifest.seed()
                    || manifest.obligationIds().isEmpty()) {
                continue;
            }
            gaps.add(GapRow.of(session.sessionId(), GapKind.ADMISSION_GAP,
                    GapClass.BLOCKING, "epoch/sessions",
                    "invariant 1: this session states role SEED and names "
                            + "the obligations it ran "
                            + manifest.obligationIds()
                            + "; a replay handed an obligation is a "
                            + "counterfactual, not the recording"));
        }
        if (stated.size() == 1) return;
        gaps.add(GapRow.of(stated.isEmpty()
                        ? sessions.get(0).sessionId() : stated.get(0),
                GapKind.ADMISSION_GAP, GapClass.BLOCKING, "epoch/sessions",
                "invariant 1 (CONTRACT-SPEC SS2: every session states its "
                        + "role in manifest.json): " + stated.size() + " of "
                        + sessions.size() + " sessions state role SEED "
                        + stated + "; exactly one must"));
    }

    /**
     * Every session was read whole (CONTRACT-SPEC SS2: one file per kind,
     * and a manifest that states the role).
     *
     * <p>BLOCKING, and it has to be: a kind a reader could not parse comes
     * back as no rows, which is indistinguishable from a kind this run had
     * none of.  A replay the campaign's kill cut mid-row, or one with no
     * manifest, therefore states less than it ran and every later stage
     * reads the shortfall as fact.  Named with the file and the codec's own
     * reason, so the fix is a re-run of that worker and not a hunt.</p>
     */
    private static void complete(SessionReader session, List<GapRow> gaps) {
        if (session.incomplete().isEmpty()) return;
        gaps.add(GapRow.of(session.sessionId(), GapKind.SESSION_INCOMPLETE,
                GapClass.BLOCKING, session.sessionId(),
                "this session could not be read whole: "
                        + session.incomplete()));
    }

    /**
     * Every row's occurrence ran in its own session (CONTRACT-SPEC SS2: one
     * ActivationRow per activation).  A decision, a read, a write or a target
     * at an occurrence the session never activated is a row about an
     * execution that session does not state.
     */
    private static void activated(SessionReader session, List<GapRow> gaps) {
        Set<String> ran = new LinkedHashSet<String>();
        for (ActivationRow row : session.activations()) {
            ran.add(row.occurrence().id());
        }
        Set<String> said = new LinkedHashSet<String>();
        for (DecisionRow row : session.decisions()) {
            unactivated(session, gaps, ran, said, "decisions", row.seq(),
                    row.occurrence());
        }
        for (TargetRow row : session.targets()) {
            unactivated(session, gaps, ran, said, "targets", row.seq(),
                    row.occurrence());
        }
        for (ReadRow row : session.reads()) {
            unactivated(session, gaps, ran, said, "reads", row.seq(),
                    row.endpoint().occurrence());
        }
        for (WriteRow row : session.writes()) {
            unactivated(session, gaps, ran, said, "writes", row.seq(),
                    row.endpoint().occurrence());
        }
    }

    private static void unactivated(SessionReader session, List<GapRow> gaps,
                                    Set<String> ran, Set<String> said,
                                    String kind, long seq,
                                    OccurrenceAddress occurrence) {
        if (ran.contains(occurrence.id())) return;
        if (!said.add(kind + "|" + occurrence.id())) return;
        gaps.add(violation(session, GapKind.ADMISSION_GAP, GapClass.BLOCKING,
                kind, seq, "occurrence", occurrence.render(),
                "invariant 1 (CONTRACT-SPEC SS2: one ActivationRow per "
                        + "activation): this session published no activation "
                        + "for the occurrence this row is about"));
    }

    // ---- 2. never-neither ---------------------------------------------

    /**
     * HANDOVER SS1.3, verbatim: every ReadRow must have an observedVersion or
     * a plain decimal concreteValue, never neither.  A read with neither
     * states that something was read and refuses to say what, which is the
     * one thing a formula cannot work around.
     */
    private static void neverNeither(SessionReader session,
                                     List<GapRow> gaps) {
        for (ReadRow row : session.reads()) {
            if (row.observedVersion() >= 0) continue;
            String value = row.concreteValue();
            if (value != null && !value.trim().isEmpty()) continue;
            gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, "reads", row.seq(),
                    "observedVersion/concreteValue",
                    row.endpoint().site() + " " + row.location(),
                    "invariant 2 (HANDOVER SS1.3: every ReadRow must have an "
                            + "observedVersion or a plain decimal "
                            + "concreteValue, never both absent)"));
        }
        for (AttachRow row : session.attaches()) {
            String pairedBy = row.pairedBy();
            if (pairedBy == null || "HANDLE".equals(pairedBy)
                    || "CORRELATION_PORT".equals(pairedBy)) {
                continue;
            }
            gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, "attaches", row.seq(), "pairedBy",
                    row.endpoint().id() + "=" + pairedBy,
                    "invariant 2 (INTERACTION-ID SS1: an attach is paired by "
                            + "the handle or by correlation+port): this row "
                            + "names a third key, so which evidence paired "
                            + "it has no answer"));
        }
    }

    // ---- 3. expression references -------------------------------------

    /**
     * Every {@code EXPR.<16hex>} a row cites exists in that session's
     * expression table, and no other reference spelling appears (HANDOVER
     * SS1.3: one symbol spelling; the composer's single lowering resolves a
     * reference through the session's ExpressionTable).  A row that names an
     * expression its own session does not hold is unlowerable, and a focused
     * replay that published rows with an EMPTY table -- laneA3 -- is exactly
     * that, for every row it wrote.
     */
    private static void references(SessionReader session, List<GapRow> gaps) {
        ExpressionTable table = session.expressions();
        Set<String> said = new LinkedHashSet<String>();
        for (DecisionRow row : session.decisions()) {
            cited(session, gaps, table, said, "decisions", row.seq(), "term",
                    row.term());
        }
        for (TargetRow row : session.targets()) {
            cited(session, gaps, table, said, "targets", row.seq(),
                    "phiTerm", row.phiTerm());
        }
        for (WriteRow row : session.writes()) {
            cited(session, gaps, table, said, "writes", row.seq(),
                    "expressionRef", row.expressionRef());
        }
        for (ExportRow row : session.exports()) {
            cited(session, gaps, table, said, "exports", row.seq(),
                    "expressionRef", row.expressionRef());
        }
        for (AttachRow row : session.attaches()) {
            cited(session, gaps, table, said, "attaches", row.seq(),
                    "symbol", row.symbol());
            cited(session, gaps, table, said, "attaches", row.seq(),
                    "arrival", row.arrival());
        }
    }

    private static void cited(SessionReader session, List<GapRow> gaps,
                              ExpressionTable table, Set<String> said,
                              String kind, long seq, String field,
                              String text) {
        if (text == null || text.isEmpty()) return;
        Matcher like = REFERENCE_LIKE.matcher(text);
        while (like.find()) {
            String ref = like.group();
            if (!REFERENCE.matcher(ref).matches()) {
                say(session, gaps, said, GapKind.UNSTATED_VALUE,
                        GapClass.BLOCKING, kind, seq, field, ref,
                        "invariant 3 (HANDOVER SS1.3: one symbol spelling): "
                                + "an expression reference is EXPR. and "
                                + "sixteen hex digits; this is not");
                continue;
            }
            if (table.expression(ref) != null) continue;
            say(session, gaps, said, GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, kind, seq, field, ref,
                    "invariant 3 (HANDOVER SS1.3: a term's references are "
                            + "resolved through the SESSION's "
                            + "ExpressionTable): this session's "
                            + "expressions.json holds " + table.refs().size()
                            + " expression(s) and not this one");
        }
    }

    // ---- 4. one row per event -----------------------------------------

    /**
     * One row per event (CONTRACT-SPEC SS2).  Two rows of one kind at one
     * seq and one subject are one event stated twice, and two events under
     * one endpoint id are one event two rows will be merged into: the
     * skeleton keys slots by endpoint, so the second is invisible.
     *
     * <p>When two events collide under one endpoint id and that endpoint
     * carries no site index, the cause is the identity and not the rows --
     * IDENTITY-IMPL A: the site index is what distinguishes repeated events
     * of one site -- so it is a DIAGNOSTIC naming the missing index rather
     * than a refusal of the recording.</p>
     */
    private static void onePerEvent(SessionReader session,
                                    List<GapRow> gaps) {
        Set<String> seen = new LinkedHashSet<String>();
        for (ReadRow row : session.reads()) {
            twice(session, gaps, seen, "reads", row.seq(), "seq/location",
                    row.seq() + "|" + row.location(), row.location() + "");
        }
        for (WriteRow row : session.writes()) {
            twice(session, gaps, seen, "writes", row.seq(), "seq/location",
                    row.seq() + "|" + row.location(), row.location() + "");
        }
        for (DecisionRow row : session.decisions()) {
            twice(session, gaps, seen, "decisions", row.seq(),
                    "seq/siteId/ordinal", row.seq() + "|" + row.siteId()
                            + "|" + row.ordinal(),
                    row.siteId() + "#" + row.ordinal());
        }
        // A target row that did not reach its anchor states no event -- its
        // seq is 0, "no VM clock" -- only that one occurrence ran without
        // reaching it, so it is one per occurrence and anchor.
        for (TargetRow row : session.targets()) {
            twice(session, gaps, seen, "targets", row.seq(),
                    "seq/anchorSiteId", (row.reachedAnchor()
                            ? row.seq() + "" : row.occurrence().id())
                            + "|" + row.anchorSiteId(),
                    row.anchorSiteId());
        }
        endpoints(session, gaps, "reads", endpointSeqs(session, "reads"));
        endpoints(session, gaps, "writes", endpointSeqs(session, "writes"));
        endpoints(session, gaps, "attaches",
                endpointSeqs(session, "attaches"));
        endpoints(session, gaps, "exports", endpointSeqs(session, "exports"));
    }

    private static void twice(SessionReader session, List<GapRow> gaps,
                              Set<String> seen, String kind, long seq,
                              String field, String key, String subject) {
        if (seen.add(kind + "|" + key)) return;
        gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                GapClass.BLOCKING, kind, seq, field, subject,
                "invariant 4 (CONTRACT-SPEC SS2: one row per event): a "
                        + "second row of this kind states the same event"));
    }

    /** endpoint id -> the seqs and the endpoint, for one row kind. */
    private static Map<String, Object[]> endpointSeqs(SessionReader session,
                                                      String kind) {
        Map<String, Object[]> byEndpoint = new LinkedHashMap<String, Object[]>();
        List<Object[]> rows = new ArrayList<Object[]>();
        if ("reads".equals(kind)) {
            for (ReadRow row : session.reads()) {
                rows.add(new Object[] {row.endpoint(), row.seq()});
            }
        } else if ("writes".equals(kind)) {
            for (WriteRow row : session.writes()) {
                rows.add(new Object[] {row.endpoint(), row.seq()});
            }
        } else if ("attaches".equals(kind)) {
            for (AttachRow row : session.attaches()) {
                rows.add(new Object[] {row.endpoint(), row.seq()});
            }
        } else {
            for (ExportRow row : session.exports()) {
                rows.add(new Object[] {row.endpoint(), row.seq()});
            }
        }
        for (Object[] row : rows) {
            Endpoint endpoint = (Endpoint) row[0];
            Object[] held = byEndpoint.get(endpoint.id());
            if (held == null) {
                byEndpoint.put(endpoint.id(), new Object[] {endpoint,
                        new LinkedHashSet<Long>(Collections.singleton(
                                (Long) row[1]))});
                continue;
            }
            @SuppressWarnings("unchecked")
            Set<Long> seqs = (Set<Long>) held[1];
            seqs.add((Long) row[1]);
        }
        return byEndpoint;
    }

    private static void endpoints(SessionReader session, List<GapRow> gaps,
                                  String kind,
                                  Map<String, Object[]> byEndpoint) {
        for (Map.Entry<String, Object[]> entry : byEndpoint.entrySet()) {
            Endpoint endpoint = (Endpoint) entry.getValue()[0];
            @SuppressWarnings("unchecked")
            Set<Long> seqs = (Set<Long>) entry.getValue()[1];
            if (seqs.size() < 2) continue;
            // DIAGNOSTIC either way, and named either way.  An index that is
            // absent and an index whose frames are equal for two events of
            // one site are the same defect -- the identity cannot separate
            // them -- and it is the identity's to fix (IDENTITY-V3 SS1.2:
            // loop back edges count into the frames).  Refusing the
            // recording for it would fail every campaign at IMPORT over
            // something no row can state, and the cure is forbidden here: no
            // ordinal, no counter.
            int frames = endpoint.siteIndex().frames().size();
            gaps.add(violation(session, GapKind.LINEAGE_LOST,
                    GapClass.DIAGNOSTIC, kind, seqs.iterator().next(),
                    "endpoint.siteIndex", endpoint.site(),
                    "invariant 4 site index missing (IDENTITY-IMPL A: the "
                            + "site index distinguishes repeated events of "
                            + "one site): " + seqs.size() + " events of this "
                            + "site in one occurrence share one endpoint id, "
                            + "at seqs " + seqs + "; the index "
                            + (frames == 0 ? "is empty"
                                    : "has " + frames + " frame(s) and is "
                                    + "equal for all of them")));
        }
    }

    // ---- 5. symbol sorts ----------------------------------------------

    /**
     * One name, one spelled sort (HANDOVER SS1.3: one symbol spelling), and a
     * placeholder read's spelled sort is the sort its own row declares.  A
     * name that appears as {@code M_I_x} in one row and {@code M_Z_x} in
     * another is two sorts for one value, and the composer's declarations
     * would disagree about which.
     */
    private static void sorts(SessionReader session, List<GapRow> gaps) {
        Map<String, String[]> sortOfName = new LinkedHashMap<String, String[]>();
        for (RootMintRow row : session.roots()) {
            sort(session, gaps, sortOfName, "roots", row.seq(), row.symbol());
        }
        for (AttachRow row : session.attaches()) {
            sort(session, gaps, sortOfName, "attaches", row.seq(),
                    row.symbol());
        }
        for (ReadRow row : session.reads()) {
            sort(session, gaps, sortOfName, "reads", row.seq(), row.symbol());
            Matcher minted = MINTED.matcher(row.symbol() == null ? ""
                    : row.symbol());
            if (!minted.matches()) continue;
            String spelled = minted.group(1).substring(0, 1);
            String declared = row.javaType() == null || row.javaType().isEmpty()
                    ? "" : row.javaType().substring(0, 1);
            if (spelled.equals(declared)) continue;
            gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, "reads", row.seq(), "symbol/javaType",
                    row.symbol(),
                    "invariant 5 (HANDOVER SS1.3: one symbol spelling): the "
                            + "symbol is spelled sort " + spelled
                            + " and the row declares javaType "
                            + row.javaType()));
        }
    }

    private static void sort(SessionReader session, List<GapRow> gaps,
                             Map<String, String[]> sortOfName, String kind,
                             long seq, String symbol) {
        Matcher minted = MINTED.matcher(symbol == null ? "" : symbol);
        if (!minted.matches()) return;
        String spelled = minted.group(1);
        String name = minted.group(2);
        String[] held = sortOfName.get(name);
        if (held == null) {
            sortOfName.put(name, new String[] {spelled, kind + "#" + seq});
            return;
        }
        if (held[0].equals(spelled)) return;
        gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                GapClass.BLOCKING, kind, seq, "symbol", symbol,
                "invariant 5 (HANDOVER SS1.3: one symbol spelling): this name "
                        + "is spelled sort " + spelled + " here and sort "
                        + held[0] + " at " + held[1]));
    }

    // ---- 6. decisions: the recorded arm is the recorded arm ------------

    /**
     * P2f, and CONTRACT-SPEC SS2's own words: {@code outcome} says whether the
     * published term HELD, so the conjunct is {@code outcome ? term : (not
     * term)} and the runtime never pre-applies the polarity.  Where a term
     * rests on nothing but DECLARED roots and VM literals, the session states
     * its own truth value, and the row must agree with it.
     *
     * <p>That is the whole of the first laneA2 defect: a term {@code marker !=
     * false} with {@code outcome=false} beside a RootMintRow recording {@code
     * true}.  Every flip cut from it asked for the value the seed already
     * had.  A term whose leaves this cannot reach is not judged.</p>
     *
     * <p>AT THE VALUATION THE SESSION RAN UNDER, which is {@link #executed}'s
     * one notion and NOT {@code recordedValue} on its own: a mint states
     * what it OBSERVED, and in a focused replay what it observed is the
     * recording's value, read before the wave's assignment is planted.  On
     * the 39bedd768 HDFS-17960 wave 0 the focused session
     * {@code cb67875d1d896d4d-73ab772f} ran {@code
     * HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED=false} (its obligation's {@code
     * rootAssignments}, and its {@code obligation_query.smt2} asserts it),
     * minted {@code recordedValue="true"}, and this rule refused three of its
     * decisions -- 79, 140 and 145 -- for stating the arm they actually took.
     * All three verify at {@code false}.</p>
     */
    private static void decisions(SessionReader session,
                                  Map<String, String> executed,
                                  List<GapRow> gaps) {
        if (executed == null || executed.isEmpty()) return;
        for (DecisionRow row : session.decisions()) {
            if (row.term() == null || row.term().trim().isEmpty()) continue;
            Boolean held = truth(session, row.term(), executed);
            if (held == null || held.booleanValue() == row.outcome()) continue;
            gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, "decisions", row.seq(), "outcome",
                    row.siteId() + "#" + row.ordinal(),
                    "invariant 6 (CONTRACT-SPEC SS2: outcome says whether the "
                            + "published term HELD; the conjunct is "
                            + "outcome ? term : (not term)): at the root "
                            + "values this session RAN under the term is "
                            + held + " and the row says " + row.outcome()));
        }
    }

    /**
     * rootId-free: what this session RAN each declared root at, by SYMBOL --
     * or null when it states no such valuation at all.
     *
     * <p>ONE NOTION, and it is a fact about an EXECUTION, not about a row.
     * A SEED read its roots, so its mints state them.  A FOCUSED replay was
     * HANDED them: the wave plants the value at the mint, and the mint
     * states what it OBSERVED there -- the recording's own value, read
     * before the plant, because after the plant the two quantities are no
     * longer distinguishable off the heap (RootMint#focusedRootValue).  So
     * for a FOCUSED session the valuation it ran is the ASK, its focus row's
     * {@code rootAssignments} and {@code clockDeltas}, per kind:</p>
     *
     * <ul>
     *   <li>MARKER and INTEGRAL: the assignment is the value, absolute.</li>
     *   <li>CLOCK: the wave states a SKEW, never an instant -- every
     *       execution reads a clock fresh -- so the value is the mint's own
     *       reading plus the delta, exactly as the mint computed it.</li>
     *   <li>any root the wave assigned nothing: the mint READ it, so its
     *       {@code recordedValue} is what ran.</li>
     * </ul>
     *
     * <p>A FOCUSED session whose ask no obligation worker of this epoch
     * states is REFUSED by name here.  Reading its mints instead would judge
     * a counterfactual at the recording's valuation, which is the defect
     * this method exists to remove, and the gate would report it as a row
     * violation of a session whose rows are fine.</p>
     */
    private static Map<String, String> executed(SessionReader session,
                                                JsonObject ask,
                                                List<GapRow> gaps) {
        SessionManifest manifest = session.manifest();
        boolean focused = manifest != null && !manifest.seed();
        if (focused && ask == null) {
            gaps.add(GapRow.of(session.sessionId(), GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, "epoch/valuation",
                    "invariant 6 (CONTRACT-SPEC SS3: a focused replay runs "
                            + "at the root values its obligation assigns): "
                            + "this session states role FOCUSED "
                            + manifest.obligationIds() + " and no obligation "
                            + "worker of this epoch states the focus row it "
                            + "ran, so the valuation it executed at is "
                            + "unstated and no term of it can be judged"));
            return null;
        }
        Map<String, String> assigned = focused
                ? strings(ask, "rootAssignments") : null;
        Map<String, String> skews = focused
                ? strings(ask, "clockDeltas") : null;
        Map<String, String> bySymbol = new LinkedHashMap<String, String>();
        for (RootMintRow row : session.roots()) {
            if (!row.declared()) continue;
            bySymbol.put(row.symbol(), ran(row, assigned, skews));
        }
        return bySymbol;
    }

    /**
     * What one mint's root RAN at: the wave's ask where it states one, and
     * the mint's own reading where it does not.
     *
     * <p>{@code ""} where the ask cannot be stated as a value -- an unstated
     * reading under a skew -- because {@code ""} is the spelling every leaf
     * this class cannot reach already has, and a rule that guessed one here
     * would report violations it cannot substantiate.</p>
     */
    private static String ran(RootMintRow row, Map<String, String> assigned,
                              Map<String, String> skews) {
        String recorded = row.recordedValue() == null ? ""
                : row.recordedValue().trim();
        if (assigned == null) return recorded;
        if (row.kind() == RootKind.CLOCK) {
            String delta = skews == null ? null : skews.get(row.rootId());
            if (delta == null || delta.trim().isEmpty()) return recorded;
            Object read = literal(recorded);
            Object skew = literal(delta.trim());
            if (!(read instanceof Long) || !(skew instanceof Long)) return "";
            return Long.toString(((Long) read).longValue()
                    + ((Long) skew).longValue());
        }
        String planted = assigned.get(row.rootId());
        if (planted == null || planted.trim().isEmpty()) return recorded;
        return planted.trim();
    }

    /**
     * The truth value a term has at the valuation the session ran under, or
     * null.
     *
     * <p>Null is the answer whenever the term reaches a leaf this cannot
     * state -- a read, a container, a cast, a shift over an unstated value.
     * The invariant is conditional on purpose: a checker that guesses at a
     * leaf reports violations it cannot substantiate.</p>
     */
    private static Boolean truth(SessionReader session, String term,
                                 Map<String, String> declared) {
        String text = term.trim();
        boolean negated = false;
        while (text.startsWith("(not ") && text.endsWith(")")) {
            negated = !negated;
            text = text.substring(5, text.length() - 1).trim();
        }
        if (!REFERENCE.matcher(text).matches()) return null;
        Object value = value(session.expressions(),
                session.expressions().expression(text), declared, 0);
        if (!(value instanceof Boolean)) return null;
        boolean held = ((Boolean) value).booleanValue();
        return Boolean.valueOf(negated != held);
    }

    /** One VM expression at the recorded valuation: Boolean, Long or null. */
    private static Object value(ExpressionTable table, JsonObject node,
                                Map<String, String> declared, int depth) {
        if (node == null || depth > 64) return null;
        String type = text(node, "_type");
        if ("SymbolExpression".equals(type)) {
            String recorded = declared.get(text(node, "_exp"));
            return recorded == null ? null : literal(recorded);
        }
        if ("ConstExpr".equals(type)) {
            Matcher value = LITERAL.matcher(text(node, "_exp"));
            if (!value.matches()) return null;
            return "Z".equals(value.group(1))
                    ? (Object) Boolean.valueOf(!"0".equals(value.group(2)))
                    : (Object) Long.valueOf(value.group(2));
        }
        if ("ConsumerBoundaryExpression".equals(type)) {
            return value(table, object(node, "expression"), declared,
                    depth + 1);
        }
        if ("ReadFromExpression".equals(type)) {
            // What the read returned is what the write it observed stated.
            JsonObject observed = object(node, "observedVersion");
            return observed == null ? null
                    : value(table, object(observed, "expression"), declared,
                            depth + 1);
        }
        if (!"BinaryExpression".equals(type)) return null;
        Object left = value(table, object(node, "_left"), declared, depth + 1);
        Object right = value(table, object(node, "_right"), declared,
                depth + 1);
        if (left == null || right == null) return null;
        return apply(text(node, "_op"), left, right);
    }

    private static Object apply(String op, Object left, Object right) {
        if ("==".equals(op)) return Boolean.valueOf(same(left, right));
        if ("!=".equals(op)) return Boolean.valueOf(!same(left, right));
        if (!(left instanceof Long) || !(right instanceof Long)) return null;
        long a = ((Long) left).longValue();
        long b = ((Long) right).longValue();
        if ("<".equals(op)) return Boolean.valueOf(a < b);
        if ("<=".equals(op)) return Boolean.valueOf(a <= b);
        if (">".equals(op)) return Boolean.valueOf(a > b);
        if (">=".equals(op)) return Boolean.valueOf(a >= b);
        if ("+".equals(op)) return Long.valueOf(a + b);
        if ("-".equals(op)) return Long.valueOf(a - b);
        if ("*".equals(op)) return Long.valueOf(a * b);
        if ("&".equals(op)) return Long.valueOf(a & b);
        if ("|".equals(op)) return Long.valueOf(a | b);
        if ("^".equals(op)) return Long.valueOf(a ^ b);
        return null;
    }

    private static boolean same(Object left, Object right) {
        long a = left instanceof Boolean
                ? (((Boolean) left).booleanValue() ? 1L : 0L)
                : ((Long) left).longValue();
        long b = right instanceof Boolean
                ? (((Boolean) right).booleanValue() ? 1L : 0L)
                : ((Long) right).longValue();
        return a == b;
    }

    /** A recorded reading, as the row spells one. */
    private static Object literal(String recorded) {
        String value = recorded == null ? "" : recorded.trim();
        if ("true".equals(value)) return Boolean.TRUE;
        if ("false".equals(value)) return Boolean.FALSE;
        if (!DECIMAL.matcher(value).matches()) return null;
        try {
            return Long.valueOf(value);
        } catch (NumberFormatException notALong) {
            return null;
        }
    }

    // ---- 7. versions ---------------------------------------------------

    /**
     * A version a read observed is a version some row of that session STATES
     * (HANDOVER SS1.4: a read joins the expression of the write version it
     * observed).  Until contract v2.4's placeholder {@code mintVersion} lands
     * (runtime P2l), a placeholder read can state a version no WriteRow
     * carries, so a missing write is a DIAGNOSTIC naming the version -- not a
     * refusal of a recording the contract has not caught up with.
     *
     * <p>A WriteRow that states the very version a placeholder read MINTED
     * is the opposite failure and is BLOCKING: that version is the mint's own
     * store, nobody wrote it, and publishing it as a write states one event
     * twice -- the placeholder would join a write that exists only to be
     * joined.  Keyed by the store, {@code location@mintVersion}, and never by
     * the symbol: a field later assigned the minted value
     * ({@code x.f = <mint symbol>}) is a real write of its own version whose
     * whole expression is that same symbol.</p>
     */
    private static void versions(SessionReader session, List<GapRow> gaps) {
        Set<String> stated = new LinkedHashSet<String>();
        for (WriteRow row : session.writes()) {
            stated.add(row.location() + "@" + row.version());
        }
        // Contract v2.4: a placeholder read STATES a version of its own,
        // which is NOT the version it observed -- seq 243 of laneA5 observed
        // 77 and minted 177 -- so the two are added to the same set of
        // stated versions and never compared with each other.  Keying the
        // mint by the observed version is what made the gate refuse a row
        // whose field was right there in it.
        Set<String> minted = new LinkedHashSet<String>();
        for (ReadRow row : session.reads()) {
            if (row.mintVersion() >= 0) {
                String store = row.location() + "@" + row.mintVersion();
                stated.add(store);
                if (row.endpoint().site().contains(PLACEHOLDER)) {
                    minted.add(store);
                }
            }
        }
        Set<String> said = new LinkedHashSet<String>();
        for (ReadRow row : session.reads()) {
            if (row.observedVersion() < 0) continue;
            String key = row.location() + "@" + row.observedVersion();
            if (stated.contains(key)) continue;
            say(session, gaps, said, GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, "reads", row.seq(),
                    "observedVersion",
                    key, "invariant 7 (HANDOVER SS1.4: a read joins the "
                            + "expression of the write version it observed; "
                            + "contract v2.4: or the placeholder mint that "
                            + "states it): no WriteRow of this session states "
                            + "this version and no placeholder read mints it");
        }
        // Every placeholder row states the version it mints.
        for (ReadRow row : session.reads()) {
            if (!row.endpoint().site().contains(PLACEHOLDER)) continue;
            if (row.mintVersion() >= 0) continue;
            gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, "reads", row.seq(), "mintVersion",
                    row.location() + "", "invariant 7 (contract v2.4: a "
                            + "placeholder ReadRow states the version it "
                            + "mints): this placeholder row states none"));
        }
        for (WriteRow row : session.writes()) {
            String store = row.location() + "@" + row.version();
            if (!minted.contains(store)) continue;
            gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, "writes", row.seq(), "version",
                    store,
                    "invariant 7 (fabricated write): this write states the "
                            + "version a placeholder read of this session "
                            + "minted -- the mint's own store, which nobody "
                            + "wrote -- so the pair would join to nothing"));
        }
    }

    // ---- 8. roots ------------------------------------------------------

    /**
     * HANDOVER SS1.3: a RootMintRow is published only for a DECLARED root,
     * and its recorded value is spelled the way its kind is read back -- a
     * MARKER as a boolean, an INTEGRAL or CLOCK as a plain decimal.  One row
     * per (occurrence, rootId): a root minted twice in one activation is two
     * values for one source in one execution.
     */
    private static void roots(SessionReader session, List<GapRow> gaps) {
        Set<String> minted = new LinkedHashSet<String>();
        for (RootMintRow row : session.roots()) {
            if (!row.declared()) {
                gaps.add(violation(session, GapKind.DECLARATION_MISSING,
                        GapClass.BLOCKING, "roots", row.seq(), "declared",
                        row.rootId(),
                        "invariant 8 (HANDOVER SS1.3: a RootMintRow is "
                                + "published only for a DECLARED root)"));
            }
            String value = row.recordedValue() == null ? ""
                    : row.recordedValue().trim();
            boolean ok = row.kind() == RootKind.MARKER
                    ? "true".equals(value) || "false".equals(value)
                    : DECIMAL.matcher(value).matches();
            if (!ok) {
                gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                        GapClass.BLOCKING, "roots", row.seq(),
                        "recordedValue", row.rootId() + "=" + value,
                        "invariant 8 (HANDOVER SS1.3): a " + row.kind()
                                + " reading is spelled "
                                + (row.kind() == RootKind.MARKER
                                        ? "true or false"
                                        : "as a plain decimal")));
            }
            if (minted.add(row.occurrence().id() + "|" + row.rootId())) {
                continue;
            }
            gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, "roots", row.seq(),
                    "occurrence/rootId", row.rootId(),
                    "invariant 8 (HANDOVER SS1.3): this occurrence already "
                            + "minted this root, so the session states two "
                            + "values for one source in one activation"));
        }
    }

    // ---- 9. targets ----------------------------------------------------

    /**
     * CONTRACT-SPEC SS2: {@code phiTerm} is published in the FATAL polarity.
     * An anchor that was reached and published no predicate took a concrete
     * branch, which is legitimate and stated as a DIAGNOSTIC -- except where
     * the run OBSERVED the fatal arm, because then there is a predicate and
     * the row dropped it.  And where the recording's own roots decide it, an
     * observed fatal must be a phi that HOLDS at those values: a fatal
     * polarity that is false in the run that took it is the polarity stated
     * backwards.
     */
    private static void targets(SessionReader session,
                                Map<String, String> executed,
                                List<GapRow> gaps) {
        Map<String, String> declared = executed == null
                ? Collections.<String, String>emptyMap() : executed;
        for (TargetRow row : session.targets()) {
            boolean empty = row.phiTerm() == null
                    || row.phiTerm().trim().isEmpty();
            if (empty && row.reachedAnchor()) {
                gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                        row.observedFatal() ? GapClass.BLOCKING
                                : GapClass.DIAGNOSTIC, "targets", row.seq(),
                        "phiTerm", row.anchorSiteId(),
                        "invariant 9 (CONTRACT-SPEC SS2: phiTerm is published "
                                + "in the FATAL polarity): the anchor was "
                                + "reached and states no predicate"
                                + (row.observedFatal()
                                        ? ", and the run OBSERVED the fatal "
                                        + "arm, so there was one"
                                        : "; a concrete branch is "
                                        + "legitimate")));
                continue;
            }
            if (empty || !row.observedFatal() || declared.isEmpty()) continue;
            Boolean held = truth(session, row.phiTerm(), declared);
            if (held == null || held.booleanValue()) continue;
            gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, "targets", row.seq(), "phiTerm",
                    row.anchorSiteId(),
                    "invariant 9 (CONTRACT-SPEC SS2: phiTerm is published in "
                            + "the FATAL polarity): the run observed the "
                            + "fatal arm and this term is FALSE at the root "
                            + "values this session RAN under"));
        }
    }

    // ---- 10. a focused session ran the flip it was given ---------------

    /**
     * A focused replay's own session states the arm the obligation asked for
     * (HANDOVER SS1.5: the verdict is ADMITTED when the prefix reproduced and
     * the flip took the other arm).  DIAGNOSTIC: the obligation's result row
     * already carries NOT_ADMITTED when it did not, so this names the row
     * rather than deciding anything.
     *
     * @param flip     the focus row the worker wrote, as JSON
     * @param session  the session that replay published
     */
    public static List<GapRow> flipped(JsonObject flip,
                                       SessionReader session) {
        List<GapRow> gaps = new ArrayList<GapRow>();
        if (flip == null || session == null) return gaps;
        JsonObject named = object(flip, "flip");
        if (named == null) return gaps;
        String site = text(named, "siteId");
        if (site.isEmpty()) return gaps;
        int ordinal = named.has("ordinal")
                ? named.get("ordinal").getAsInt() : 1;
        boolean outcome = named.has("outcome")
                && named.get("outcome").getAsBoolean();
        for (DecisionRow row : session.decisions()) {
            if (!site.equals(row.siteId()) || row.ordinal() != ordinal) {
                continue;
            }
            if (row.outcome() == outcome) return gaps;
        }
        gaps.add(violation(session, GapKind.ADMISSION_GAP,
                GapClass.DIAGNOSTIC, "decisions", 0L, "outcome",
                site + "#" + ordinal,
                "invariant 10 (HANDOVER SS1.5: a focused replay is ADMITTED "
                        + "when the flip took the other arm): this session "
                        + "states no decision at that site and ordinal with "
                        + "outcome " + outcome + "; the obligation's own "
                        + "result row carries the verdict"));
        return gaps;
    }

    // ---- 11. a root symbol without its RootMintRow ---------------------

    /**
     * R4: every root symbol a session REFERENCES is a root that session
     * itself MINTED a row for.
     *
     * <p>SET-level, the way invariant 1 is: which quantities are roots is a
     * fact about the EPOCH -- a root is declared by the case and minted
     * wherever the run reaches its site -- so the names are taken from every
     * session's {@code RootMintRow}s together, and a root's symbol is the
     * same name in every session that minted it.  What is then asked of each
     * session on its own is whether it states the row for the roots it
     * NAMES.</p>
     *
     * <p>BLOCKING, because a symbol with no row is not a gap in a report: it
     * is a quantity the session carries and nothing of the session
     * attributes.  The composer meets it as an arm it cannot guard and the
     * claim meets it as a root free at every valuation, which is exactly how
     * hdfs-11741 campaign #4 came out satisfiable at the recorded valuation
     * and yielded no witness -- seven of thirteen sessions referenced a
     * declared root they published no row for, {@code
     * HDFS.BLOCK_KEY.SERIAL_NO} among them, carried out of an activation the
     * run abandoned.  The runtime's half of the same rule is {@code
     * RootMint#mintUnattributed}: a mint no admitted activation owns mints
     * no symbol, and one that does is rowed.</p>
     *
     * <p>Referenced means named by the session's own tables: every {@code
     * SymbolExpression} leaf of {@code expressions.json} -- the one walk
     * {@link Arms#symbolsIn} makes, so COMPOSE and IMPORT decide "which
     * roots does this expression name" the same way -- plus the terms the
     * decision and target rows publish, which is where the citation comes
     * from.</p>
     */
    private static void attributed(List<SessionReader> sessions,
                                   List<GapRow> gaps) {
        Map<String, String> roots = new LinkedHashMap<String, String>();
        for (SessionReader session : sessions) {
            for (RootMintRow row : session.roots()) {
                String rootId = row.rootId() == null ? "" : row.rootId();
                String symbol = row.symbol() == null ? "" : row.symbol();
                if (rootId.isEmpty() || symbol.isEmpty()) continue;
                if (!roots.containsKey(rootId)) roots.put(rootId, symbol);
            }
        }
        if (roots.isEmpty()) return;
        for (SessionReader session : sessions) {
            Map<String, String> named = named(session);
            Set<String> stated = new LinkedHashSet<String>();
            for (RootMintRow row : session.roots()) {
                stated.add(row.rootId() == null ? "" : row.rootId());
            }
            for (Map.Entry<String, String> root : roots.entrySet()) {
                if (stated.contains(root.getKey())) continue;
                String where = named.get(root.getValue());
                if (where == null) continue;
                gaps.add(GapRow.of(session.sessionId(),
                        GapKind.MINT_UNATTRIBUTED, GapClass.BLOCKING,
                        root.getKey(),
                        "invariant 11 (R4: a root symbol without its "
                                + "RootMintRow): session "
                                + session.sessionId() + " references symbol "
                                + root.getValue() + " at " + where
                                + " and states no RootMintRow for root "
                                + root.getKey() + ", so it carries a "
                                + "quantity no row of it attributes"));
            }
        }
    }

    /**
     * Every symbol one session names, each with ONE place it was referenced.
     *
     * <p>The published terms are read first so the citation is a ROW a
     * reader can open, and the expression table fills in the rest.</p>
     */
    private static Map<String, String> named(SessionReader session) {
        Map<String, String> where = new LinkedHashMap<String, String>();
        for (DecisionRow row : session.decisions()) {
            cite(session, row.term(), where, "decisions.jsonl seq=" + row.seq()
                    + " field=term " + row.siteId() + "#" + row.ordinal());
        }
        for (TargetRow row : session.targets()) {
            cite(session, row.phiTerm(), where, "targets.jsonl seq="
                    + row.seq() + " field=phiTerm " + row.anchorSiteId());
        }
        for (Map.Entry<String, JsonObject> entry
                : session.expressions().expressions().entrySet()) {
            Set<String> symbols = new LinkedHashSet<String>();
            Arms.symbolsIn(entry.getValue(), symbols, 0);
            for (String symbol : symbols) {
                if (!where.containsKey(symbol)) {
                    where.put(symbol,
                            "expressions.json ref=" + entry.getKey());
                }
            }
        }
        return where;
    }

    /** The symbols one published term names, cited at the row that holds it. */
    private static void cite(SessionReader session, String term,
                             Map<String, String> where, String place) {
        String text = term == null ? "" : term.trim();
        while (text.startsWith("(not ") && text.endsWith(")")) {
            text = text.substring(5, text.length() - 1).trim();
        }
        if (text.isEmpty()) return;
        Set<String> symbols = new LinkedHashSet<String>();
        if (MINTED.matcher(text).matches()) {
            symbols.add(text);
        } else {
            Arms.symbolsIn(session.expressions().expression(text), symbols, 0);
        }
        for (String symbol : symbols) {
            if (!where.containsKey(symbol)) where.put(symbol, place);
        }
    }

    // ---- shared -------------------------------------------------------

    private static void say(SessionReader session, List<GapRow> gaps,
                            Set<String> said, GapKind kind, GapClass cls,
                            String rowKind, long seq, String field,
                            String subject, String detail) {
        if (!said.add(rowKind + "|" + field + "|" + subject)) return;
        gaps.add(violation(session, kind, cls, rowKind, seq, field, subject,
                detail));
    }

    /** Every violation names session, row kind, seq and field. */
    private static GapRow violation(SessionReader session, GapKind kind,
                                    GapClass cls, String rowKind, long seq,
                                    String field, String subject,
                                    String detail) {
        return GapRow.of(session.sessionId(), kind, cls,
                rowKind + ".jsonl seq=" + seq + " field=" + field + " "
                        + subject, detail);
    }

    private static String text(JsonObject node, String member) {
        if (node == null || !node.has(member)) return "";
        JsonElement value = node.get(member);
        return value.isJsonPrimitive() ? value.getAsString() : "";
    }

    private static JsonObject object(JsonObject node, String member) {
        if (node == null || !node.has(member)) return null;
        JsonElement value = node.get(member);
        return value.isJsonObject() ? value.getAsJsonObject() : null;
    }

    /** One string-to-string member of a row, or an empty map. */
    private static Map<String, String> strings(JsonObject node,
                                               String member) {
        Map<String, String> read = new LinkedHashMap<String, String>();
        JsonObject stated = object(node, member);
        if (stated == null) return read;
        for (Map.Entry<String, JsonElement> entry : stated.entrySet()) {
            if (!entry.getValue().isJsonPrimitive()) continue;
            read.put(entry.getKey(), entry.getValue().getAsString());
        }
        return read;
    }
}

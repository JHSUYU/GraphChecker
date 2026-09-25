package edu.uva.liftlab.graphchecker.contract;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.primitiveString;

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
import java.util.function.Function;
import java.util.function.ToLongFunction;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * The row contract, checked at IMPORT as a gate over one epoch's sessions.
 * Each rule is one sentence of CONTRACT-SPEC SS2 or HANDOVER SS1.3, cited in
 * its gap; BLOCKING gaps fail the stage closed.  Pure functions over rows: a
 * rule the rows cannot decide reports a DIAGNOSTIC rather than guess.
 */
public final class RowInvariants {
    /** {@code EXPR.} plus sixteen hex digits, and nothing else. */
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
    public static final String PLACEHOLDER = "#PLACEHOLDER#";

    private RowInvariants() {
    }

    /**
     * Every violation, in rule order.  {@code asks} maps session id to the
     * focus row ({@code rootAssignments}, {@code clockDeltas}) a FOCUSED
     * session ran under.
     */
    public static List<GapRow> check(List<SessionReader> sessions,
                                     Map<String, JsonObject> asks) {
        List<GapRow> gaps = new ArrayList<GapRow>();
        if (sessions.isEmpty()) return gaps;
        sessionSet(sessions, gaps);
        for (SessionReader session : sessions) {
            complete(session, gaps);
            check(session, asks.get(session.sessionId()), gaps);
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
        // One valuation, read once, for every rule that judges a term.
        Map<String, String> executed = executed(session, ask, gaps);
        decisions(session, executed, gaps);
        versions(session, gaps);
        roots(session, gaps);
        targets(session, executed, gaps);
    }

    // ---- 1. the session set -------------------------------------------

    /**
     * Exactly one session states it is the seed, and the seed names no
     * obligation.  Read off {@code manifest.json}, never inferred from
     * activations: a focused replay that never activated looks like a seed.
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
     * Every session was read whole (CONTRACT-SPEC SS2).  BLOCKING: an
     * unparseable kind reads back as no rows, which later stages take as fact.
     */
    private static void complete(SessionReader session, List<GapRow> gaps) {
        if (session.incomplete().isEmpty()) return;
        gaps.add(GapRow.of(session.sessionId(), GapKind.SESSION_INCOMPLETE,
                GapClass.BLOCKING, session.sessionId(),
                "this session could not be read whole: "
                        + session.incomplete()));
    }

    /** Every row's occurrence ran in its session (CONTRACT-SPEC SS2). */
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
     * a plain decimal concreteValue, never neither.  An attach is paired by
     * HANDLE or CORRELATION_PORT and nothing else.
     */
    private static void neverNeither(SessionReader session,
                                     List<GapRow> gaps) {
        for (ReadRow row : session.reads()) {
            if (row.observedVersion() >= 0) continue;
            if (row.concreteValue() != null) continue;
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
     * SS1.3).  A reference the session does not hold is unlowerable.
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
     * One row per event (CONTRACT-SPEC SS2): two rows of one kind at one seq
     * and subject are one event stated twice (BLOCKING).  Two events under
     * one endpoint id merge in the skeleton, which keys slots by endpoint;
     * that is an identity defect (IDENTITY-IMPL A), so only a DIAGNOSTIC.
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
        // An unreached target has seq 0 (no VM clock): one per occurrence.
        for (TargetRow row : session.targets()) {
            twice(session, gaps, seen, "targets", row.seq(),
                    "seq/anchorSiteId", (row.reachedAnchor()
                            ? row.seq() + "" : row.occurrence().id())
                            + "|" + row.anchorSiteId(),
                    row.anchorSiteId());
        }
        endpoints(session, gaps, "reads", session.reads(), ReadRow::endpoint,
                ReadRow::seq);
        endpoints(session, gaps, "writes", session.writes(),
                WriteRow::endpoint, WriteRow::seq);
        endpoints(session, gaps, "attaches", session.attaches(),
                AttachRow::endpoint, AttachRow::seq);
        endpoints(session, gaps, "exports", session.exports(),
                ExportRow::endpoint, ExportRow::seq);
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

    /** Events of one row kind that share one endpoint id (DIAGNOSTIC). */
    private static <T> void endpoints(SessionReader session,
                                      List<GapRow> gaps, String kind,
                                      List<T> rows,
                                      Function<T, Endpoint> endpointOf,
                                      ToLongFunction<T> seqOf) {
        Map<String, Endpoint> endpoints = new LinkedHashMap<String, Endpoint>();
        Map<String, Set<Long>> seqsOf = new LinkedHashMap<String, Set<Long>>();
        for (T row : rows) {
            Endpoint endpoint = endpointOf.apply(row);
            endpoints.putIfAbsent(endpoint.id(), endpoint);
            seqsOf.computeIfAbsent(endpoint.id(), id -> new LinkedHashSet<Long>())
                    .add(seqOf.applyAsLong(row));
        }
        for (Map.Entry<String, Set<Long>> entry : seqsOf.entrySet()) {
            Endpoint endpoint = endpoints.get(entry.getKey());
            Set<Long> seqs = entry.getValue();
            if (seqs.size() < 2) continue;
            // Absent index or equal frames: the identity's defect to fix
            // (IDENTITY-V3 SS1.2), never cured here by an ordinal or counter.
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

    /** One name, one spelled sort, = a read's javaType (HANDOVER SS1.3). */
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
            Matcher minted = MINTED.matcher(row.symbol());
            if (!minted.matches()) continue;
            String spelled = minted.group(1).substring(0, 1);
            String declared = row.javaType().substring(0, 1);
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
        Matcher minted = MINTED.matcher(symbol);
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
     * CONTRACT-SPEC SS2: {@code outcome} says whether the published term
     * HELD; the runtime never pre-applies the polarity.  A term resting only
     * on declared roots and literals must agree with its row, judged at the
     * valuation the session RAN under ({@link #executed}), not at
     * {@code recordedValue}.
     */
    private static void decisions(SessionReader session,
                                  Map<String, String> executed,
                                  List<GapRow> gaps) {
        if (executed == null || executed.isEmpty()) return;
        for (DecisionRow row : session.decisions()) {
            if (row.term().trim().isEmpty()) continue;
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
     * What this session RAN each declared root at, by symbol, or null when
     * unstated.  A FOCUSED replay's mints record the recording's value
     * (RootMint#focusedRootValue), so its valuation is the ask: assignments
     * are absolute, a CLOCK is reading plus delta, an unassigned root is its
     * {@code recordedValue}.  A FOCUSED session with no ask is BLOCKING.
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

    /** One mint's executed value; {@code ""} (unjudgeable) if unstatable. */
    private static String ran(RootMintRow row, Map<String, String> assigned,
                              Map<String, String> skews) {
        String recorded = row.recordedValue().trim();
        if (assigned == null) return recorded;
        if (row.kind() == RootKind.CLOCK) {
            String delta = skews.get(row.rootId());
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

    /** Truth of a term at the valuation; null at an unevaluable leaf. */
    private static Boolean truth(SessionReader session, String term,
                                 Map<String, String> declared) {
        String text = term.trim();
        boolean negated = false;
        while (negation(text)) {
            negated = !negated;
            text = operand(text);
        }
        if (!REFERENCE.matcher(text).matches()) return null;
        Object value = value(session.expressions().expression(text),
                declared, 0);
        if (!(value instanceof Boolean)) return null;
        boolean held = ((Boolean) value).booleanValue();
        return Boolean.valueOf(negated != held);
    }

    /** Whether a published term is {@code (not <operand>)}. */
    private static boolean negation(String text) {
        return text.startsWith("(not ") && text.endsWith(")");
    }

    private static String operand(String negation) {
        return negation.substring(5, negation.length() - 1).trim();
    }

    /** One VM expression at the recorded valuation: Boolean, Long or null. */
    private static Object value(JsonObject node, Map<String, String> declared,
                                int depth) {
        if (node == null || depth > 64) return null;
        String type = primitiveString(node, "_type");
        if ("SymbolExpression".equals(type)) {
            String recorded = declared.get(primitiveString(node, "_exp"));
            return recorded == null ? null : literal(recorded);
        }
        if ("ConstExpr".equals(type)) {
            Matcher value = LITERAL.matcher(primitiveString(node, "_exp"));
            if (!value.matches()) return null;
            return "Z".equals(value.group(1))
                    ? (Object) Boolean.valueOf(!"0".equals(value.group(2)))
                    : (Object) Long.valueOf(value.group(2));
        }
        if ("ConsumerBoundaryExpression".equals(type)) {
            return value(object(node, "expression"), declared, depth + 1);
        }
        if ("ReadFromExpression".equals(type)) {
            // What the read returned is what the write it observed stated.
            return value(object(object(node, "observedVersion"),
                    "expression"), declared, depth + 1);
        }
        if (!"BinaryExpression".equals(type)) return null;
        Object left = value(object(node, "_left"), declared, depth + 1);
        Object right = value(object(node, "_right"), declared, depth + 1);
        if (left == null || right == null) return null;
        return apply(primitiveString(node, "_op"), left, right);
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
        String value = recorded.trim();
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
     * An observed version is stated by a WriteRow or a read's
     * {@code mintVersion} (HANDOVER SS1.4); missing is a DIAGNOSTIC.  A
     * WriteRow at a placeholder's minted version is BLOCKING (nobody wrote
     * it); keyed by {@code location@mintVersion}, never by symbol, since
     * {@code x.f = <mint symbol>} is a real write.
     */
    private static void versions(SessionReader session, List<GapRow> gaps) {
        Set<String> stated = new LinkedHashSet<String>();
        for (WriteRow row : session.writes()) {
            stated.add(row.location() + "@" + row.version());
        }
        // A placeholder's mintVersion differs from its observedVersion;
        // never key the mint by the observed one.
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
     * MARKER spelled boolean, INTEGRAL/CLOCK plain decimal, one row per
     * (occurrence, rootId).
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
            String value = row.recordedValue().trim();
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
     * CONTRACT-SPEC SS2: {@code phiTerm} is in the FATAL polarity.  A reached
     * anchor with no predicate is a concrete branch (DIAGNOSTIC) unless the
     * fatal arm was observed (BLOCKING).  An observed fatal's phi must HOLD
     * at the session's valuation where the roots decide it.
     */
    private static void targets(SessionReader session,
                                Map<String, String> executed,
                                List<GapRow> gaps) {
        Map<String, String> declared = executed == null
                ? Collections.<String, String>emptyMap() : executed;
        for (TargetRow row : session.targets()) {
            boolean empty = row.phiTerm().trim().isEmpty();
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
     * A focused replay's session states the arm its focus row {@code flip}
     * asked for (HANDOVER SS1.5).  DIAGNOSTIC: the result row carries the
     * verdict.
     */
    public static List<GapRow> flipped(JsonObject flip,
                                       SessionReader session) {
        List<GapRow> gaps = new ArrayList<GapRow>();
        JsonObject named = object(flip, "flip");
        String site = primitiveString(named, "siteId");
        if (site.isEmpty()) return gaps;
        int ordinal = optionalInteger(named, "ordinal", 1);
        boolean outcome = optionalBool(named, "outcome", false);
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
     * R4: every root symbol a session names has a RootMintRow in that
     * session.  The root set is epoch-wide; BLOCKING, since an unrowed
     * symbol is a root free at every valuation.  "Names" uses the same walk
     * as COMPOSE ({@link Arms#symbolsIn}).  Runtime half:
     * {@code RootMint#mintUnattributed}.
     */
    private static void attributed(List<SessionReader> sessions,
                                   List<GapRow> gaps) {
        Map<String, String> roots = new LinkedHashMap<String, String>();
        for (SessionReader session : sessions) {
            for (RootMintRow row : session.roots()) {
                roots.putIfAbsent(row.rootId(), row.symbol());
            }
        }
        if (roots.isEmpty()) return;
        for (SessionReader session : sessions) {
            Map<String, String> named = named(session);
            Set<String> stated = new LinkedHashSet<String>();
            for (RootMintRow row : session.roots()) {
                stated.add(row.rootId());
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

    /** Every symbol one session names, with one citation (rows first). */
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
        String text = term.trim();
        while (negation(text)) {
            text = operand(text);
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

    /** One string-to-string member of a row, or an empty map. */
    private static Map<String, String> strings(JsonObject node,
                                               String member) {
        Map<String, String> read = new LinkedHashMap<String, String>();
        for (Map.Entry<String, JsonElement> entry
                : object(node, member).entrySet()) {
            if (!entry.getValue().isJsonPrimitive()) continue;
            read.put(entry.getKey(), entry.getValue().getAsString());
        }
        return read;
    }
}

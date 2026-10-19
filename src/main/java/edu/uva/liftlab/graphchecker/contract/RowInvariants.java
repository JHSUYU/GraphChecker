package edu.uva.liftlab.graphchecker.contract;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.primitiveString;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.Arms;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.function.Function;
import java.util.function.ToLongFunction;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public final class RowInvariants {
    private static final Pattern REFERENCE =
            Pattern.compile("EXPR\\.[0-9a-fA-F]{16}");
    private static final Pattern REFERENCE_LIKE =
            Pattern.compile("EXPR\\.[0-9a-zA-Z_.\\-]*");
    private static final Pattern MINTED =
            Pattern.compile("^M_(L'[^']*'|[A-Z])_(.*)$");
    private static final Pattern LITERAL =
            Pattern.compile("^Y_([A-Z])_(-?[0-9]+)$");
    private static final Pattern DECIMAL = Pattern.compile("^-?[0-9]+$");
    public static final String PLACEHOLDER = "#PLACEHOLDER#";

    private RowInvariants() {
    }

    public interface Gated {
        String sessionId();

        boolean seed();

        Map<String, String> roots();

        Map<String, String> named() throws IOException;
    }

    public static final class Judged implements Gated {
        private final String sessionId;
        private final boolean seed;
        private final Map<String, String> roots;
        private final Map<String, String> named;

        public Judged(String sessionId, boolean seed, Map<String, String> roots,
                      Map<String, String> named) {
            this.sessionId = sessionId;
            this.seed = seed;
            this.roots = Collections.unmodifiableMap(
                    new LinkedHashMap<String, String>(roots));
            this.named = Collections.unmodifiableMap(
                    new LinkedHashMap<String, String>(named));
        }

        @Override
        public String sessionId() {
            return sessionId;
        }

        @Override
        public boolean seed() {
            return seed;
        }

        @Override
        public Map<String, String> roots() {
            return roots;
        }

        @Override
        public Map<String, String> named() {
            return named;
        }
    }

    public static final class Checked {
        public final List<GapRow> gaps;
        public final List<Judged> judged;

        Checked(List<GapRow> gaps, List<Judged> judged) {
            this.gaps = gaps;
            this.judged = judged;
        }
    }

    private static final class Member {
        final String sessionId;
        final boolean seed;
        final Map<String, String> roots;
        final SessionReader header;
        final Gated before;

        private Member(String sessionId, boolean seed,
                       Map<String, String> roots, SessionReader header,
                       Gated before) {
            this.sessionId = sessionId;
            this.seed = seed;
            this.roots = roots;
            this.header = header;
            this.before = before;
        }

        static Member of(SessionReader header) {
            return new Member(header.sessionId(), header.seed(),
                    firstRoots(header), header, null);
        }

        static Member of(Gated before) {
            return new Member(before.sessionId(), before.seed(),
                    before.roots(), null, before);
        }
    }

    public static Checked check(List<? extends Gated> admitted,
                                List<SessionDir> gated,
                                Map<String, List<JsonObject>> focus)
            throws IOException {
        List<GapRow> gaps = new ArrayList<GapRow>();
        List<Judged> judged = new ArrayList<Judged>();
        if (gated.isEmpty()) return new Checked(gaps, judged);
        Map<String, SessionDir> fresh = new LinkedHashMap<String, SessionDir>();
        for (SessionDir dir : gated) fresh.put(dir.sessionId(), dir);
        TreeMap<String, Member> epoch = new TreeMap<String, Member>();
        for (Gated before : admitted) {
            if (!fresh.containsKey(before.sessionId())) {
                epoch.put(before.sessionId(), Member.of(before));
            }
        }
        for (SessionDir dir : gated) {
            epoch.put(dir.sessionId(), Member.of(SessionReader.readHeader(dir)));
        }
        sessionSet(epoch.values(), gaps);
        Map<String, String> roots = epochRoots(epoch.values(), false);
        Map<String, String> brought = new LinkedHashMap<String, String>(roots);
        brought.entrySet().removeAll(epochRoots(epoch.values(), true)
                .entrySet());
        for (Member member : epoch.values()) {
            if (member.before != null) {
                if (!brought.isEmpty()) {
                    attributed(member.sessionId, member.roots.keySet(),
                            member.before.named(), brought, gaps);
                }
                continue;
            }
            SessionReader session = SessionReader.read(
                    fresh.get(member.sessionId));
            complete(session, gaps);
            List<JsonObject> rows = focus.getOrDefault(session.sessionId(),
                    Collections.<JsonObject>emptyList());
            check(session, rows.isEmpty() ? null : rows.get(0), gaps);
            Map<String, String> named = named(session);
            attributed(session.sessionId(), firstRoots(session).keySet(),
                    named, roots, gaps);
            for (JsonObject row : rows) gaps.addAll(flipped(row, session));
            judged.add(new Judged(session.sessionId(), session.seed(),
                    firstRoots(session), named));
        }
        return new Checked(gaps, judged);
    }

    private static Map<String, String> firstRoots(SessionReader session) {
        Map<String, String> roots = new LinkedHashMap<String, String>();
        for (RootMintRow row : session.roots()) {
            roots.putIfAbsent(row.rootId(), row.symbol());
        }
        return roots;
    }

    private static void check(SessionReader session, JsonObject ask,
                              List<GapRow> gaps) {
        activated(session, gaps);
        neverNeither(session, gaps);
        references(session, gaps);
        onePerEvent(session, gaps);
        sorts(session, gaps);
        Map<String, String> executed = executed(session, ask, gaps);
        decisions(session, executed, gaps);
        versions(session, gaps);
        referents(session, gaps);
        roots(session, gaps);
        targets(session, executed, gaps);
    }


    private static void sessionSet(Collection<Member> epoch,
                                   List<GapRow> gaps) {
        List<String> stated = new ArrayList<String>();
        for (Member member : epoch) {
            if (member.seed) stated.add(member.sessionId);
            SessionManifest manifest = member.header == null ? null
                    : member.header.manifest();
            if (manifest == null || !manifest.seed()
                    || manifest.obligationIds().isEmpty()) {
                continue;
            }
            gaps.add(GapRow.of(member.sessionId, GapKind.ADMISSION_GAP,
                    GapClass.BLOCKING, "epoch/sessions",
                    "invariant 1: this session states role SEED and names "
                            + "the obligations it ran "
                            + manifest.obligationIds()
                            + "; a replay handed an obligation is a "
                            + "counterfactual, not the recording"));
        }
        if (stated.size() == 1) return;
        gaps.add(GapRow.of(stated.isEmpty()
                        ? epoch.iterator().next().sessionId : stated.get(0),
                GapKind.ADMISSION_GAP, GapClass.BLOCKING, "epoch/sessions",
                "invariant 1 (CONTRACT-SPEC §2.6: every session states its "
                        + "role in manifest.json): " + stated.size() + " of "
                        + epoch.size() + " sessions state role SEED "
                        + stated + "; exactly one must"));
    }

    private static void complete(SessionReader session, List<GapRow> gaps) {
        if (session.incomplete().isEmpty()) return;
        gaps.add(GapRow.of(session.sessionId(), GapKind.SESSION_INCOMPLETE,
                GapClass.BLOCKING, session.sessionId(),
                "this session could not be read whole: "
                        + session.incomplete()));
    }

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
                "invariant 1 (CONTRACT-SPEC §2.6: one ActivationRow per "
                        + "activation): this session published no activation "
                        + "for the occurrence this row is about"));
    }


    private static void neverNeither(SessionReader session,
                                     List<GapRow> gaps) {
        for (ReadRow row : session.reads()) {
            if (row.observedVersion() >= 0) continue;
            if (row.concreteValue() != null) continue;
            gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, "reads", row.seq(),
                    "observedVersion/concreteValue",
                    row.endpoint().site() + " " + row.location(),
                    "invariant 2 (CONTRACT-SPEC §2.6: every ReadRow must "
                            + "have an observedVersion or a plain decimal "
                            + "concreteValue, never both absent)"));
        }
        for (AttachRow row : session.attaches()) {
            String key = row.pairedBy();
            if (key == null || AttachRow.HANDLE.equals(key)
                    || AttachRow.CORRELATION_PORT.equals(key)) {
                continue;
            }
            gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, "attaches", row.seq(), "pairedBy",
                    row.endpoint().id() + "=" + key,
                    "invariant 2 (CONTRACT-SPEC §2.6: an attach is paired by "
                            + "the handle or by correlation+port): this row "
                            + "names a third key, so which evidence paired "
                            + "it has no answer"));
        }
    }


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
                        "invariant 3 (CONTRACT-SPEC §2.6: one symbol spelling): "
                                + "an expression reference is EXPR. and "
                                + "sixteen hex digits; this is not");
                continue;
            }
            if (table.expression(ref) != null) continue;
            say(session, gaps, said, GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, kind, seq, field, ref,
                    "invariant 3 (CONTRACT-SPEC §2.6: a term's references are "
                            + "resolved through the SESSION's "
                            + "ExpressionTable): this session's "
                            + "expressions.jsonl holds " + table.refs().size()
                            + " expression(s) and not this one");
        }
    }


    private static void onePerEvent(SessionReader session,
                                    List<GapRow> gaps) {
        Set<String> seen = new LinkedHashSet<String>();
        for (ReadRow row : session.reads()) {
            boolean store = row.location().kind() == LocationKind.STORE
                    || row.location().kind() == LocationKind.VIEW;
            twice(session, gaps, seen, "reads", row.seq(), store
                    ? "occurrence/seq/location/version" : "seq/location",
                    (store ? row.endpoint().occurrence().id() + "|" : "")
                            + row.seq() + "|" + row.location()
                            + (store ? "|" + row.observedVersion() : ""),
                    row.location() + "");
        }
        for (WriteRow row : session.writes()) {
            boolean store = row.location().kind() == LocationKind.STORE
                    || row.location().kind() == LocationKind.VIEW;
            twice(session, gaps, seen, "writes", row.seq(), store
                    ? "seq/location/version" : "seq/location", row.seq() + "|"
                    + row.location() + (store ? "|" + row.version() : ""),
                    row.location() + "");
        }
        for (DecisionRow row : session.decisions()) {
            twice(session, gaps, seen, "decisions", row.seq(),
                    "seq/siteId/ordinal", row.seq() + "|" + row.siteId()
                            + "|" + row.ordinal(),
                    row.siteId() + "#" + row.ordinal());
        }
        for (TargetRow row : session.targets()) {
            twice(session, gaps, seen, "targets", row.seq(),
                    "occurrence/seq/anchorSiteId", row.occurrence().id()
                            + "|" + (row.reachedAnchor() ? row.seq() : 0L)
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
                "invariant 4 (CONTRACT-SPEC §2.6: one row per event): a "
                        + "second row of this kind states the same event"));
    }

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
            int frames = endpoint.siteIndex().frames().size();
            gaps.add(violation(session, GapKind.LINEAGE_LOST,
                    GapClass.DIAGNOSTIC, kind, seqs.iterator().next(),
                    "endpoint.siteIndex", endpoint.site(),
                    "invariant 4 site index missing (IDENTITY §4: the "
                            + "site index distinguishes repeated events of "
                            + "one site): " + seqs.size() + " events of this "
                            + "site in one occurrence share one endpoint id, "
                            + "at seqs " + seqs + "; the index "
                            + (frames == 0 ? "is empty"
                                    : "has " + frames + " frame(s) and is "
                                    + "equal for all of them")));
        }
    }


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
            spelledAsDeclared(session, gaps, "reads", row.seq(), row.symbol(),
                    row.javaType());
        }
    }

    private static void spelledAsDeclared(SessionReader session,
                                          List<GapRow> gaps, String kind,
                                          long seq, String symbol,
                                          String javaType) {
        Matcher minted = MINTED.matcher(symbol);
        if (!minted.matches()) return;
        String spelled = minted.group(1).substring(0, 1);
        if (spelled.equals(javaType.substring(0, 1))) return;
        gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                GapClass.BLOCKING, kind, seq, "symbol/javaType", symbol,
                "invariant 5 (CONTRACT-SPEC §2.6: one symbol spelling): the "
                        + "symbol is spelled sort " + spelled
                        + " and the row declares javaType " + javaType));
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
                "invariant 5 (CONTRACT-SPEC §2.6: one symbol spelling): this "
                        + "name is spelled sort " + spelled + " here and sort "
                        + held[0] + " at " + held[1]));
    }


    private static void decisions(SessionReader session,
                                  Map<String, String> executed,
                                  List<GapRow> gaps) {
        if (executed == null || executed.isEmpty()) return;
        for (DecisionRow row : session.decisions()) {
            if (row.term().trim().isEmpty()) continue;
            Boolean held = truth(session, row.term(), executed);
            if (held == null
                    || held.booleanValue() == row.concreteOutcome()) {
                continue;
            }
            gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, "decisions", row.seq(), "outcome",
                    row.siteId() + "#" + row.ordinal(),
                    "invariant 6 (CONTRACT-SPEC §2.6: outcome says whether the "
                            + "published term HELD; the conjunct is "
                            + "outcome ? term : (not term)): at the root "
                            + "values this session RAN under the term is "
                            + held + " and the row says "
                            + row.concreteOutcome()));
        }
    }

    private static Map<String, String> executed(SessionReader session,
                                                JsonObject ask,
                                                List<GapRow> gaps) {
        SessionManifest manifest = session.manifest();
        boolean focused = manifest != null && !manifest.seed();
        if (focused && ask == null) {
            gaps.add(GapRow.of(session.sessionId(), GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, "epoch/valuation",
                    "invariant 6 (CONTRACT-SPEC §2.6: a focused replay runs "
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
        Map<String, String> bySymbol = new LinkedHashMap<String, String>();
        for (RootMintRow row : session.roots()) {
            if (!row.declared()) continue;
            bySymbol.put(row.symbol(), ran(row, assigned));
        }
        return bySymbol;
    }

    private static String ran(RootMintRow row, Map<String, String> assigned) {
        String recorded = row.recordedValue().trim();
        if (assigned == null || row.kind() == RootKind.CLOCK) {
            return recorded;
        }
        String planted = assigned.get(row.rootId());
        if (planted == null || planted.trim().isEmpty()) return recorded;
        return planted.trim();
    }

    private static Boolean truth(SessionReader session, String term,
                                 Map<String, String> declared) {
        String text = term.trim();
        boolean negated = false;
        while (negation(text)) {
            negated = !negated;
            text = operand(text);
        }
        Object value = REFERENCE.matcher(text).matches()
                ? value(session.expressions().expression(text), declared)
                : literal(text);
        if (!(value instanceof Boolean)) return null;
        boolean held = ((Boolean) value).booleanValue();
        return Boolean.valueOf(negated != held);
    }

    private static boolean negation(String text) {
        return text.startsWith("(not ") && text.endsWith(")");
    }

    private static String operand(String negation) {
        return negation.substring(5, negation.length() - 1).trim();
    }

    private static Object value(JsonObject root,
                                Map<String, String> declared) {
        if (root == null) return null;
        Map<JsonObject, Object> values =
                new IdentityHashMap<JsonObject, Object>();
        List<JsonObject> pending = new ArrayList<JsonObject>();
        pending.add(root);
        while (!pending.isEmpty()) {
            JsonObject node = pending.get(pending.size() - 1);
            JsonObject[] operands = operands(node);
            boolean ready = true;
            for (JsonObject operand : operands) {
                if (operand != null && !values.containsKey(operand)) {
                    pending.add(operand);
                    ready = false;
                }
            }
            if (!ready) continue;
            pending.remove(pending.size() - 1);
            values.put(node, value(node, operands, values, declared));
        }
        return values.get(root);
    }

    private static JsonObject[] operands(JsonObject node) {
        String type = primitiveString(node, "_type");
        if ("ConsumerBoundaryExpression".equals(type)) {
            return new JsonObject[]{member(node, "expression")};
        }
        if ("ReadFromExpression".equals(type)) {
            return new JsonObject[]{member(member(node, "observedVersion"),
                    "expression")};
        }
        if ("BinaryExpression".equals(type)) {
            return new JsonObject[]{member(node, "_left"),
                    member(node, "_right")};
        }
        return new JsonObject[0];
    }

    private static JsonObject member(JsonObject node, String name) {
        JsonElement value = node == null ? null : node.get(name);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : null;
    }

    private static Object value(JsonObject node, JsonObject[] operands,
                                Map<JsonObject, Object> values,
                                Map<String, String> declared) {
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
        if (operands.length == 0) return null;
        Object[] held = new Object[operands.length];
        for (int index = 0; index < operands.length; index++) {
            held[index] = values.get(operands[index]);
            if (held[index] == null) return null;
        }
        return operands.length == 1 ? held[0]
                : apply(primitiveString(node, "_op"), held[0], held[1]);
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


    private static void versions(SessionReader session, List<GapRow> gaps) {
        Set<String> stated = new LinkedHashSet<String>();
        for (WriteRow row : session.writes()) {
            stated.add(row.location() + "@" + row.version());
        }
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
                    key, "invariant 7 (CONTRACT-SPEC §2.6: a read joins the "
                            + "expression of the write version it observed, "
                            + "or the placeholder mint that "
                            + "states it): no WriteRow of this session states "
                            + "this version and no placeholder read mints it");
        }
        for (ReadRow row : session.reads()) {
            if (!row.endpoint().site().contains(PLACEHOLDER)) continue;
            if (row.mintVersion() >= 0) continue;
            gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, "reads", row.seq(), "mintVersion",
                    row.location() + "", "invariant 7 (CONTRACT-SPEC §2.6: a "
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


    private static void roots(SessionReader session, List<GapRow> gaps) {
        Set<String> minted = new LinkedHashSet<String>();
        for (RootMintRow row : session.roots()) {
            if (!row.declared()) {
                gaps.add(violation(session, GapKind.DECLARATION_MISSING,
                        GapClass.BLOCKING, "roots", row.seq(), "declared",
                        row.rootId(),
                        "invariant 8 (CONTRACT-SPEC §2.6: a RootMintRow is "
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
                        "invariant 8 (CONTRACT-SPEC §2.6): a " + row.kind()
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
                    "invariant 8 (CONTRACT-SPEC §2.6): this occurrence already "
                            + "minted this root, so the session states two "
                            + "values for one source in one activation"));
        }
    }


    private static void targets(SessionReader session,
                                Map<String, String> executed,
                                List<GapRow> gaps) {
        Map<String, String> declared = executed == null
                ? Collections.<String, String>emptyMap() : executed;
        for (TargetRow row : session.targets()) {
            if (!row.reachedAnchor()) continue;
            if (row.phiTerm().trim().isEmpty()) {
                gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                        row.observedFatal() ? GapClass.BLOCKING
                                : GapClass.DIAGNOSTIC, "targets", row.seq(),
                        "phiTerm", row.anchorSiteId(),
                        "invariant 9 (CONTRACT-SPEC §2.6: a reached anchor "
                                + "states phi, a concrete condition as the "
                                + "constant of its arm): the anchor was "
                                + "reached and states no predicate"
                                + (row.observedFatal()
                                        ? ", and the run OBSERVED the fatal "
                                        + "arm, so the witness would rest on "
                                        + "a predicate no row states"
                                        : "")));
                continue;
            }
            Boolean held = truth(session, row.phiTerm(), declared);
            if (held == null || held.booleanValue() == row.observedFatal()) {
                continue;
            }
            gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, "targets", row.seq(), "phiTerm",
                    row.anchorSiteId(),
                    "invariant 9 (CONTRACT-SPEC §2.6: phiTerm is published in "
                            + "the FATAL polarity): the run "
                            + (row.observedFatal()
                                    ? "observed the fatal arm and this term "
                                    + "is FALSE"
                                    : "took the healthy arm and this term is "
                                    + "TRUE")
                            + " at the root values this session RAN under"));
        }
    }


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
                "invariant 10 (CONTRACT-SPEC §2.6: a focused replay is ADMITTED "
                        + "when the flip took the other arm): this session "
                        + "states no decision at that site and ordinal with "
                        + "outcome " + outcome + "; the obligation's own "
                        + "result row carries the verdict"));
        return gaps;
    }


    private static void attributed(String sessionId, Set<String> stated,
                                   Map<String, String> named,
                                   Map<String, String> roots,
                                   List<GapRow> gaps) {
        if (roots.isEmpty()) return;
        for (Map.Entry<String, String> root : roots.entrySet()) {
            if (stated.contains(root.getKey())) continue;
            String where = named.get(root.getValue());
            if (where == null) continue;
            gaps.add(GapRow.of(sessionId,
                    GapKind.MINT_UNATTRIBUTED, GapClass.BLOCKING,
                    root.getKey(),
                    "invariant 11 (CONTRACT-SPEC §2.6: a root symbol "
                            + "without its RootMintRow): session "
                            + sessionId + " references symbol "
                            + root.getValue() + " at " + where
                            + " and states no RootMintRow for root "
                            + root.getKey() + ", so it carries a "
                            + "quantity no row of it attributes"));
        }
    }

    private static Map<String, String> epochRoots(Collection<Member> epoch,
                                                  boolean before) {
        Map<String, String> roots = new LinkedHashMap<String, String>();
        for (Member member : epoch) {
            if (before && member.before == null) continue;
            for (Map.Entry<String, String> root : member.roots.entrySet()) {
                roots.putIfAbsent(root.getKey(), root.getValue());
            }
        }
        return roots;
    }

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
        Set<JsonElement> walked = Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>());
        for (Map.Entry<String, JsonObject> entry
                : session.expressions().expressions().entrySet()) {
            Set<String> symbols = new LinkedHashSet<String>();
            Arms.symbolsIn(entry.getValue(), symbols, walked);
            for (String symbol : symbols) {
                if (!where.containsKey(symbol)) {
                    where.put(symbol,
                            "expressions.jsonl ref=" + entry.getKey());
                }
            }
        }
        return where;
    }

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
            Arms.symbolsIn(session.expressions().expression(text), symbols);
        }
        for (String symbol : symbols) {
            if (!where.containsKey(symbol)) where.put(symbol, place);
        }
    }


    private static void referents(SessionReader session, List<GapRow> gaps) {
        Set<String> stated = new LinkedHashSet<String>();
        for (WriteRow row : session.writes()) {
            stated.add(row.location() + "@" + row.version());
        }
        for (WriteRow row : session.writes()) {
            WriteRow.Referent referent = row.referentState();
            if (referent == null) continue;
            String state = referent.location() + "@" + referent.version();
            if (referent.version() >= row.version()) {
                gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                        GapClass.BLOCKING, "writes", row.seq(),
                        "referentState", row.location() + "@" + row.version()
                                + " -> " + state, "invariant 12 (CONTRACT-SPEC"
                                + " §2.6): the state is not older than the "
                                + "store"));
            } else if (!stated.contains(state)) {
                gaps.add(violation(session, GapKind.UNSTATED_VALUE,
                        GapClass.DIAGNOSTIC, "writes", row.seq(),
                        "referentState", row.location() + "@" + row.version()
                                + " -> " + state, "invariant 12 (CONTRACT-SPEC"
                                + " §2.6): no WriteRow of this session states "
                                + "the referent's state"));
            }
        }
    }


    private static void say(SessionReader session, List<GapRow> gaps,
                            Set<String> said, GapKind kind, GapClass cls,
                            String rowKind, long seq, String field,
                            String subject, String detail) {
        if (!said.add(rowKind + "|" + field + "|" + subject)) return;
        gaps.add(violation(session, kind, cls, rowKind, seq, field, subject,
                detail));
    }

    private static GapRow violation(SessionReader session, GapKind kind,
                                    GapClass cls, String rowKind, long seq,
                                    String field, String subject,
                                    String detail) {
        return GapRow.of(session.sessionId(), kind, cls,
                rowKind + ".jsonl seq=" + seq + " field=" + field + " "
                        + subject, detail);
    }

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

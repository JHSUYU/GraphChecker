package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.explore.Corpus;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.smt.VmRows;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

public final class Independence {
    private static final String LOCATION = "loc:";

    private final Set<Long> decisions = new LinkedHashSet<Long>();
    private final Set<Long> reads = new LinkedHashSet<Long>();
    private final Set<String> locations = new LinkedHashSet<String>();

    private Independence() {
    }

    public boolean keeps(DecisionRow decision) {
        return decisions.contains(decision.seq());
    }

    boolean keeps(ReadRow read) {
        return reads.contains(read.seq());
    }

    static String location(String locationKey) {
        return LOCATION + locationKey;
    }

    public Set<String> locations() {
        return locations;
    }

    static Independence of(Corpus corpus, String session,
                           Collection<String> seedTerms,
                           Collection<String> families,
                           List<DecisionRow> conditions,
                           List<ReadRow> readRows,
                           Function<ReadRow, List<DecisionRow>> built,
                           Corpus.Claims claims) {
        SmtLowering.SessionJoin join = corpus.join(session);
        Set<String> bound = new LinkedHashSet<String>(families);
        Predicate<String> moving = variable -> bound.contains(variable)
                || join.moves(variable);
        Independence kept = new Independence();
        Set<String> named = new LinkedHashSet<String>();
        for (String term : seedTerms) {
            kept.hold(termLeaves(corpus, session, term), named);
        }
        List<Set<String>> byCondition = conditionLeaves(corpus, session,
                conditions);
        List<Set<String>> byRead = new ArrayList<Set<String>>(
                readRows.size());
        List<List<DecisionRow>> guards = new ArrayList<List<DecisionRow>>(
                readRows.size());
        for (ReadRow read : readRows) {
            Set<String> leaves = readLeaves(corpus, session, read, claims);
            List<DecisionRow> shaped = built.apply(read);
            Set<String> value = shaped.isEmpty() ? leaves
                    : new LinkedHashSet<String>(leaves);
            for (DecisionRow decision : shaped) {
                value.addAll(termLeaves(corpus, session,
                        Arms.conjunct(decision)));
            }
            guards.add(shaped);
            byRead.add(value);
        }
        boolean[] keptCondition = new boolean[conditions.size()];
        boolean[] keptRead = new boolean[readRows.size()];
        for (boolean grew = true; grew; ) {
            grew = false;
            for (int at = 0; at < keptCondition.length; at++) {
                if (keptCondition[at] || !shares(byCondition.get(at), moving)) {
                    continue;
                }
                kept.decisions.add(conditions.get(at).seq());
                kept.hold(byCondition.get(at), named);
                keptCondition[at] = true;
                grew = true;
            }
            for (int at = 0; at < keptRead.length; at++) {
                if (keptRead[at]) continue;
                ReadRow read = readRows.get(at);
                String symbol = read.symbol();
                boolean moves = shares(byRead.get(at), moving);
                if (!moves && (symbol == null || !named.contains(symbol))) {
                    continue;
                }
                if (moves && symbol != null && !symbol.isEmpty()) {
                    bound.add(symbol);
                }
                kept.reads.add(read.seq());
                kept.hold(byRead.get(at), named);
                for (DecisionRow decision : guards.get(at)) {
                    kept.decisions.add(decision.seq());
                }
                keptRead[at] = true;
                grew = true;
            }
        }
        return kept;
    }

    private void hold(Set<String> leaves, Set<String> named) {
        for (String leaf : leaves) {
            if (leaf.startsWith(LOCATION)) {
                locations.add(leaf.substring(LOCATION.length()));
            } else {
                named.add(leaf);
            }
        }
    }

    public static Independence ofGuard(Corpus corpus, String session,
                                       String guard,
                                       List<DecisionRow> conditions,
                                       List<ReadRow> readRows) {
        Independence kept = new Independence();
        Set<String> variables = new LinkedHashSet<String>(
                termLeaves(corpus, session, guard));
        List<Set<String>> byCondition = conditionLeaves(corpus, session,
                conditions);
        List<Set<String>> byRead = new ArrayList<Set<String>>(
                readRows.size());
        for (ReadRow read : readRows) {
            byRead.add(readLeaves(corpus, session, read, null));
        }
        boolean[] keptCondition = new boolean[conditions.size()];
        boolean[] keptRead = new boolean[readRows.size()];
        for (boolean grew = true; grew; ) {
            grew = false;
            for (int at = 0; at < keptCondition.length; at++) {
                if (keptCondition[at]
                        || !shares(byCondition.get(at), variables)) {
                    continue;
                }
                kept.decisions.add(conditions.get(at).seq());
                variables.addAll(byCondition.get(at));
                keptCondition[at] = true;
                grew = true;
            }
            for (int at = 0; at < keptRead.length; at++) {
                if (keptRead[at] || !shares(byRead.get(at), variables)) {
                    continue;
                }
                kept.reads.add(readRows.get(at).seq());
                variables.addAll(byRead.get(at));
                keptRead[at] = true;
                grew = true;
            }
        }
        kept.hold(variables, new LinkedHashSet<String>());
        return kept;
    }

    private static List<Set<String>> conditionLeaves(Corpus corpus,
                                                     String session,
                                                     List<DecisionRow> conditions) {
        List<Set<String>> byCondition = new ArrayList<Set<String>>(
                conditions.size());
        for (DecisionRow condition : conditions) {
            byCondition.add(termLeaves(corpus, session,
                    Arms.conjunct(condition)));
        }
        return byCondition;
    }

    private static Set<String> readLeaves(Corpus corpus, String session,
                                          ReadRow read, Corpus.Claims claims) {
        return corpus.readLeaves(session, read, claims,
                () -> walkRead(corpus, session, read,
                        corpus.expressions(session)));
    }

    private static Set<String> walkRead(Corpus corpus, String session,
                                        ReadRow read, ExpressionTable table) {
        Set<String> leaves = new LinkedHashSet<String>();
        String key = SmtLowering.locationKey(read.location());
        leaves.add(LOCATION + key);
        if (read.symbol() != null && !read.symbol().isEmpty()) {
            leaves.add(read.symbol());
        }
        if (read.observedVersion() < 0L) return leaves;
        SmtLowering.SessionJoin join = corpus.join(session);
        expressionLeaves(corpus, session,
                join.writeExpression(key, read.observedVersion()), table,
                leaves, new LinkedHashSet<String>());
        leaves.addAll(join.mintedReadSymbols(read.observedVersion()));
        return leaves;
    }

    private static Set<String> termLeaves(Corpus corpus, String session,
                                          String term) {
        return corpus.leaves(session, "term " + term,
                () -> leaves(corpus, session, term,
                        corpus.expressions(session)));
    }

    private static Set<String> leaves(Corpus corpus, String session,
                                      String term, ExpressionTable table) {
        Set<String> leaves = new LinkedHashSet<String>();
        Set<String> walked = new LinkedHashSet<String>();
        for (String name : SmtNames.symbols(term == null ? "" : term,
                new LinkedHashSet<String>())) {
            if (SmtNames.reference(name)) {
                if (walked.add(name)) {
                    expressionLeaves(corpus, session, table.expression(name),
                            table, leaves, walked);
                }
            } else {
                leaves.add(name);
            }
        }
        return leaves;
    }

    private static void expressionLeaves(Corpus corpus, String session,
                                         JsonElement expression,
                                         ExpressionTable table,
                                         Set<String> into,
                                         Set<String> walked) {
        if (expression == null || expression.isJsonNull()) return;
        Set<JsonElement> seen = Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>());
        List<JsonElement> pending = new ArrayList<JsonElement>();
        pending.add(expression);
        while (!pending.isEmpty()) {
            JsonElement node = pending.remove(pending.size() - 1);
            if (node.isJsonPrimitive()) {
                String text = node.getAsString();
                if (SmtNames.reference(text) && walked.add(text)) {
                    JsonObject referenced = table.expression(text);
                    if (referenced != null) pending.add(referenced);
                }
                continue;
            }
            if (!seen.add(node)) continue;
            if (node.isJsonArray()) {
                for (JsonElement child : node.getAsJsonArray()) {
                    pending.add(child);
                }
                continue;
            }
            if (!node.isJsonObject()) continue;
            JsonObject object = node.getAsJsonObject();
            if (VmExpressionIr.SYMBOL_TYPE.equals(
                    VmExpressionIr.typeOf(object))) {
                String raw = JsonFields.optionalString(object, "_exp");
                if (!raw.isEmpty() && !VmExpressionIr.builtinSymbol(raw)) {
                    into.add(raw);
                }
            }
            JsonElement location = object.get("location");
            if (location != null && location.isJsonObject()) {
                String key = SmtLowering.locationKey(
                        location.getAsJsonObject());
                if (!key.isEmpty()) into.add(LOCATION + key);
                if (!key.isEmpty() && VmRows.GUARDED_READ_TYPE.equals(
                        VmExpressionIr.typeOf(object))) {
                    observed(corpus.join(session), key,
                            VmRows.recordedVersion(object), into, pending);
                }
            }
            List<JsonElement> operands = ContainerSmtCodec.handlesField(object)
                    ? ContainerSmtCodec.fieldOperands(object) : null;
            pending.addAll(operands != null ? operands
                    : object.asMap().values());
        }
    }

    private static void observed(SmtLowering.SessionJoin join, String key,
                                 long version, Set<String> into,
                                 List<JsonElement> pending) {
        JsonElement written = join.writeExpression(key, version);
        if (written != null) pending.add(written);
        into.addAll(join.mintedReadSymbols(version));
        into.addAll(join.readSymbols(key, version));
    }

    private static boolean shares(Set<String> leaves, Set<String> variables) {
        return shares(leaves, (Predicate<String>) variables::contains);
    }

    private static boolean shares(Set<String> leaves,
                                  Predicate<String> variables) {
        for (String leaf : leaves) {
            if (variables.test(leaf)) return true;
        }
        return false;
    }
}

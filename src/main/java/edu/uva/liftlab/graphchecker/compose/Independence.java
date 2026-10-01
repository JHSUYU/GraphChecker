package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.explore.Corpus;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * Constraint independence (KLEE's) over one closure's conditions and reads:
 * those that share a variable with the seed -- the fatal predicate, or the
 * values an arm delivers -- or with a root of the session, directly or
 * through one another.  A condition whose variables are disjoint from all of
 * them names no root and nothing the seed rests on: the recording satisfies
 * it at its recorded values whatever the witness moves, so leaving it out
 * changes no answer, while lowering it lets a condition the composer cannot
 * state (a string operation on a block file's name, a read no write row
 * states) refuse the whole path.
 *
 * <p>A variable is a symbol a recorded expression names (never the VM's
 * built-in null or void), or a tracked location: every read of one location
 * is one variable, since a STATE family moves them together, and a read
 * carries the value its observed write stated.  A field projection names
 * what its lowering reads ({@link ContainerSmtCodec#fieldOperands}), not
 * how the VM reached its owner: walked whole, hdfs-11741 r3's
 * {@code isIterationOver} clock test brought in every block-location list
 * and storage-group lookup its Source had been found through, none of
 * which the composer can state.</p>
 *
 * <p>The same closure seeded by one flipped GUARD alone ({@link #ofGuard})
 * is what an obligation is keyed by ({@code ObligationFactory#dependence}).
 * </p>
 */
public final class Independence {
    private static final String LOCATION = "loc:";

    private final Set<Long> decisions = new LinkedHashSet<Long>();
    private final Set<Long> reads = new LinkedHashSet<Long>();
    private final Set<String> variables = new LinkedHashSet<String>();

    private Independence() {
    }

    /** Whether this condition stays in the formula. */
    public boolean keeps(DecisionRow decision) {
        return decisions.contains(decision.seq());
    }

    /** Whether this read stays in the formula. */
    boolean keeps(ReadRow read) {
        return reads.contains(read.seq());
    }

    /** One tracked location as a variable of this closure. */
    static String location(String locationKey) {
        return LOCATION + locationKey;
    }

    /** The tracked locations the seed rests on, as location keys. */
    public Set<String> locations() {
        Set<String> locations = new LinkedHashSet<String>();
        for (String variable : variables) {
            if (variable.startsWith(LOCATION)) {
                locations.add(variable.substring(LOCATION.length()));
            }
        }
        return locations;
    }

    /**
     * What {@code seedTerms}, the roots and the variables a family binds
     * ({@code bound}: symbols, and {@link #location}s) rest on among these
     * conditions and reads of one session.  A family moves what it binds,
     * so a condition over it is not the recording's to satisfy.  A read
     * kept brings the decisions the referent its write stored was built
     * under ({@code built}, R3-REFCONT §1.6): the value rests on them though
     * no variable of theirs is in it.
     */
    static Independence of(Corpus corpus, String session,
                           Collection<String> seedTerms,
                           Collection<String> bound,
                           List<DecisionRow> conditions,
                           List<ReadRow> readRows,
                           Function<ReadRow, List<DecisionRow>> built) {
        Set<String> seeds = new LinkedHashSet<String>(bound);
        for (String term : seedTerms) {
            seeds.addAll(termLeaves(corpus, session, term));
        }
        for (RootMintRow root : corpus.session(session).roots()) {
            seeds.add(root.symbol());
        }
        return closure(corpus, session, seeds, conditions, readRows, built);
    }

    /**
     * What one flipped GUARD rests on among these conditions and reads of
     * one session.  No root is a seed here: a flip asks only its guard's
     * variables to move, so a condition over another root holds at its
     * recorded value whatever the flip's model is.
     */
    public static Independence ofGuard(Corpus corpus, String session,
                                       String guard,
                                       List<DecisionRow> conditions,
                                       List<ReadRow> readRows) {
        return closure(corpus, session,
                termLeaves(corpus, session, guard), conditions, readRows,
                read -> Collections.<DecisionRow>emptyList());
    }

    private static Independence closure(Corpus corpus, String session,
                                        Set<String> seeds,
                                        List<DecisionRow> conditions,
                                        List<ReadRow> readRows,
                                        Function<ReadRow, List<DecisionRow>>
                                                built) {
        Independence kept = new Independence();
        Set<String> variables = kept.variables;
        variables.addAll(seeds);
        Map<DecisionRow, Set<String>> byCondition =
                new LinkedHashMap<DecisionRow, Set<String>>();
        for (DecisionRow condition : conditions) {
            byCondition.put(condition, termLeaves(corpus, session,
                    Arms.conjunct(condition)));
        }
        Map<ReadRow, Set<String>> byRead =
                new LinkedHashMap<ReadRow, Set<String>>();
        for (ReadRow read : readRows) {
            byRead.put(read, corpus.leaves(session, "read " + read.seq(),
                    () -> readLeaves(corpus, session, read,
                            corpus.expressions(session))));
        }
        for (boolean grew = true; grew; ) {
            grew = false;
            for (Map.Entry<DecisionRow, Set<String>> condition
                    : new ArrayList<Map.Entry<DecisionRow, Set<String>>>(
                    byCondition.entrySet())) {
                if (!shares(condition.getValue(), variables)) continue;
                kept.decisions.add(condition.getKey().seq());
                variables.addAll(condition.getValue());
                byCondition.remove(condition.getKey());
                grew = true;
            }
            for (Map.Entry<ReadRow, Set<String>> read
                    : new ArrayList<Map.Entry<ReadRow, Set<String>>>(
                    byRead.entrySet())) {
                if (!shares(read.getValue(), variables)) continue;
                kept.reads.add(read.getKey().seq());
                variables.addAll(read.getValue());
                for (DecisionRow decision : built.apply(read.getKey())) {
                    variables.addAll(termLeaves(corpus, session,
                            Arms.conjunct(decision)));
                }
                byRead.remove(read.getKey());
                grew = true;
            }
        }
        return kept;
    }

    /** A read's variables: its location, its symbol, and what its observed
     *  write stated. */
    private static Set<String> readLeaves(Corpus corpus, String session,
                                          ReadRow read,
                                          ExpressionTable table) {
        Set<String> leaves = new LinkedHashSet<String>();
        leaves.add(LOCATION + SmtLowering.locationKey(read.location()));
        if (read.symbol() != null && !read.symbol().isEmpty()) {
            leaves.add(read.symbol());
        }
        WriteRow write = read.observedVersion() < 0L ? null
                : corpus.writeOf(session,
                        SmtLowering.locationKey(read.location()),
                        read.observedVersion());
        if (write != null) {
            expressionLeaves(table.expression(write.expressionRef()), table,
                    leaves, new LinkedHashSet<String>());
        }
        return leaves;
    }

    private static Set<String> termLeaves(Corpus corpus, String session,
                                          String term) {
        return corpus.leaves(session, "term " + term,
                () -> leaves(term, corpus.expressions(session)));
    }

    /** A term's variables: its free names, each expression it references
     *  walked. */
    private static Set<String> leaves(String term, ExpressionTable table) {
        Set<String> leaves = new LinkedHashSet<String>();
        Set<String> walked = new LinkedHashSet<String>();
        for (String name : SmtNames.symbols(term == null ? "" : term,
                new LinkedHashSet<String>())) {
            if (SmtNames.reference(name)) {
                if (walked.add(name)) {
                    expressionLeaves(table.expression(name), table, leaves,
                            walked);
                }
            } else {
                leaves.add(name);
            }
        }
        return leaves;
    }

    /** Each node once, by identity: walked as a tree, 18413's cluster-state
     *  chains kept EXPLORE's planning busy for 20 minutes. */
    private static void expressionLeaves(JsonElement expression,
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
                // A constant is no variable: as one, every "x != null" shared
                // "N" with every other (80 of 145 kept per SOLR-18406 path).
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
            }
            List<JsonElement> operands = ContainerSmtCodec.handlesField(object)
                    ? ContainerSmtCodec.fieldOperands(object) : null;
            pending.addAll(operands != null ? operands
                    : object.asMap().values());
        }
    }

    private static boolean shares(Set<String> leaves, Set<String> variables) {
        for (String leaf : leaves) {
            if (variables.contains(leaf)) return true;
        }
        return false;
    }
}

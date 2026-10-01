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
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * Constraint independence over one closure's conditions and reads, by what
 * MOVES.  A variable moves where a witness can give it another value: what
 * the binding rule says moves ({@link SmtLowering.SessionJoin#moves}: a root,
 * a clock cell, a value the session received), what a family binds (an
 * anchor handoff's symbol, a location a STATE family may re-pair), or a read
 * whose value rests on one.  A condition stays exactly when one of its
 * variables moves: one
 * over nothing that moves holds at its recorded values in every world, so
 * leaving it out changes no answer, while lowering it lets a condition the
 * composer cannot state (a string operation on a block file's name, a read
 * no write row states) refuse the whole path.  What the seed -- the fatal
 * predicate, the values an arm delivers -- or a kept condition NAMES is
 * bound: the read stating that symbol stays, and so does what its value
 * names in turn.  A condition that only shares a value that does not move
 * with a kept one does not: sharing is no dependence (SOLR-18413 r9: every
 * lookup of the cluster state shares the map, a serializer's position
 * counter every character it wrote, and closed over sharing one path kept
 * 3479 conditions and reads, among them a tlog write that did not lower).
 *
 * <p>A variable is a symbol a recorded expression names (never the VM's
 * built-in null or void), or a tracked location.  A read's value is what its
 * observed write stated, and rests on the decisions its referent was built
 * under (R3-REFCONT §1.6); a location as a whole moves only where a family
 * binds it, since one family re-pairs every read of it.  A field projection
 * names what its lowering reads ({@link ContainerSmtCodec#fieldOperands}),
 * not how the VM reached its owner: walked whole, hdfs-11741 r3's
 * {@code isIterationOver} clock test brought in every block-location list
 * and storage-group lookup its Source had been found through, none of
 * which the composer can state.</p>
 *
 * <p>An obligation is keyed by the closure one flipped GUARD shares
 * variables with ({@link #ofGuard}, {@code ObligationFactory#dependence}):
 * a question's identity, not a formula, so it closes over sharing.</p>
 */
public final class Independence {
    private static final String LOCATION = "loc:";

    private final Set<Long> decisions = new LinkedHashSet<Long>();
    private final Set<Long> reads = new LinkedHashSet<Long>();
    /** The tracked locations the seed and what is kept read. */
    private final Set<String> locations = new LinkedHashSet<String>();

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
        return locations;
    }

    /**
     * What {@code seedTerms} and the conditions over what moves rest on
     * among these conditions and reads of one session.  What moves: what the
     * binding rule says moves, what a family binds ({@code families}:
     * symbols, and {@link #location}s), and a read whose value rests on one.
     * A read's value rests on the decisions the referent its write stored
     * was built under too ({@code built}, R3-REFCONT §1.6), though no
     * variable of theirs is in it, and a kept read keeps them.
     */
    static Independence of(Corpus corpus, String session,
                           Collection<String> seedTerms,
                           Collection<String> families,
                           List<DecisionRow> conditions,
                           List<ReadRow> readRows,
                           Function<ReadRow, List<DecisionRow>> built) {
        SmtLowering.SessionJoin join = corpus.join(session);
        Set<String> bound = new LinkedHashSet<String>(families);
        Predicate<String> moving = variable -> bound.contains(variable)
                || join.moves(variable);
        Independence kept = new Independence();
        Set<String> named = new LinkedHashSet<String>();
        for (String term : seedTerms) {
            kept.hold(termLeaves(corpus, session, term), named);
        }
        Map<DecisionRow, Set<String>> byCondition = conditionLeaves(corpus,
                session, conditions);
        Map<ReadRow, Set<String>> byRead = new LinkedHashMap<ReadRow,
                Set<String>>();
        Map<ReadRow, List<DecisionRow>> guards =
                new LinkedHashMap<ReadRow, List<DecisionRow>>();
        for (ReadRow read : readRows) {
            Set<String> value = new LinkedHashSet<String>(
                    readLeaves(corpus, session, read));
            guards.put(read, built.apply(read));
            for (DecisionRow decision : guards.get(read)) {
                value.addAll(termLeaves(corpus, session,
                        Arms.conjunct(decision)));
            }
            byRead.put(read, value);
        }
        for (boolean grew = true; grew; ) {
            grew = false;
            for (Iterator<Map.Entry<DecisionRow, Set<String>>> pending =
                         byCondition.entrySet().iterator();
                 pending.hasNext(); ) {
                Map.Entry<DecisionRow, Set<String>> condition = pending.next();
                if (!shares(condition.getValue(), moving)) continue;
                kept.decisions.add(condition.getKey().seq());
                kept.hold(condition.getValue(), named);
                pending.remove();
                grew = true;
            }
            for (Iterator<Map.Entry<ReadRow, Set<String>>> pending =
                         byRead.entrySet().iterator(); pending.hasNext(); ) {
                Map.Entry<ReadRow, Set<String>> read = pending.next();
                String symbol = read.getKey().symbol();
                boolean moves = shares(read.getValue(), moving);
                if (!moves && (symbol == null || !named.contains(symbol))) {
                    continue;
                }
                if (moves && symbol != null && !symbol.isEmpty()) {
                    bound.add(symbol);
                }
                kept.reads.add(read.getKey().seq());
                kept.hold(read.getValue(), named);
                // Its referent's shape is theirs: they are conjoined in the
                // polarity they took, moving or not.
                for (DecisionRow decision : guards.get(read.getKey())) {
                    kept.decisions.add(decision.seq());
                }
                pending.remove();
                grew = true;
            }
        }
        return kept;
    }

    /** A kept item's variables: its locations are read, its symbols bound. */
    private void hold(Set<String> leaves, Set<String> named) {
        for (String leaf : leaves) {
            if (leaf.startsWith(LOCATION)) {
                locations.add(leaf.substring(LOCATION.length()));
            } else {
                named.add(leaf);
            }
        }
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
        Independence kept = new Independence();
        Set<String> variables = new LinkedHashSet<String>(
                termLeaves(corpus, session, guard));
        Map<DecisionRow, Set<String>> byCondition = conditionLeaves(corpus,
                session, conditions);
        Map<ReadRow, Set<String>> byRead =
                new LinkedHashMap<ReadRow, Set<String>>();
        for (ReadRow read : readRows) {
            byRead.put(read, readLeaves(corpus, session, read));
        }
        for (boolean grew = true; grew; ) {
            grew = false;
            for (Iterator<Map.Entry<DecisionRow, Set<String>>> pending =
                         byCondition.entrySet().iterator();
                 pending.hasNext(); ) {
                Map.Entry<DecisionRow, Set<String>> condition = pending.next();
                if (!shares(condition.getValue(), variables)) continue;
                kept.decisions.add(condition.getKey().seq());
                variables.addAll(condition.getValue());
                pending.remove();
                grew = true;
            }
            for (Iterator<Map.Entry<ReadRow, Set<String>>> pending =
                         byRead.entrySet().iterator(); pending.hasNext(); ) {
                Map.Entry<ReadRow, Set<String>> read = pending.next();
                if (!shares(read.getValue(), variables)) continue;
                kept.reads.add(read.getKey().seq());
                variables.addAll(read.getValue());
                pending.remove();
                grew = true;
            }
        }
        kept.hold(variables, new LinkedHashSet<String>());
        return kept;
    }

    private static Map<DecisionRow, Set<String>> conditionLeaves(
            Corpus corpus, String session, List<DecisionRow> conditions) {
        Map<DecisionRow, Set<String>> byCondition =
                new LinkedHashMap<DecisionRow, Set<String>>();
        for (DecisionRow condition : conditions) {
            byCondition.put(condition, termLeaves(corpus, session,
                    Arms.conjunct(condition)));
        }
        return byCondition;
    }

    /** A read's variables: its location, its symbol, and what its observed
     *  write stated (one walk per read and session, {@link Corpus#leaves}). */
    private static Set<String> readLeaves(Corpus corpus, String session,
                                          ReadRow read) {
        return corpus.leaves(session, "read " + read.seq(),
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
        // As the lowering binds the row: the write of the version it saw,
        // else the mint that made that version.
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

    /** A term's variables: its free names, each expression it references
     *  walked. */
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

    /**
     * Each node once, by identity: walked as a tree, 18413's cluster-state
     * chains kept EXPLORE's planning busy for 20 minutes.  A guarded read's
     * value is the write it observed, as the lowering joins it
     * ({@link SmtLowering#bind}), whether or not the VM inlined it.
     */
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

    /**
     * What a guarded read of one version returned, from each source the
     * lowering may bind it to ({@link SmtLowering#bind}): the write of that
     * version, walked; the mint that made it; the rows that state it (a
     * scalar read lowers to its row's symbol, and a join that refuses gives
     * way to the row's pin).
     */
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

package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.compose.SmtNames;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Task;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** One flip query as text: {@link FlipQuery} decides what it says; this only
 *  lays it out (header comments, reached preamble, own variables, definitions,
 *  assertions), asking the builder's {@link Scope} about renaming. */
final class FlipQueryText {

    /** What the query knows about a recorded name; the builder answers. */
    interface Scope {
        /** This session's recorded symbol -> the query's own variable. */
        Map<String, String> renamesOf(String sessionId);

        /** Whether this query states that recorded name of that session. */
        boolean stated(String name, String sessionId);
    }

    private FlipQueryText() {
    }

    /** Exactly the declarations these texts reach, in this query's variables. A
     *  cached lowering holds many more; stating them would blur what the query
     *  rests on. Line-deduplicated: equal minted names mean equal closed terms.
     */
    static Set<String> statedDeclarations(Corpus corpus,
                                          Set<String> lowered, Scope scope,
                                          List<String> texts) {
        Set<String> stated = new LinkedHashSet<String>();
        for (String sessionId : lowered) {
            SmtLowering lowering = corpus.lowering(sessionId);
            if (lowering == null) continue;
            Map<String, String> rename = scope.renamesOf(sessionId);
            for (SmtLowering.Declaration declaration
                    : lowering.reachedBy(texts)) {
                // A recorded symbol the query bound is declared once, by the
                // query.
                if (rename.containsKey(declaration.name)) continue;
                stated.add(declaration.body.isEmpty()
                        ? declaration.render()
                        : "(define-fun " + declaration.name + " () "
                        + declaration.sort + " "
                        + SmtNames.rename(declaration.body, rename,
                        name -> scope.stated(name, sessionId),
                        new LinkedHashSet<String>()) + ")");
            }
        }
        return stated;
    }

    static String render(Corpus corpus, Task task,
                         Corpus.RecordedPath path, Set<String> lowered,
                         Scope scope, Map<String, String> meaning,
                         Map<String, String> sorts, List<String> assertions,
                         Map<String, String> nearest,
                         DecisionRow flipped, int flipIndex) {
        StringBuilder text = new StringBuilder();
        text.append("; task ").append(task.taskId())
                .append(" focused ").append(task.focused().render())
                .append('\n');
        text.append("; path ").append(path.pathId).append(" session ")
                .append(path.sessionId).append('\n');
        text.append("; flip ").append(flipped.siteId()).append('#')
                .append(flipped.ordinal()).append(" recorded ")
                .append(flipped.outcome()).append(" -> ")
                .append(!flipped.outcome()).append(" after ")
                .append(flipIndex).append(" prefix decisions\n");
        for (Map.Entry<String, String> entry : meaning.entrySet()) {
            text.append("; ").append(entry.getKey()).append(" = ")
                    .append(entry.getValue()).append('\n');
        }
        // Preamble: exactly what assertions, declarations and variable sorts
        // reach (SmtNames#reachedPreamble, same rule as the composed query).
        Set<String> declarations = statedDeclarations(corpus, lowered,
                scope, assertions);
        List<String> reaching = new ArrayList<String>(assertions);
        reaching.addAll(declarations);
        reaching.addAll(sorts.values());
        Set<String> opening = new LinkedHashSet<String>();
        for (String sessionId : lowered) {
            SmtLowering lowering = corpus.lowering(sessionId);
            if (lowering == null) continue;
            opening.addAll(SmtNames.reachedPreamble(
                    lowering.preambleLines(), reaching));
        }
        if (opening.isEmpty()) opening.add("(set-logic ALL)");
        for (String line : opening) text.append(line).append('\n');
        // Own variables before definitions: a define-fun over an undeclared
        // constant errors and cascades.
        for (Map.Entry<String, String> entry : sorts.entrySet()) {
            text.append("(declare-fun ").append(entry.getKey())
                    .append(" () ").append(entry.getValue()).append(")\n");
        }
        for (String line : declarations) {
            text.append(line).append('\n');
        }
        for (String assertion : assertions) {
            text.append("(assert ").append(assertion).append(")\n");
        }
        // The nearest world (FlipQuery.Builder#nearest): least movement of
        // roots and clocks.
        if (!nearest.isEmpty()) {
            StringBuilder distance = new StringBuilder();
            for (Map.Entry<String, String> entry : nearest.entrySet()) {
                distance.append(" (abs (- ").append(entry.getKey())
                        .append(' ').append(entry.getValue()).append("))");
            }
            text.append("(minimize ").append(nearest.size() == 1
                    ? distance.substring(1) : "(+" + distance + ")")
                    .append(")\n");
        }
        // No check-sat: the ask is Z3#modelQuery's, so the published query is
        // the one solved. Illegal bare names are quoted once, as in the
        // composed query.
        return SmtNames.legalSymbols(text.toString());
    }
}

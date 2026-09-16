package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Task;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * ONE flip query, as TEXT.  Relocated out of {@link FlipQuery} unchanged.
 *
 * <p>{@link FlipQuery} decides what a flip query SAYS -- which prefix, which
 * arm, which variable stands for which recorded symbol; this decides how it
 * READS, which is the part with no rule in it at all: the header comments
 * that name the task and the flip, the part of each session's preamble the
 * query's own texts reach, the query's variables before the definitions that
 * name them, and the assertions.</p>
 *
 * <p>Two questions the text has to ask the builder that owns the renaming,
 * and no more, so the rendering holds no query state of its own.</p>
 */
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

    /**
     * Exactly the declarations these texts reach, in this query's own
     * variables.
     *
     * <p>A lowering is cached per session and answers many questions, so
     * emitting all of its declarations would state symbols this query
     * does not conjoin, and a reader cannot tell those from the ones the
     * query rests on.  Deduplicated by line: two sessions share a minted
     * name only when the definition is literally the same closed term,
     * because the digest is over the scoped text.</p>
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
                // A recorded symbol the query bound is declared by the
                // query, under its own variable, once.
                if (rename.containsKey(declaration.name)) continue;
                stated.add(declaration.body.isEmpty()
                        ? declaration.render()
                        : "(define-fun " + declaration.name + " () "
                        + declaration.sort + " "
                        + SmtLowering.rename(declaration.body, rename,
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
        // The lowering's own preamble, then EXACTLY the declarations
        // this query's texts reach ({@link #statedDeclarations}).
        Set<String> declarations = statedDeclarations(corpus, lowered,
                scope, assertions);
        // WHAT THIS QUERY REACHES: its assertions, the declarations
        // they reach, and the sorts of its own variables -- which is
        // what decides the part of the preamble the query states
        // (SmtLowering#reachedPreamble, the same rule the composed
        // query is written by).
        List<String> reaching = new ArrayList<String>(assertions);
        reaching.addAll(declarations);
        reaching.addAll(sorts.values());
        Set<String> opening = new LinkedHashSet<String>();
        for (String sessionId : lowered) {
            SmtLowering lowering = corpus.lowering(sessionId);
            if (lowering == null) continue;
            opening.addAll(SmtLowering.reachedPreamble(
                    lowering.preambleLines(), reaching));
        }
        if (opening.isEmpty()) opening.add("(set-logic ALL)");
        for (String line : opening) text.append(line).append('\n');
        // The query's OWN variables before the definitions: a renamed
        // subterm body names them, and a define-fun over a constant
        // nothing has declared yet is an error that cascades into every
        // definition above it.
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
        // No check-sat here: the body is the formula, and what is
        // ASKED of it -- the verdict, then the values of the variables
        // this query declared -- is the one z3 driver's own text
        // ({@link Z3#modelQuery}), so the published query is the
        // question that was actually solved and not a second one.
        // A name SMT-LIB cannot spell bare is quoted, once, on the way
        // out -- the same routine the composed query is rendered by.
        return SmtLowering.legalSymbols(text.toString());
    }
}

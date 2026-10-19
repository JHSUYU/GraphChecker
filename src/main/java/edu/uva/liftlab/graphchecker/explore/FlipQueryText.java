package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.compose.SmtNames;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Task;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

final class FlipQueryText {

    interface Scope {
        Map<String, String> renamesOf(String sessionId);

        boolean stated(String name, String sessionId);
    }

    private FlipQueryText() {
    }

    static Map<String, String> statedDeclarations(Corpus corpus,
                                                  Set<String> lowered,
                                                  Scope scope,
                                                  List<String> texts) {
        Map<String, String> stated = new LinkedHashMap<String, String>();
        SmtNames.Named named = SmtNames.named(texts);
        for (String sessionId : lowered) {
            SmtLowering lowering = corpus.lowering(sessionId);
            if (lowering == null) continue;
            Map<String, String> rename = scope.renamesOf(sessionId);
            for (SmtLowering.Declaration declaration
                    : lowering.reachedBy(named)) {
                if (rename.containsKey(declaration.name)
                        || stated.containsKey(declaration.name)) {
                    continue;
                }
                stated.put(declaration.name, declaration.body.isEmpty()
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
        Collection<String> declarations = statedDeclarations(corpus, lowered,
                scope, assertions).values();
        List<String> reaching = new ArrayList<String>(assertions);
        reaching.addAll(declarations);
        reaching.addAll(sorts.values());
        Set<String> opening = new LinkedHashSet<String>();
        SmtNames.Named named = SmtNames.named(reaching);
        Set<List<String>> offered = new LinkedHashSet<List<String>>();
        for (String sessionId : lowered) {
            SmtLowering lowering = corpus.lowering(sessionId);
            if (lowering == null) continue;
            List<String> preamble = lowering.preambleLines();
            if (offered.add(preamble)) {
                opening.addAll(SmtNames.reachedPreamble(preamble, named));
            }
        }
        if (opening.isEmpty()) opening.add("(set-logic ALL)");
        for (String line : opening) text.append(line).append('\n');
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
        return SmtNames.legalSymbols(text.toString());
    }
}

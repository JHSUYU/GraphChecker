package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RootDomain;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.explore.Corpus;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.Z3;
import java.lang.reflect.Method;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * PairingProbe ITERATION SELECTOR ROOT_DOMAINS SCOPE_MAP [Z3]: why a sat composition names
 * no mechanism.  The recorded valuation is asked four ways -- nothing held, the
 * clocks held, every path's own pairing held, both -- with ClaimPolicy's own ask;
 * for each sat model, the selected path's family arms whose producer ran in
 * ANOTHER session are printed with the attach sites they deliver to.
 *
 *   javac -cp $JAR -d out tools/analysis/PairingProbe.java
 *   java -cp out:$JAR edu.uva.liftlab.graphchecker.compose.PairingProbe \
 *       <iteration-0000> <node/region/REGION.x#k> <root-domains.jsonl> \
 *       <static_scope_map.jsonl>
 */
public class PairingProbe {
    public static void main(String[] a) throws Exception {
        Path iteration = Paths.get(a[0]);
        Corpus corpus = Corpus.read(iteration, null);
        OccurrenceAddress anchor = ComposeMain.anchorOf(a[1], corpus);
        Composer.Composition c = Composer.compose(corpus, anchor,
                RootDomain.declared(Paths.get(a[2])), 128,
                StaticScopeMap.read(Paths.get(a[3])));
        Z3 z3 = new Z3(Paths.get(a.length > 4 ? a[4] : "z3"), 600000L);
        Method ask = ClaimPolicy.class.getDeclaredMethod("outcome",
                Composer.Composition.class, Z3.class,
                Composer.Valuation.class, List.class, boolean.class);
        ask.setAccessible(true);
        List<String> clocks = new ArrayList<>();
        for (String cell : c.clockCells()) {
            Long reading = c.clockReadings().get(cell);
            if (reading == null) continue;
            clocks.add("(assert (! (= " + cell + " "
                    + JavaPrimitiveSmtSemantics.integralLiteral(
                    reading.toString()) + ") :named clock_pinned__"
                    + ArtifactIO.digest(cell, 10) + "))");
        }
        List<String> both = new ArrayList<>(clocks);
        both.addAll(c.recordedPairings());
        Object[][] asks = {{"nothing held", new ArrayList<String>()},
                {"clocks held", clocks},
                {"own pairings held", c.recordedPairings()},
                {"both held", both}};
        System.out.println(c.disjuncts().size() + " paths, " + clocks.size()
                + " clock cells");
        for (Object[] held : asks) {
            report((String) held[0], (ClaimPolicy.Outcome) ask.invoke(null, c,
                    z3, c.valuations().get(0), held[1], false), iteration);
        }
    }

    private static void report(String name, ClaimPolicy.Outcome o,
                               Path iteration) throws Exception {
        System.out.println("== " + name + ": " + o.answer().status()
                + (o.witness() ? " path " + o.selected().path().pathId
                + " of session " + o.selected().path().sessionId : ""));
        if (!o.witness()) return;
        String session = o.selected().path().sessionId;
        String ordinal = o.selected().selector()
                .replaceAll("^path_selector__(\\d+)__.*$", "$1");
        SessionReader own = SessionReader.read(iteration, session);
        for (Map.Entry<String, ComposedFamilies.ArmChoice> arm
                : o.selectedArms().entrySet()) {
            ComposedFamilies.ArmChoice chosen = arm.getValue();
            if (!chosen.family().matches("\\w+_family__" + ordinal + "__.*")
                    || chosen.sessionIds().contains(session)) {
                continue;
            }
            System.out.println("  delivered from session "
                    + chosen.sessionIds() + " (" + chosen.family() + "):");
            for (AttachRow row : own.attaches()) {
                if (chosen.attachEndpointIds().contains(row.endpoint().id())) {
                    System.out.println("    "
                            + row.endpoint().occurrence().node().render()
                            + " " + row.endpoint().site());
                }
            }
        }
    }
}

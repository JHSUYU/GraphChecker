package edu.uva.liftlab.graphchecker.transformer;

import edu.uva.liftlab.graphchecker.analysis.PhaseInfo;
import edu.uva.liftlab.graphchecker.causynth.CausynthPipeline;
import edu.uva.liftlab.graphchecker.option.GraphCheckerOptions;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;

import java.io.IOException;
import java.util.Map;

public class GraphCheckerTransformer extends SceneTransformer {
    public static final PhaseInfo PHASE_INFO = new PhaseInfo(
            "wjtp",
            "graphchecker",
            "Causynth graph synthesis transformer",
            true,
            false);

    private static final Logger LOG = LoggerFactory.getLogger(GraphCheckerTransformer.class);

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        int classCount = 0;
        int concreteMethodCount = 0;

        for (SootClass sootClass : Scene.v().getApplicationClasses()) {
            classCount++;
            concreteMethodCount += sootClass.getMethods().stream()
                    .filter(method -> method.isConcrete())
                    .count();
        }

        LOG.info("GraphChecker visited {} application classes and {} concrete methods",
                classCount, concreteMethodCount);

        try {
            new CausynthPipeline(GraphCheckerOptions.getInstance(), classCount, concreteMethodCount).run();
        } catch (IOException exception) {
            throw new RuntimeException("Causynth pipeline failed", exception);
        }
    }
}

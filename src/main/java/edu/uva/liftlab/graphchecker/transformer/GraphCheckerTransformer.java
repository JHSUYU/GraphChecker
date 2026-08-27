package edu.uva.liftlab.graphchecker.transformer;

import edu.uva.liftlab.graphchecker.causynth.CausynthPipeline;
import edu.uva.liftlab.graphchecker.option.GraphCheckerOptions;
import soot.SceneTransformer;

import java.io.IOException;
import java.util.Map;

public class GraphCheckerTransformer extends SceneTransformer {
    /** The one whole-program pack phase GraphChecker registers. */
    public static final String PHASE_PACK = "wjtp";
    public static final String PHASE_NAME = "wjtp.graphchecker";

    private final GraphCheckerOptions graphCheckerOptions;

    public GraphCheckerTransformer(GraphCheckerOptions graphCheckerOptions) {
        this.graphCheckerOptions = graphCheckerOptions;
    }

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        try {
            new CausynthPipeline(graphCheckerOptions).run();
        } catch (IOException exception) {
            throw new RuntimeException("Causynth pipeline failed", exception);
        }
    }
}

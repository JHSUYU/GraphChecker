package edu.uva.liftlab.graphchecker.transformer;

import edu.uva.liftlab.graphchecker.analysis.PhaseInfo;
import edu.uva.liftlab.graphchecker.grey.GreyStateAnalysisResult;
import edu.uva.liftlab.graphchecker.grey.GreyStateConeExtractor;
import edu.uva.liftlab.graphchecker.grey.GreyStateOutputWriter;
import edu.uva.liftlab.graphchecker.grey.GreyStateProbeInstrumenter;
import edu.uva.liftlab.graphchecker.grey.GreyStateSpec;
import edu.uva.liftlab.graphchecker.grey.GreyStateSpecLoader;
import edu.uva.liftlab.graphchecker.GraphCheckerMain;
import soot.SceneTransformer;

import java.nio.file.Paths;
import java.util.Map;

public final class GreyStateLifecycleTransformer extends SceneTransformer {
    public static final PhaseInfo PHASE_INFO = new PhaseInfo(
            "wjtp",
            "grey_state_lifecycle",
            "Extract grey-state lifecycle semantic events and bounded SMT model",
            true,
            true);

    private final String configFilePath;
    private final GreyStateSpecLoader loader;
    private final GreyStateConeExtractor extractor;
    private final GreyStateOutputWriter outputWriter;

    public GreyStateLifecycleTransformer(String configFilePath) {
        this(configFilePath, new GreyStateSpecLoader(), new GreyStateConeExtractor(), new GreyStateOutputWriter());
    }

    GreyStateLifecycleTransformer(
            String configFilePath,
            GreyStateSpecLoader loader,
            GreyStateConeExtractor extractor,
            GreyStateOutputWriter outputWriter) {
        this.configFilePath = configFilePath;
        this.loader = loader;
        this.extractor = extractor;
        this.outputWriter = outputWriter;
    }

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        if (configFilePath == null || configFilePath.trim().isEmpty()) {
            throw new IllegalArgumentException("Grey-state lifecycle extraction requires -C <config.yaml>");
        }
        GreyStateSpec spec = loader.load(Paths.get(configFilePath));
        GreyStateAnalysisResult result = extractor.extract(spec);
        int probes = 0;
        if (GraphCheckerMain.options != null && !GraphCheckerMain.options.noOutput()) {
            probes = new GreyStateProbeInstrumenter().instrument(result);
        }
        outputWriter.write(spec, result);
        System.out.println("Grey-state lifecycle extraction wrote output to " + spec.getOutputDir());
        System.out.println("events=" + result.getEvents().size()
                + ", summaries=" + result.getTransitionSummaries().size()
                + ", unknowns=" + result.getUnknowns().size()
                + ", inserted_probes=" + probes);
    }
}

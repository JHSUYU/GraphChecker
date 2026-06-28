package edu.uva.liftlab.graphchecker.util;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.PackManager;
import soot.Transform;
import soot.Transformer;

public final class SootUtils {
    private static final Logger LOG = LoggerFactory.getLogger(SootUtils.class);

    private SootUtils() {
    }

    public static Transform addNewTransform(String phasePackName, String phaseName, Transformer transformer) {
        LOG.info("Registering Soot transform {} in pack {}", phaseName, phasePackName);
        Transform phase = new Transform(phaseName, transformer);
        phase.setDeclaredOptions("enabled");
        phase.setDefaultOptions("enabled:false");
        PackManager.v().getPack(phasePackName).add(phase);
        return phase;
    }
}

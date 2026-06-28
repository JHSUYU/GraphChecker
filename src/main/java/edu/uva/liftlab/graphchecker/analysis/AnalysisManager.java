package edu.uva.liftlab.graphchecker.analysis;

import edu.uva.liftlab.graphchecker.transformer.GraphCheckerTransformer;
import edu.uva.liftlab.graphchecker.util.SootUtils;
import soot.Transform;
import soot.Transformer;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

public class AnalysisManager {
    private static final PhaseInfo[] PHASES = {
            GraphCheckerTransformer.PHASE_INFO
    };

    private static AnalysisManager instance;

    private final Map<String, Transform> analysisMap = new HashMap<>();
    private final Map<String, PhaseInfo> phaseInfoMap = new HashMap<>();
    private final Set<String> enabledAnalysisSet = new HashSet<>();

    private AnalysisManager() {
        for (PhaseInfo info : PHASES) {
            phaseInfoMap.put(info.getFullName(), info);
        }
    }

    public static AnalysisManager getInstance() {
        if (instance == null) {
            instance = new AnalysisManager();
        }
        return instance;
    }

    public boolean enableAnalysis(String name) {
        if (!phaseInfoMap.containsKey(name)) {
            return false;
        }
        enabledAnalysisSet.add(name);
        return true;
    }

    public boolean isAnalysisEnabled(String name) {
        return enabledAnalysisSet.contains(name);
    }

    public PhaseInfo getPhaseInfo(String name) {
        return phaseInfoMap.get(name);
    }

    public Iterator<PhaseInfo> phaseInfoIterator() {
        return phaseInfoMap.values().iterator();
    }

    public Transform registerAnalysis(Transformer analysis, PhaseInfo info) {
        Transform phase = SootUtils.addNewTransform(info.getPack(), info.getFullName(), analysis);
        analysisMap.put(info.getFullName(), phase);
        phaseInfoMap.put(info.getFullName(), info);
        return phase;
    }
}

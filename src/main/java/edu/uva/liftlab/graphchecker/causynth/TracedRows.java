package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.number;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.text;

public final class TracedRows {
    public static final String DIGEST_RESOURCE = "causynth-traced-rows.digest";

    private final Set<String> callSites = new HashSet<>();
    private final Set<String> anyCallee = new HashSet<>();
    private final Set<String> callArguments = new HashSet<>();
    private final Set<String> anyArgument = new HashSet<>();
    private final Set<String> methodArguments = new HashSet<>();
    private final Set<String> methodExits = new HashSet<>();
    final String digest;

    private TracedRows(Collection<StaticProgram.RegionRow> skeletons,
                       StaticScopeMap scopeMap,
                       Collection<Map<String, Object>> graph,
                       String digest) {
        this.digest = digest;
        for (StaticScopeMap.Site site : scopeMap.declaredSites()) {
            callSites.add(site.siteId + "\n" + site.declaredCallee);
        }
        anyCallee.addAll(RuntimeSelectedRegionFinalizer.fieldAccessingCalls(
                graph, scopeMap).keySet());
        Set<String> storing =
                RuntimeSelectedRegionFinalizer.storingCalls(scopeMap).keySet();
        anyCallee.addAll(storing);
        anyArgument.addAll(storing);
        for (StaticProgram.RegionRow skeleton : skeletons) {
            for (ConfiguredSourcePhaseContract.Declaration declaration
                    : skeleton.sourcePhasesBySite().values()) {
                if (declaration.category() == RootCategory.HOOK) {
                    anyCallee.add(declaration.siteId());
                }
            }
            for (Map<String, Object> port : skeleton.communicationPorts) {
                tracePort(port);
            }
        }
    }

    static TracedRows of(Collection<StaticProgram.RegionRow> skeletons,
                         File skeletonFile) throws IOException {
        String declared = System.getProperty("causynth.output.dir", "");
        if (declared.trim().isEmpty()) {
            throw new IOException("the campaign declared no "
                    + "-Dcausynth.output.dir: the recording cannot tell which "
                    + "rows its aggregation reads");
        }
        Path output = Paths.get(declared.trim());
        File scopeMap = output.resolve(StaticScopeMap.FILE).toFile();
        File graph = new File(output.toFile(),
                CausynthArtifactWriter.CANDIDATE_GRAPH);
        return new TracedRows(skeletons, StaticScopeMap.read(scopeMap.toPath()),
                MapFields.readRows(graph),
                inputsDigest(scopeMap, graph, skeletonFile));
    }

    static final String RULE = "storing calls' receivers and arguments;"
            + " method entries' windows";

    public static String inputsDigest(File scopeMap, File graph,
                                      File skeletons) throws IOException {
        return ArtifactIO.sha256(RULE + "\n"
                + ArtifactIO.sha256(scopeMap.toPath()) + "\n"
                + ArtifactIO.sha256(graph.toPath()) + "\n"
                + ArtifactIO.sha256(skeletons.toPath()));
    }

    private void tracePort(Map<String, Object> port) {
        String capture = text(port.get(
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND));
        String method = text(port.get(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD));
        String site = SiteId.render(method, number(port.get(
                CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX), -1));
        String callee = text(port.get(
                CommunicationCatalogContract.DECLARED_CALLEE));
        int index = number(port.get(
                CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1);
        if (CommunicationCatalogContract.CAPTURE_CALL_RETURN.equals(capture)) {
            callSites.add(site + "\n" + callee);
        } else if (CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT.equals(
                capture)) {
            callSites.add(site + "\n" + callee);
            callArguments.add(site + "\n" + callee + "\n" + index);
        } else if (CommunicationCatalogContract.CAPTURE_METHOD_PARAMETER
                .equals(capture)) {
            methodArguments.add(method + "\n" + index);
        } else if (CommunicationCatalogContract.CAPTURE_METHOD_RETURN.equals(
                capture)) {
            methodExits.add(method);
        }
    }

    public boolean callSite(String siteId, String declaredCallee) {
        return anyCallee.contains(siteId)
                || callSites.contains(siteId + "\n" + declaredCallee);
    }

    public boolean callArgument(String siteId, String declaredCallee,
                                int index) {
        return anyArgument.contains(siteId)
                || callArguments.contains(siteId + "\n" + declaredCallee
                + "\n" + index);
    }

    public boolean methodArgument(String method, int index) {
        return methodArguments.contains(method + "\n" + index);
    }

    public boolean methodExit(String method) {
        return methodExits.contains(method);
    }
}

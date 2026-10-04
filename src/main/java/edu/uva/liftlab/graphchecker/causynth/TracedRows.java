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

/**
 * Which of the recording's call, argument and exit rows SEED's aggregation
 * reads (PIPELINE §2): the recording weave traces a row only where one of
 * these says so, and still calls every hook, so the event numbering is the
 * same.  The readers, and what each takes:
 *
 * <ul>
 * <li>a declared site's captures ({@code RuntimeRegionPlanner
 *     #declaredSiteCaptures}): the call rows at the site and callee of a
 *     {@code DECLARED_SITE};</li>
 * <li>a field's owners ({@code RuntimeRegionPlanner#stampFieldOwners}): the
 *     call rows at a call that accesses a field of its receiver ({@link
 *     RuntimeSelectedRegionFinalizer#fieldAccessingCalls});</li>
 * <li>a configured source's phases ({@code
 *     RuntimeRegionPlanner#configuredSourcePhases}): the call rows at a
 *     declared configured-source site;</li>
 * <li>a port's captures ({@code RuntimeRegionPlanner
 *     #communicationCaptureEvent}): the call rows at a call-return or
 *     call-argument port's site, the argument row of a call-argument port,
 *     the method-argument row of a parameter port, the exit row of a
 *     method-return port.</li>
 * </ul>
 *
 * Every other call row, argument row and normal-exit row is read by no
 * stage (hdfs-adhoc-49, TestSnapshot: 65 % of the trace's bytes).
 */
public final class TracedRows {
    /**
     * What the recording weave leaves beside the classes it wove: the
     * digest of the static artifacts it decided its rows on ({@link
     * #inputsDigest}).  The recorder states it in the trace's manifest, and
     * the aggregation refuses a trace whose digest is not its own artifacts'
     * ({@code TRACED_ROWS_MISMATCH}): over other artifacts, a declared site
     * or port they add would find no rows and say nothing.
     */
    public static final String DIGEST_RESOURCE = "causynth-traced-rows.digest";

    /** {@code <siteId>\n<declaredCallee>}: every call row there. */
    private final Set<String> callSites = new HashSet<>();
    /** Sites whose every call is traced, whatever its callee. */
    private final Set<String> anyCallee = new HashSet<>();
    /** {@code <siteId>\n<declaredCallee>\n<index>}. */
    private final Set<String> callArguments = new HashSet<>();
    /** {@code <method>\n<index>}. */
    private final Set<String> methodArguments = new HashSet<>();
    private final Set<String> methodExits = new HashSet<>();
    /** {@link #inputsDigest} of the artifacts these rows were read off, or
     *  "" for rows built from no files. */
    final String digest;

    TracedRows(Collection<StaticProgram.RegionRow> skeletons,
               StaticScopeMap scopeMap,
               Collection<Map<String, Object>> graph) {
        this(skeletons, scopeMap, graph, "");
    }

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

    /** The recording weave's: the campaign's static artifacts beside the
     *  candidate skeletons it weaves from ({@code causynth.output.dir}). */
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

    /**
     * The digest of the three static artifacts the rows are decided on: the
     * scope map, the candidate graph and the candidate skeletons, by their
     * bytes.  The weave and the aggregation compute it alike.
     */
    public static String inputsDigest(File scopeMap, File graph,
                                      File skeletons) throws IOException {
        return ArtifactIO.sha256(ArtifactIO.sha256(scopeMap.toPath()) + "\n"
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

    /** The enter, return and unwinding rows of the calls at one site. */
    public boolean callSite(String siteId, String declaredCallee) {
        return anyCallee.contains(siteId)
                || callSites.contains(siteId + "\n" + declaredCallee);
    }

    public boolean callArgument(String siteId, String declaredCallee,
                                int index) {
        return callArguments.contains(siteId + "\n" + declaredCallee + "\n"
                + index);
    }

    public boolean methodArgument(String method, int index) {
        return methodArguments.contains(method + "\n" + index);
    }

    /** A normal exit's row (an exceptional one is always traced). */
    public boolean methodExit(String method) {
        return methodExits.contains(method);
    }
}

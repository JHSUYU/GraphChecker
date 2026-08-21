package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import soot.Body;
import soot.Unit;
import soot.jimple.Stmt;
import soot.toolkits.graph.BriefUnitGraph;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * The static communication and loop catalog of one target-selected slice.
 *
 * <p>A region is coarse: it begins at a selected execution-context entry and
 * includes the selected nested calls executed in that context, and a
 * synchronous call does not split it.  This class therefore publishes
 * <em>sites</em> - one row per discovered communication call site with its
 * typed ports, one row per retained loop with its kind and bound - and never
 * CFG fragments.  A remote handler is a separate region occurrence because it
 * runs in another thread/source context, not because a fragment boundary was
 * cut here.</p>
 *
 * <h2>What the algorithm knows</h2>
 *
 * <p>Nothing about Hadoop.  A {@link CommunicationCallSiteAdapter} decides
 * which invoke is a communication call and where its server entry is; this
 * class only sees {@link CommunicationCallSite}.</p>
 */
final class CommunicationCatalogPlanner {
    private static final Pattern SIGNATURE = Pattern.compile(
            "<([^:]+):\\s+(\\S+)\\s+([^\\s(]+)\\((.*)\\)>");

    private CommunicationCatalogPlanner() {
    }

    /** Static discovery output for one analysis run. */
    static final class Result {
        final List<Map<String, Object>> callSites = new ArrayList<>();
        /** One row per retained loop of a selected method. */
        final List<Map<String, Object>> loops = new ArrayList<>();
        final List<Map<String, Object>> gaps = new ArrayList<>();
        /**
         * Declared callees that are communication boundaries in the selected
         * slice.  This is the authority for where a demand walk stops.
         */
        final Set<String> callSiteCallees = new LinkedHashSet<>();
        /** Resolved post-deserialization server entries. */
        final Set<String> serverEntryMethods = new LinkedHashSet<>();
        /** Implementation frames removed before coarse region closure. */
        final Set<String> regionEnvelopeExclusions = new LinkedHashSet<>();
    }

    /**
     * The same discovery for a campaign that declares no {@code K_L}: every
     * retained loop inherits {@link LoopBoundPolicy#MAX_LOOP_BODY_ITERATIONS}
     * and no row carries a declared bound.
     */
    static Result plan(Collection<String> selectedMethods,
                       Function<String, Body> bodies,
                       CommunicationCallSiteAdapter adapter) {
        return plan(selectedMethods, bodies, adapter,
                DeclaredLoopBodyBounds.none());
    }

    /**
     * Discovers communication call sites and retained loops inside the
     * already target-selected methods.
     *
     * @param selectedMethods the target slice; nothing outside it is scanned
     * @param bodies          resolves a method signature to its Jimple body
     * @param adapter         protocol-specific call-site recognition
     * @param loopBodyBounds  {@code K_L}, as the campaign declared it per
     *                        loop control site
     */
    static Result plan(Collection<String> selectedMethods,
                       Function<String, Body> bodies,
                       CommunicationCallSiteAdapter adapter,
                       DeclaredLoopBodyBounds loopBodyBounds) {
        Result result = new Result();
        if (selectedMethods == null || bodies == null || adapter == null) {
            return result;
        }
        DeclaredLoopBodyBounds bounds = loopBodyBounds == null
                ? DeclaredLoopBodyBounds.none() : loopBodyBounds;
        List<String> ordered = new ArrayList<>(new TreeSet<>(
                selectedMethods));
        // An adapter whose server side is found by structure has to see the
        // whole slice before it can answer about one call site.
        adapter.prepare(ordered, bodies);
        Map<String, List<CommunicationCallSite>> sitesByMethod =
                new LinkedHashMap<>();
        for (String method : ordered) {
            Body body = body(bodies, method);
            if (body == null) continue;
            List<CommunicationCallSite> sites = discover(method, body,
                    adapter, result);
            if (!sites.isEmpty()) sitesByMethod.put(method, sites);
        }

        // Communication the slice declares but no call site covers is a
        // coverage gap, not silence: zero call sites also means zero
        // call-site gaps.
        for (CommunicationDeclarationGap declaration
                : adapter.uncutDeclarations()) {
            result.gaps.add(gap(declaration.kind, declaration.reason,
                    declaration.method, declaration.siteId,
                    declaration.detail));
        }

        Set<String> serverEntries = new TreeSet<>();
        for (List<CommunicationCallSite> sites : sitesByMethod.values()) {
            for (CommunicationCallSite site : sites) {
                Map<String, Object> row = site.row();
                result.callSites.add(row);
                result.callSiteCallees.add(site.declaredCallee);
                serverEntries.addAll(site.serverEntryCandidates);
            }
        }
        result.serverEntryMethods.addAll(serverEntries);

        result.regionEnvelopeExclusions.addAll(
                transportImplementationMethods(
                ordered, result.callSiteCallees, sitesByMethod.keySet(),
                serverEntries, adapter));

        for (String entry : serverEntries) {
            if (body(bodies, entry) == null) {
                result.gaps.add(gap(CommunicationCatalogContract
                                .GAP_SERVER_BODY_UNAVAILABLE,
                        "NO_JIMPLE_BODY", entry, "", entry));
            }
        }

        // Loop discovery is independent of communication: every selected
        // production method may retain loops whether or not it communicates.
        for (String method : ordered) {
            if (result.regionEnvelopeExclusions.contains(method)) continue;
            Body body = body(bodies, method);
            if (body == null) continue;
            catalogLoops(method, body, bounds, result);
        }
        return result;
    }

    // ------------------------------------------------------------------
    // Target-selected call-site discovery
    // ------------------------------------------------------------------

    private static List<CommunicationCallSite> discover(
            String method, Body body, CommunicationCallSiteAdapter adapter,
            Result result) {
        List<CommunicationCallSite> sites = new ArrayList<>();
        int index = -1;
        for (Unit unit : body.getUnits()) {
            index++;
            if (!(unit instanceof Stmt)
                    || !((Stmt) unit).containsInvokeExpr()) {
                continue;
            }
            String callee = ((Stmt) unit).getInvokeExpr().getMethodRef()
                    .getSignature();
            String siteId = CommunicationCatalogContract.siteId(method, index);
            if (reflectiveDispatch(callee)) {
                // A reflective call may hide a communication call site.
                // Naming it keeps the slice honest; guessing an edge would
                // not.
                result.gaps.add(gap(CommunicationCatalogContract
                                .GAP_CALL_SITE_UNRESOLVED,
                        "REFLECTIVE_DISPATCH", method, siteId, callee));
                continue;
            }
            CommunicationResolution resolution = adapter.resolve(method,
                    index, callee);
            if (resolution.isGap()) {
                result.gaps.add(gap(resolution.gapKind,
                        resolution.gapReason, method, siteId,
                        resolution.gapDetail));
            }
            if (resolution.site != null) sites.add(resolution.site);
        }
        return sites;
    }

    // ------------------------------------------------------------------
    // Retained loops
    // ------------------------------------------------------------------

    /**
     * Publishes one row per retained loop of {@code method}: its stable
     * {@code loopSiteId}, its control sites, its kind, the rule that decided
     * the kind, and {@code K_L} where the campaign declared one.
     *
     * <p>A nest is fixed-count only when every one of its guards is: a
     * {@code while} anywhere in the nest decides body executions by data, and
     * claiming an exact cardinality for the nest would state a count nothing
     * proves.  Each way of losing the fixed-count claim, and a
     * condition-bounded loop that declares no {@code K_L} of its own, is named
     * so no later stage has to guess what happened.</p>
     */
    private static void catalogLoops(String method, Body body,
                                     DeclaredLoopBodyBounds bounds,
                                     Result result) {
        List<CfgLoopControl.RetainedLoop> retained =
                CfgLoopControl.retainedLoops(CfgLoopControl.loopCfg(body,
                        new BriefUnitGraph(body)));
        if (retained.isEmpty()) return;
        Map<Unit, Integer> unitIndices = new LinkedHashMap<>();
        int index = -1;
        for (Unit unit : body.getUnits()) {
            unitIndices.put(unit, Integer.valueOf(++index));
        }
        for (CfgLoopControl.RetainedLoop loop : retained) {
            Integer headerPosition = unitIndices.get(loop.header);
            if (headerPosition == null) continue;
            List<String> controlSites = new ArrayList<>();
            for (Unit guard : loop.guards) {
                Integer position = unitIndices.get(guard);
                if (position == null) continue;
                controlSites.add(CommunicationCatalogContract.siteId(method,
                        position.intValue()));
            }
            if (controlSites.isEmpty()) continue;
            String loopSiteId = LoopBoundPolicy.loopSiteId(controlSites);
            boolean fixedCount = LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED
                    .equals(loop.classification);
            if (loop.guardsClassifyDifferently) {
                result.gaps.add(gap(
                        LoopBoundPolicy.GAP_LOOP_CLASSIFICATION_INCONSISTENT,
                        "LOOP_NEST_GUARDS_CLASSIFY_DIFFERENTLY", method,
                        loopSiteId, controlSites.toString()));
            }
            int declaredBound = bounds.bound(controlSites);
            if (!fixedCount && declaredBound == 0) {
                // The loop still runs under the inherited K_L, and the model
                // it produces is a prefix nobody stated for this workload.
                result.gaps.add(gap("BOUNDED_LOOP_BODY_BOUND_UNDECLARED",
                        "INHERITED_K_L_"
                                + LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                        method, loopSiteId, controlSites.toString()));
            }
            Map<String, Object> row = new LinkedHashMap<>();
            row.put(CommunicationCatalogContract.SCHEMA_VERSION_FIELD,
                    CommunicationCatalogContract.SCHEMA_VERSION);
            row.put(CommunicationCatalogContract.KIND, LOOP_ROW_KIND);
            row.put("enclosingMethod", method);
            row.put(LoopBoundPolicy.LOOP_SITE_ID, loopSiteId);
            row.put(LoopBoundPolicy.RUNTIME_LOOP_ID,
                    method + "#loop:u" + headerPosition.intValue());
            row.put(LoopBoundPolicy.LOOP_CONTROL_SITE_IDS, controlSites);
            row.put(LoopBoundPolicy.LOOP_CLASSIFICATION, loop.classification);
            row.put(LoopBoundPolicy.LOOP_CLASSIFICATION_AUTHORITY,
                    CfgLoopControl.classificationAuthority(
                            loop.classification));
            if (declaredBound > 0) {
                row.put(LoopBoundPolicy.LOOP_BODY_BOUND, declaredBound);
            }
            result.loops.add(row);
        }
    }

    /** {@code kind} of one retained-loop catalog row. */
    static final String LOOP_ROW_KIND = "RETAINED_LOOP";

    // ------------------------------------------------------------------
    // Transport surface
    // ------------------------------------------------------------------

    /**
     * The transport surface of the selected slice: every frame that carries
     * a remote call rather than decides one.
     *
     * <p>Three sources, in order of how much they already know:</p>
     *
     * <ol>
     *   <li>every discovered call-site callee.  Transport, serialization and
     *       translator frames between the two semantic sites are
     *       implementation sites, and the callee is the door into them;</li>
     *   <li>every other selected method declared by a callee's own type.
     *       That type is the transport, and its remaining surface in this
     *       slice is the rest of the same transport - most importantly its
     *       <em>receiving</em> half, which no client callee reaches;</li>
     *   <li>whatever the adapter declares.  Protocol knowledge belongs there,
     *       and an adapter that recognises a transport by a rule this class
     *       cannot express says so through
     *       {@link CommunicationCallSiteAdapter#transportImplementationMethods()}.</li>
     * </ol>
     *
     * <p>A semantic site is then removed again, and that subtraction is what
     * makes rule 2 safe: a client call holder and a resolved server entry are
     * where the slice decides something, so neither is transport however its
     * declaring type is used elsewhere.</p>
     */
    private static Set<String> transportImplementationMethods(
            Collection<String> selectedMethods, Set<String> callSiteCallees,
            Set<String> callHolders, Set<String> serverEntries,
            CommunicationCallSiteAdapter adapter) {
        Set<String> transportTypes = new LinkedHashSet<>();
        for (String callee : callSiteCallees) {
            String owner = declaringType(callee);
            if (!owner.isEmpty()) transportTypes.add(owner);
        }
        Set<String> declared = new TreeSet<>(callSiteCallees);
        for (String method : selectedMethods) {
            if (transportTypes.contains(declaringType(method))) {
                declared.add(method);
            }
        }
        for (String method : adapter.transportImplementationMethods()) {
            if (method != null && !method.isEmpty()) declared.add(method);
        }
        declared.removeAll(callHolders);
        declared.removeAll(serverEntries);
        declared.remove("");
        return declared;
    }

    /** Declaring type of a method signature, or {@code ""}. */
    private static String declaringType(String methodSignature) {
        if (methodSignature == null) return "";
        Matcher matcher = SIGNATURE.matcher(methodSignature);
        return matcher.matches() ? matcher.group(1) : "";
    }

    private static boolean reflectiveDispatch(String callee) {
        Matcher matcher = SIGNATURE.matcher(callee);
        if (!matcher.matches()) return false;
        String owner = matcher.group(1);
        String name = matcher.group(3);
        if (owner.startsWith("java.lang.reflect.")) {
            return "invoke".equals(name) || "newProxyInstance".equals(name);
        }
        return "java.lang.invoke.MethodHandle".equals(owner)
                && ("invoke".equals(name) || "invokeExact".equals(name));
    }

    static Map<String, Object> gap(String kind, String reason,
                                   String method, String siteId,
                                   String detail) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put(CommunicationCatalogContract.SCHEMA_VERSION_FIELD,
                CommunicationCatalogContract.SCHEMA_VERSION);
        row.put(CommunicationCatalogContract.KIND,
                CommunicationCatalogContract.GAP_ROW_KIND);
        row.put(CommunicationCatalogContract.GAP_KIND, kind);
        row.put(CommunicationCatalogContract.GAP_REASON, reason);
        row.put(CommunicationCatalogContract.GAP_METHOD, method);
        row.put(CommunicationCatalogContract.GAP_SITE_ID, siteId);
        row.put(CommunicationCatalogContract.GAP_DETAIL, detail);
        return row;
    }

    private static Body body(Function<String, Body> bodies, String method) {
        try {
            return bodies.apply(method);
        } catch (RuntimeException unavailable) {
            return null;
        }
    }
}

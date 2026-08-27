package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import soot.Body;
import soot.Unit;
import soot.jimple.Stmt;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;

/** The static communication and loop catalog of one target-selected slice. */
final class CommunicationCatalogPlanner {
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
     * Discovers communication call sites and retained loops inside the already
     * target-selected methods; nothing outside {@code selectedMethods} is
     * scanned.  {@link DeclaredLoopBodyBounds#none} makes every retained loop
     * inherit {@link LoopBoundPolicy#MAX_LOOP_BODY_ITERATIONS} with no
     * declared bound on any row.
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
        adapter.prepare(ordered);
        Map<String, List<CommunicationCallSite>> sitesByMethod =
                new LinkedHashMap<>();
        for (String method : ordered) {
            Body body = body(bodies, method);
            if (body == null) continue;
            List<CommunicationCallSite> sites = discover(method, body,
                    adapter, result);
            if (!sites.isEmpty()) sitesByMethod.put(method, sites);
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
                serverEntries, adapter, bodies));

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

    /**
     * Publishes one row per retained loop of {@code method}: its stable {@code
     * loopSiteId}, its control sites, its kind, the rule that decided the
     * kind, and {@code K_L} where the campaign declared one.
     */
    private static void catalogLoops(String method, Body body,
                                     DeclaredLoopBodyBounds bounds,
                                     Result result) {
        List<CfgLoopControl.RetainedLoop> retained =
                CfgLoopControl.retainedLoops(CfgLoopControl.loopCfg(body));
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
            boolean fixedCount = CfgLoopControl.fixedCount(
                    loop.classification);
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
            Map<String, Object> row = newRow(LOOP_ROW_KIND);
            row.put("enclosingMethod", method);
            row.put(LoopBoundPolicy.LOOP_SITE_ID, loopSiteId);
            row.put(LoopBoundPolicy.RUNTIME_LOOP_ID,
                    method + "#loop:u" + headerPosition.intValue());
            row.put(LoopBoundPolicy.LOOP_CONTROL_SITE_IDS, controlSites);
            int latchIndex = headerPosition.intValue();
            for (Unit latch : loop.latches) {
                Integer position = unitIndices.get(latch);
                if (position != null) {
                    latchIndex = Math.max(latchIndex, position.intValue());
                }
            }
            row.put(LoopBoundPolicy.LOOP_LATCH_UNIT_INDEX, latchIndex);
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

    /**
     * The transport surface of the selected slice: every frame that carries a
     * remote call rather than decides one.
     */
    private static Set<String> transportImplementationMethods(
            Collection<String> selectedMethods, Set<String> callSiteCallees,
            Set<String> callHolders, Set<String> serverEntries,
            CommunicationCallSiteAdapter adapter,
            Function<String, Body> bodies) {
        Set<String> transportTypes = new LinkedHashSet<>();
        for (String callee : callSiteCallees) {
            String owner = CausynthStaticFacts.methodOwner(callee);
            if (!owner.isEmpty()) transportTypes.add(owner);
        }
        Set<String> declared = new TreeSet<>(callSiteCallees);
        for (String method : selectedMethods) {
            if (transportTypes.contains(
                    CausynthStaticFacts.methodOwner(method))) {
                declared.add(method);
            }
        }
        for (String method : adapter.transportImplementationMethods()) {
            if (method != null && !method.isEmpty()) declared.add(method);
        }
        declared.removeAll(callHolders);
        declared.removeAll(serverEntries);
        declared.remove("");
        declared.removeAll(cutHolderApproaches(declared, callHolders,
                callSiteCallees, bodies));
        return declared;
    }

    /**
     * The transport frames a region member has to keep in order to own the
     * cut attributed to it.
     *
     * <p>A declared client stub may be called from inside the transport
     * surface itself (the encrypted data-transfer handshake is built two
     * frames below the caller that initiates it).  The cut is still this
     * slice's cut and its ports are declared on the region of the caller
     * that reached it, so the frames between that caller and the frame
     * holding the stub call must stay coarse region members: excluded, they
     * break the call chain, no region holds the cut, and the cut's own
     * argument boundary can never be resolved or observed.  Only the frames
     * that actually approach a holder are kept; the stub callee itself and
     * every other implementation frame remain boundaries.</p>
     */
    private static Set<String> cutHolderApproaches(
            Set<String> declared, Set<String> callHolders,
            Set<String> callSiteCallees, Function<String, Body> bodies) {
        Set<String> retained = new LinkedHashSet<>();
        if (declared.isEmpty() || callHolders.isEmpty() || bodies == null) {
            return retained;
        }
        Map<String, Set<String>> callees = new LinkedHashMap<>();
        for (String method : declared) {
            Body body = body(bodies, method);
            if (body == null) continue;
            callees.put(method, invokedSignatures(body));
        }
        // The frames a holder calls to build the request it then cuts on:
        // the declared stub callee stays the boundary, but the value it
        // carries is computed one frame below the holder and the region has
        // to own that frame for the cut argument to have a relation at all.
        for (String holder : callHolders) {
            for (String callee : invokedSignatures(body(bodies, holder))) {
                if (declared.contains(callee)
                        && !callSiteCallees.contains(callee)) {
                    retained.add(callee);
                }
            }
        }
        Set<String> reaching = new LinkedHashSet<>(callHolders);
        reaching.addAll(retained);
        boolean grew = true;
        while (grew) {
            grew = false;
            for (Map.Entry<String, Set<String>> entry : callees.entrySet()) {
                if (retained.contains(entry.getKey())) continue;
                for (String callee : entry.getValue()) {
                    if (!reaching.contains(callee)) continue;
                    retained.add(entry.getKey());
                    reaching.add(entry.getKey());
                    grew = true;
                    break;
                }
            }
        }
        return retained;
    }

    private static boolean reflectiveDispatch(String callee) {
        String owner = CausynthStaticFacts.methodOwner(callee);
        String name = CausynthStaticFacts.methodName(callee);
        if (owner.startsWith("java.lang.reflect.")) {
            return "invoke".equals(name) || "newProxyInstance".equals(name);
        }
        return "java.lang.invoke.MethodHandle".equals(owner)
                && ("invoke".equals(name) || "invokeExact".equals(name));
    }

    /** One schema-stamped catalog row of {@code kind}. */
    static Map<String, Object> newRow(String kind) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put(CommunicationCatalogContract.SCHEMA_VERSION_FIELD,
                CommunicationCatalogContract.SCHEMA_VERSION);
        row.put(CommunicationCatalogContract.KIND, kind);
        return row;
    }

    static Map<String, Object> gap(String kind, String reason,
                                   String method, String siteId,
                                   String detail) {
        Map<String, Object> row = newRow(
                CommunicationCatalogContract.GAP_ROW_KIND);
        row.put(CommunicationCatalogContract.GAP_KIND, kind);
        row.put(CommunicationCatalogContract.GAP_REASON, reason);
        row.put(CommunicationCatalogContract.GAP_METHOD, method);
        row.put(CommunicationCatalogContract.GAP_SITE_ID, siteId);
        row.put(CommunicationCatalogContract.GAP_DETAIL, detail);
        return row;
    }

    /** Every declared callee signature invoked by one body. */
    private static Set<String> invokedSignatures(Body body) {
        Set<String> targets = new LinkedHashSet<>();
        if (body == null) return targets;
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof Stmt)
                    || !((Stmt) unit).containsInvokeExpr()) {
                continue;
            }
            targets.add(((Stmt) unit).getInvokeExpr().getMethodRef()
                    .getSignature());
        }
        return targets;
    }

    private static Body body(Function<String, Body> bodies, String method) {
        try {
            return bodies.apply(method);
        } catch (RuntimeException unavailable) {
            return null;
        }
    }
}

package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OccurrenceId;
import org.junit.Assume;
import org.junit.Test;

import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

/**
 * A value crossing an RPC is lowered exactly like a field read: the
 * receiver's leaf <em>is</em> the sender's expression, as one case merge with
 * one arm per sender case, each guarded by that sender occurrence's case
 * selector.
 *
 * <p>The corpus is the smallest shape that can tell a correct lowering from a
 * collapsed one: one sender region observed in two replays taking two
 * different local cases, exporting {@code k} in one and {@code k + 1} in the
 * other, and one receiver region whose only value is the attached leaf. A
 * lowering that keeps one arm, or that drops the sender's case selector, still
 * produces a receiver value -- it just stops being the sender's, and pinning a
 * sender case then no longer decides what the receiver read.</p>
 */
public class RpcAttachLoweringTest {
    private static final String EPOCH = "epoch-1";
    private static final String FAMILY = "CBF.WIRE";
    private static final String PORT =
            "XCH.da84e470-fe7e-3068-b93f-caafeef64a70.req.wire-key-id";

    /**
     * The attach family becomes one case merge with one arm per sender case,
     * and the receiver's own leaf is replaced by it rather than left as a
     * free boundary reference.
     */
    @Test
    public void attachFamilyLowersToOneArmPerSenderCase() {
        SymbolicPropagationClosure.Result result = corpus();

        assertTrue(result.complete());
        JsonObject merge = merge(result, FAMILY);
        assertEquals(SymbolicPropagationClosure.ITE_TYPE,
                optionalString(merge, "_type"));
        assertEquals(FAMILY, optionalString(merge,
                VmExpressionIr.FAMILY_KEY));
        JsonArray arms = merge.getAsJsonArray("arms");
        assertEquals(2, arms.size());

        // One arm per sender case, each naming that sender occurrence.
        Set<String> caseSelectors = new LinkedHashSet<>();
        Set<String> payloads = new LinkedHashSet<>();
        for (JsonElement encoded : arms) {
            JsonObject arm = encoded.getAsJsonObject();
            assertEquals("S", optionalString(arm, "regionId"));
            assertEquals("S#a1", optionalString(arm, "occurrenceId"));
            caseSelectors.add(optionalString(arm, "caseSelector"));
            payloads.add(arm.get("expression").toString());
        }
        assertEquals(2, caseSelectors.size());
        assertEquals(2, payloads.size());

        // The dependency row the manifest publishes carries the same arms
        // under the RPC_ATTACH kind, so the wire ledger can find them.
        JsonObject dependency = dependency(result, FAMILY);
        assertEquals(VmExpressionIr.RPC_ATTACH,
                optionalString(dependency, "boundaryKind"));
        assertEquals(2, dependency.getAsJsonArray("arms").size());
    }

    /**
     * Pinning one sender case decides the receiver's value, in the SMT the
     * composer's arm shape produces. This is the property the wire exists to
     * carry, and the one a collapsed single-arm merge silently loses.
     */
    @Test
    public void pinningTheSenderCaseFlipsTheReceiverValue() throws Exception {
        Assume.assumeTrue(z3Available());
        JsonArray arms = merge(corpus(), FAMILY).getAsJsonArray("arms");
        assertEquals(2, arms.size());

        List<String> selectors = new ArrayList<>();
        Map<String, Integer> valueBySelector = new LinkedHashMap<>();
        for (JsonElement encoded : arms) {
            JsonObject arm = encoded.getAsJsonObject();
            String selector = optionalString(arm, "caseSelector");
            selectors.add(selector);
            valueBySelector.put(selector, senderValue(arm.get("expression")));
        }
        // The two sender cases really do export different values.
        assertEquals(2, new LinkedHashSet<>(valueBySelector.values()).size());

        // The merge as the composer lowers it: an exactly-one partition over
        // the sender's case selectors, and one implication per arm.
        StringBuilder model = new StringBuilder();
        for (String selector : selectors) {
            model.append("(declare-const ").append(selector)
                    .append(" Bool)\n");
        }
        model.append("(declare-const merged_boundary__wire Int)\n")
                .append(assertion(ConcolicSmtComposer.conditionalExactlyOne(
                        "true", selectors)));
        for (String selector : selectors) {
            model.append(assertion("(=> " + selector
                    + " (= merged_boundary__wire "
                    + valueBySelector.get(selector) + "))"));
        }

        for (String selector : selectors) {
            int expected = valueBySelector.get(selector);
            // Pinning that sender case forces the receiver's leaf to the
            // value that case exported ...
            assertEquals("unsat", solve(model + assertion(selector)
                    + assertion("(not (= merged_boundary__wire "
                    + expected + "))")));
            // ... and rules out the other case's value.
            for (Map.Entry<String, Integer> other
                    : valueBySelector.entrySet()) {
                if (other.getValue() == expected) continue;
                assertEquals("unsat", solve(model + assertion(selector)
                        + assertion("(= merged_boundary__wire "
                        + other.getValue() + ")")));
            }
            // The receiver's value is not pinned without a sender case.
            assertEquals("sat", solve(model.toString()
                    + assertion("(= merged_boundary__wire " + expected
                    + ")")));
        }
    }

    /**
     * An attach whose sender-side expression never reached the join is named
     * as such, rather than sharing the field read's code: the two have
     * different causes and different fixes. Here the producer the handoff
     * names has no selected case at all, so the family carries no arm and the
     * receiver's leaf is left equal to nothing.
     */
    @Test
    public void anAttachWithNoSenderExpressionIsNamed() {
        List<JsonObject> rows = new ArrayList<>();
        String scope = "replay-group:attach-orphan";
        JsonObject leaf = boundary(990L, symbol("M_K"));
        JsonObject receiver = summary("R", "R#a1", "TASK.R.1", scope, leaf);
        // The producer endpoint names an execution this composition selected
        // no case from: the wire's value never entered the join.
        handoff(receiver, FAMILY, 990L, "TASK.S.ABSENT", "S#a1", leaf);
        rows.add(receiver);

        SymbolicPropagationClosure.Result result = rewrite(rows);

        assertFalse(result.complete());
        assertTrue(reasons(result).contains(SymbolicPropagationClosure
                .RPC_ATTACH_SENDER_EXPRESSION_MISSING));
        // The receiver's leaf is left as an unresolved reference, not
        // quietly replaced by a value nothing on the wire produced.
        assertEquals(0, merge(result, FAMILY).size());
    }

    /**
     * One sender region, two replays, two local cases, two exported values,
     * and one receiver whose value is the attached leaf.
     */
    private static SymbolicPropagationClosure.Result corpus() {
        List<JsonObject> rows = new ArrayList<>();
        for (int replay = 1; replay <= 2; replay++) {
            String scope = "replay-group:attach-" + replay;
            // ".2" makes this replay's sender take the other branch, which
            // is what gives it its own local case.
            String senderTask = replay == 1 ? "TASK.S.1" : "TASK.S.2";
            JsonElement exported = replay == 1 ? symbol("M_K")
                    : sum(symbol("M_K"), constant(1));
            rows.add(summary("S", "S#a1", senderTask, scope, exported));
            long event = 900L + replay;
            JsonObject leaf = boundary(event, exported);
            JsonObject receiver = summary("R", "R#a1",
                    "TASK.R." + replay, scope, leaf);
            handoff(receiver, FAMILY, event, senderTask, "S#a1", leaf);
            rows.add(receiver);
        }
        return rewrite(rows);
    }

    /** The concrete value one sender arm exports, as its VM IR states it. */
    private static int senderValue(JsonElement expression) {
        JsonObject node = expression.getAsJsonObject();
        if ("BinaryExpression".equals(optionalString(node, "_type"))) {
            return senderValue(node.get("_left"))
                    + senderValue(node.get("_right"));
        }
        if ("ConSymbolExp".equals(optionalString(node, "_type"))) {
            return Integer.parseInt(optionalString(node, "_exp")
                    .substring("C_I_".length()));
        }
        // The shared symbolic base both cases build on.
        return 40;
    }

    private static Set<String> reasons(
            SymbolicPropagationClosure.Result result) {
        Set<String> found = new LinkedHashSet<>();
        for (JsonElement gap : result.gaps()) {
            found.add(optionalString(gap.getAsJsonObject(), "reason"));
        }
        return found;
    }

    private static JsonObject merge(SymbolicPropagationClosure.Result result,
                                    String family) {
        for (JsonObject summary : result.summaries()) {
            JsonObject found = firstMerge(summary, family);
            if (found.size() > 0) return found;
        }
        return new JsonObject();
    }

    private static JsonObject firstMerge(JsonElement value, String family) {
        if (value == null || !value.isJsonObject()) {
            if (value != null && value.isJsonArray()) {
                for (JsonElement child : value.getAsJsonArray()) {
                    JsonObject found = firstMerge(child, family);
                    if (found.size() > 0) return found;
                }
            }
            return new JsonObject();
        }
        JsonObject node = value.getAsJsonObject();
        if (SymbolicPropagationClosure.ITE_TYPE.equals(
                optionalString(node, "_type"))
                && family.equals(optionalString(node,
                        VmExpressionIr.FAMILY_KEY))) {
            return node;
        }
        for (Map.Entry<String, JsonElement> member : node.entrySet()) {
            JsonObject found = firstMerge(member.getValue(), family);
            if (found.size() > 0) return found;
        }
        return new JsonObject();
    }

    private static JsonObject dependency(
            SymbolicPropagationClosure.Result result, String family) {
        for (JsonElement encoded : result.caseDependencies()) {
            JsonObject row = encoded.getAsJsonObject();
            if (family.equals(optionalString(row,
                    VmExpressionIr.FAMILY_KEY))) {
                return row;
            }
        }
        return new JsonObject();
    }

    private static SymbolicPropagationClosure.Result rewrite(
            List<JsonObject> rows) {
        List<JsonObject> portable = new ArrayList<>();
        for (JsonObject row : rows) {
            row.remove(LocalCaseIdentity.FIELD);
            row.addProperty(LocalCaseIdentity.FIELD,
                    LocalCaseIdentity.compute(row));
            portable.add(SharedExpressionTable.compact(row));
        }
        return SymbolicPropagationClosure.rewriteSummaryRows(portable);
    }

    private static void handoff(JsonObject receiver, String family,
                                long attachEvent, String producerTask,
                                String producerOccurrence,
                                JsonObject wrapper) {
        JsonObject event = VmHandoffEvidence.event(PORT, attachEvent - 1,
                attachEvent, wrapper, producerTask, producerOccurrence);
        event = VmHandoffEvidence.withBoundaryFamily(event, family, EPOCH);
        event.addProperty("boundarySessionScope",
                receiver.get("boundarySessionScope").getAsString());
        JsonArray events = new JsonArray();
        events.add(event);
        receiver.add(VmHandoffEvidence.FIELD, events);
    }

    private static JsonObject summary(String region, String occurrence,
                                      String task, String scope,
                                      JsonElement condition) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
        row.addProperty("summaryId", "SUMMARY." + task + "." + scope);
        row.addProperty("relationKey", "REL." + region);
        row.addProperty("regionId", region);
        row.addProperty("sourceKey", "SOURCE." + region);
        row.addProperty("occurrenceId", occurrence);
        row.addProperty("plannedOccurrenceId",
                OccurrenceId.parse(occurrence).planned());
        row.addProperty("taskId", task);
        row.addProperty("sourceTaskId", task);
        row.addProperty("boundarySessionScope", scope);
        row.addProperty(VmExpressionIr.TOPOLOGY_EPOCH, EPOCH);
        row.addProperty("pathSetClosed", true);
        JsonArray pc = new JsonArray();
        pc.add(condition.deepCopy());
        row.add("pathCondition", pc);
        JsonArray mappings = new JsonArray();
        mappings.add(SummaryBranchMapping.concrete(
                ExactConcreteBranchObservation.attested("SITE." + region,
                        "<fixture." + region + ": void run()>", 0, 1,
                        !task.endsWith(".2")),
                SummaryBranchMapping.Policy.EXPLORE).toJson());
        row.add("branchMappings", mappings);
        row.addProperty(LocalCaseIdentity.FIELD,
                LocalCaseIdentity.compute(row));
        return row;
    }

    private static JsonObject boundary(long event, JsonElement payload) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", VmExpressionIr.CONSUMER_BOUNDARY_TYPE);
        result.addProperty(VmExpressionIr.BOUNDARY_KIND,
                VmExpressionIr.RPC_ATTACH);
        result.addProperty(VmExpressionIr.EVENT_ID, event);
        result.addProperty("_java_type", "I");
        result.add(VmExpressionIr.EXPRESSION, payload.deepCopy());
        return result;
    }

    private static JsonObject symbol(String name) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", name);
        return result;
    }

    private static JsonObject constant(int value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConSymbolExp");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", "C_I_" + value);
        return result;
    }

    private static JsonObject sum(JsonElement left, JsonElement right) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.addProperty("_java_type", "I");
        result.addProperty("_op", "+");
        result.add("_left", left.deepCopy());
        result.add("_right", right.deepCopy());
        return result;
    }

    private static String assertion(String term) {
        return term.isEmpty() ? "" : "(assert " + term + ")\n";
    }

    private static String solve(String model) throws Exception {
        Process process = new ProcessBuilder("z3", "-in")
                .redirectErrorStream(true).start();
        try (OutputStream input = process.getOutputStream()) {
            input.write((model + "(check-sat)\n").getBytes(
                    StandardCharsets.UTF_8));
        }
        ByteArrayOutputStream captured = new ByteArrayOutputStream();
        try (InputStream output = process.getInputStream()) {
            byte[] buffer = new byte[4096];
            for (int read = output.read(buffer); read >= 0;
                 read = output.read(buffer)) {
                captured.write(buffer, 0, read);
            }
        }
        process.waitFor();
        return captured.toString("UTF-8").trim();
    }

    private static boolean z3Available() {
        try {
            return new ProcessBuilder("z3", "--version").start()
                    .waitFor() == 0;
        } catch (Exception unavailable) {
            return false;
        }
    }

    private static JsonObject ledgerRow(String port, boolean declared,
                                        boolean bound, boolean fieldRead) {
        JsonObject row = new JsonObject();
        row.addProperty("portId", port);
        row.addProperty("declaredWireFlow", declared);
        row.addProperty("valueBound", bound);
        row.addProperty("consumerFieldRead", fieldRead);
        return row;
    }

    private static Set<String> subjects(
            SymbolicPropagationClosure.Result result) {
        Set<String> found = new LinkedHashSet<>();
        for (JsonElement gap : result.gaps()) {
            found.add(optionalString(gap.getAsJsonObject(), "subject"));
        }
        return found;
    }

    private static final String FAMILY_AB = "CBF.WIRE.AB";
    private static final String FAMILY_BC = "CBF.WIRE.BC";
    private static final String PORT_AB =
            "XCH.e244e592-6913-3e09-bdeb-7725d3983d4e.resp.a-to-b";
    private static final String PORT_BC =
            "XCH.da84e470-fe7e-3068-b93f-caafeef64a70.req.b-to-c";

    /** A -> B -> C over two wires, with A taking a different case per replay. */
    private static SymbolicPropagationClosure.Result chainCorpus() {
        List<JsonObject> rows = new ArrayList<>();
        for (int replay = 1; replay <= 2; replay++) {
            String scope = "replay-group:chain-" + replay;
            String senderTask = replay == 1 ? "TASK.A.1" : "TASK.A.2";
            JsonElement exported = replay == 1 ? symbol("M_K")
                    : sum(symbol("M_K"), constant(1));
            rows.add(summary("A", "A#a1", senderTask, scope, exported));

            long eventAB = 800L + replay;
            JsonObject leafAB = boundary(eventAB, exported);
            // B's own value is its own. It received A's and forwarded it,
            // which is the client's part in NN -> client -> DN: the leaf
            // reaches the walk only inside what B sent on.
            JsonObject middle = summary("B", "B#a1", "TASK.B." + replay,
                    scope, constant(7));
            attach(middle, FAMILY_AB, PORT_AB, eventAB, senderTask, "A#a1",
                    leafAB);
            rows.add(middle);

            // What B forwarded is the very leaf it received: the value never
            // becomes B's own, so C's read stays a question about A.
            long eventBC = 850L + replay;
            JsonObject leafBC = boundary(eventBC, leafAB);
            JsonObject last = summary("C", "C#a1", "TASK.C." + replay,
                    scope, leafBC);
            attach(last, FAMILY_BC, PORT_BC, eventBC, "TASK.B." + replay,
                    "B#a1", leafBC);
            rows.add(last);
        }
        return rewrite(rows);
    }

    /** Like {@link #handoff} but names its own port, and appends. */
    private static void attach(JsonObject receiver, String family,
                               String port, long attachEvent,
                               String producerTask, String producerOccurrence,
                               JsonObject wrapper) {
        JsonObject event = VmHandoffEvidence.event(port, attachEvent - 1,
                attachEvent, wrapper, producerTask, producerOccurrence);
        event = VmHandoffEvidence.withBoundaryFamily(event, family, EPOCH);
        event.addProperty("boundarySessionScope",
                receiver.get("boundarySessionScope").getAsString());
        JsonArray events = receiver.getAsJsonArray(VmHandoffEvidence.FIELD);
        if (events == null) {
            events = new JsonArray();
            receiver.add(VmHandoffEvidence.FIELD, events);
        }
        events.add(event);
    }

}

package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.BranchReplayContract;
import edu.uva.liftlab.graphchecker.concolic.BranchPredicateAlgebra;
import edu.uva.liftlab.graphchecker.concolic.BranchWitness;
import edu.uva.liftlab.graphchecker.concolic.ExactConcreteBranchObservation;
import edu.uva.liftlab.graphchecker.concolic.SharedExpressionTable;
import edu.uva.liftlab.graphchecker.concolic.SummaryBranchMapping;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.After;
import org.junit.Test;

import static java.util.Collections.singletonList;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/** Source evidence used to replay one exact region occurrence. */
public class ConcolicRegionRuntimeSourceAnchorTest {
    private static final String EXPECTED = "dn0#epoch0";
    private static final SourceRef DN0_REPLAY =
            new SourceRef("DATANODE", "dn", "dn0", 7L);
    private static final SourceRef NN0_REPLAY =
            new SourceRef("NAMENODE", "nn", "nn0", 7L);

    @After
    public void clearMessageState() {
        SymbolicMessageEnvelope.clear();
    }

    @Test
    public void inheritedSourceFillsOnlyAnAbsentReceiverRegistration() {
        assertTrue(ConcolicRegionRuntime.registeredSourceAnchorMatches(
                EXPECTED, null, DN0_REPLAY));
        assertTrue(ConcolicRegionRuntime.registeredSourceAnchorMatches(
                EXPECTED, DN0_REPLAY, NN0_REPLAY));

        assertFalse(ConcolicRegionRuntime.registeredSourceAnchorMatches(
                EXPECTED, NN0_REPLAY, DN0_REPLAY));
        assertFalse(ConcolicRegionRuntime.registeredSourceAnchorMatches(
                EXPECTED, null, NN0_REPLAY));
    }

    @Test
    public void exactOutgoingPortStillRequiresThePlannedRequest() {
        String request = "dn0#epoch0/request/heartbeat#1";
        assertFalse(ConcolicRegionRuntime
                .outgoingProducerMayDeferMissingContext(
                        true, null, null, "nn0#epoch0", request,
                        "heartbeat", "", ""));

        // An inherited caller source is not the missing service receiver's
        // identity.  The exact request address and the unique OUT edge admit
        // it provisionally; publication still requires that OUT hook.
        assertTrue(ConcolicRegionRuntime
                .outgoingProducerMayDeferMissingContext(
                        true, null, DN0_REPLAY, "nn0#epoch0", request,
                        "heartbeat", request, "heartbeat"));

        // A receiver registration remains authoritative.  Incomplete or
        // conflicting request evidence and an absent exact OUT proof remain
        // strict as well.  In particular, an OUT port cannot make an earlier
        // setup request impersonate the request selected from the trace.
        assertFalse(ConcolicRegionRuntime
                .outgoingProducerMayDeferMissingContext(
                        true, DN0_REPLAY, null, "nn0#epoch0", request,
                        "heartbeat", "", ""));
        assertFalse(ConcolicRegionRuntime
                .outgoingProducerMayDeferMissingContext(
                        true, null, NN0_REPLAY, "nn0#epoch0", request,
                        "heartbeat", "", ""));
        assertFalse(ConcolicRegionRuntime
                .outgoingProducerMayDeferMissingContext(
                        true, null, null, "nn0#epoch0", request,
                        "heartbeat", request, ""));
        assertFalse(ConcolicRegionRuntime
                .outgoingProducerMayDeferMissingContext(
                        true, null, null, "nn0#epoch0", request,
                        "heartbeat", "other/request/heartbeat#1",
                        "heartbeat"));
        assertFalse(ConcolicRegionRuntime
                .outgoingProducerMayDeferMissingContext(
                        false, null, null, "nn0#epoch0", request,
                        "heartbeat", "", ""));
    }

    @Test
    public void repeatedLoopPortIsDeliveredInMessageOrder() {
        assertTrue(SymbolicMessageEnvelope.stage("block-key", 41L,
                "producer", "producer#1",
                singletonList("consumer#1")));
        assertTrue(SymbolicMessageEnvelope.stage("block-key", 42L,
                "producer", "producer#2",
                singletonList("consumer#1")));

        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());
        assertEquals(41L,
                SymbolicMessageEnvelope.take("block-key").handle());
        assertEquals(42L,
                SymbolicMessageEnvelope.take("block-key").handle());
        assertFalse(SymbolicMessageEnvelope.take("block-key").present());
    }

    @Test
    public void messageProducerCanAddressConsumerBeforeAttachConsumesIt() {
        assertTrue(SymbolicMessageEnvelope.stage("block-key", 0L,
                "task-1", "producer#1#a3",
                singletonList("consumer#1")));
        assertTrue(SymbolicMessageEnvelope.stage("block-key", 42L,
                "task-2", "producer#2#a1",
                singletonList("consumer#1")));
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());

        assertFalse(ConcolicRegionRuntime.inboundMessageMatches(
                "block-key", "producer#2", "consumer#1"));
        assertTrue(ConcolicRegionRuntime.inboundMessageMatches(
                "block-key", "producer#1", "consumer#1"));
        assertTrue(ConcolicRegionRuntime.inboundMessageMatches(
                "block-key", "producer#1", "consumer#1"));
        assertFalse(ConcolicRegionRuntime.inboundMessageMatches(
                "block-key", "producer#1", "consumer#2"));
        assertEquals(0L, SymbolicMessageEnvelope.take("block-key").handle());
        assertTrue(ConcolicRegionRuntime.inboundMessageMatches(
                "block-key", "producer#2", "consumer#1"));
    }

    @Test
    public void producerAddressSupersedesConsumerInvocationOrdinal() {
        assertFalse(ConcolicRegionRuntime.rootInvocationAddressMatches(
                1, 1, Collections.singletonMap(
                        "data-key", "producer#1"), "consumer#1", false));
        assertTrue(SymbolicMessageEnvelope.stage("data-key", 91L,
                "task", "producer#2",
                singletonList("consumer#1")));
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());
        assertTrue(ConcolicRegionRuntime.rootInvocationAddressMatches(
                99, 1, Collections.singletonMap(
                        "data-key", "producer#2"), "consumer#1", false));
        assertFalse(ConcolicRegionRuntime.rootInvocationAddressMatches(
                1, 1, Collections.singletonMap(
                        "data-key", "producer#1"), "consumer#1", false));
        assertFalse(ConcolicRegionRuntime.rootInvocationAddressMatches(
                99, 1, Collections.singletonMap(
                        "data-key", "producer#2"), "consumer#2", false));

        assertTrue(ConcolicRegionRuntime.rootInvocationAddressMatches(
                1, 1, Collections.<String, String>emptyMap(),
                "consumer#1", false));
        assertFalse(ConcolicRegionRuntime.rootInvocationAddressMatches(
                2, 1, Collections.<String, String>emptyMap(),
                "consumer#1", false));

        // A producer selected by one exact request/OUT/consumer tuple keeps
        // the address open until a candidate actually executes that OUT.
        assertTrue(ConcolicRegionRuntime.rootInvocationAddressMatches(
                2, 1, Collections.<String, String>emptyMap(),
                "consumer#1", true));
        assertTrue(ConcolicRegionRuntime.rootInvocationAddressMatches(
                null, 1, Collections.<String, String>emptyMap(),
                "consumer#1", true));
    }

    @Test
    public void exactMessageAttributesAnUnregisteredConsumerButNotAConflict() {
        Map<String, String> producers = Collections.singletonMap(
                "data-key", "producer#2");
        assertTrue(SymbolicMessageEnvelope.stage("data-key", 91L,
                "task", "producer#2#a4",
                singletonList("consumer#1")));
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());

        boolean addressed = ConcolicRegionRuntime
                .inboundMessageAddressMatches(producers, "consumer#1");
        String attributed = ConcolicRegionRuntime
                .inboundMessageSourceEvidence(EXPECTED, null, addressed);
        assertEquals(EXPECTED, attributed);
        assertTrue(RuntimeTraceContext.sameSourceIdentity(
                EXPECTED, attributed));

        assertEquals("", ConcolicRegionRuntime
                .inboundMessageSourceEvidence(EXPECTED, NN0_REPLAY,
                        addressed));
    }

    @Test
    public void everyPlannedInputMustBeInTheCurrentMessage() {
        Map<String, String> producers = new LinkedHashMap<>();
        producers.put("block-key", "block-producer#1");
        producers.put("data-key", "data-producer#1");

        assertTrue(SymbolicMessageEnvelope.stage("block-key", 41L,
                "block-task", "block-producer#1",
                singletonList("consumer#1")));
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());
        assertFalse(ConcolicRegionRuntime.rootInvocationAddressMatches(
                99, 1, producers, "consumer#1", false));

        SymbolicMessageEnvelope.clear();
        assertTrue(SymbolicMessageEnvelope.stage("block-key", 41L,
                "block-task", "block-producer#1",
                singletonList("consumer#1")));
        assertTrue(SymbolicMessageEnvelope.stage("data-key", 42L,
                "data-task", "wrong-producer#1",
                singletonList("consumer#1")));
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());
        assertFalse(ConcolicRegionRuntime.rootInvocationAddressMatches(
                99, 1, producers, "consumer#1", false));

        SymbolicMessageEnvelope.clear();
        assertTrue(SymbolicMessageEnvelope.stage("block-key", 41L,
                "block-task", "block-producer#1",
                singletonList("consumer#1")));
        assertTrue(SymbolicMessageEnvelope.stage("data-key", 42L,
                "data-task", "data-producer#1#a2",
                singletonList("consumer#1")));
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());
        assertTrue(ConcolicRegionRuntime.rootInvocationAddressMatches(
                99, 1, producers, "consumer#1", false));
    }

    @Test
    public void replayChecksExactSwitchSuccessorBeforeFlippedBranch() {
        JsonObject selector = variable("I_selector");
        JsonObject switchPredicate = binary(selector, "==", integer(7));
        JsonObject targetPredicate = binary(variable("I_value"), "==",
                integer(1));
        JsonArray path = new JsonArray();
        path.add(switchPredicate);
        path.add(targetPredicate);

        JsonArray mappings = new JsonArray();
        mappings.add(SummaryBranchMapping.concrete(
                ExactConcreteBranchObservation.attestedSwitch("SITE.S",
                        "switchMethod", 3, 1,
                        ExactConcreteBranchObservation.LOOKUP_SWITCH,
                        Arrays.asList(7, 9), 0),
                SummaryBranchMapping.Policy.PATH_ASSUMPTION).toJson());
        mappings.add(SummaryBranchMapping.witnessed(
                BranchWitness.pcPredicateImmutable("SITE.S", "switchMethod", 3, 1,
                        1, switchPredicate, 0), 0,
                SummaryBranchMapping.Policy.PATH_ASSUMPTION).toJson());
        JsonObject metadata = new JsonObject();
        metadata.addProperty("predicateNormalization",
                BranchWitness.IDENTITY_NORMALIZATION);
        mappings.add(SummaryBranchMapping.witnessed(
                BranchWitness.vmPcImmutable("SITE.T", "targetMethod", 5, 1, true,
                        targetPredicate, 1, metadata), 1,
                SummaryBranchMapping.Policy.EXPLORE).toJson());
        JsonObject summary = new JsonObject();
        summary.add("pathCondition", path);
        summary.add("branchMappings", mappings);

        BranchReplayContract contract = BranchReplayContract.fromSummary(
                summary, "SITE.T", 1);
        assertEquals(1, contract.toJson()
                .getAsJsonArray("runtimePrefix").size());
        BranchReplayContract.RuntimeSchedule schedule =
                BranchReplayContract.runtimeScheduleFromJson(
                        contract.toJson());
        BranchReplayContract.ReplayProgress replay =
                new BranchReplayContract.ReplayProgress(schedule);
        assertFalse(replay.observeSwitch("SITE.S", 1,
                ExactConcreteBranchObservation.LOOKUP_SWITCH,
                Arrays.asList(7, 9), 0));
        assertTrue(replay.observeBinary("SITE.T", 1, false));
        assertTrue(replay.complete());

        BranchReplayContract.ReplayProgress mismatch =
                new BranchReplayContract.ReplayProgress(schedule);
        assertFalse(mismatch.observeSwitch("SITE.S", 1,
                ExactConcreteBranchObservation.LOOKUP_SWITCH,
                Arrays.asList(7, 9), 1));
        assertTrue(mismatch.failed());
    }

    @Test
    public void boundedLoopReplayFollowsEquivalentSymbolicElementSupport() {
        String method = "<Owner: void iterate()>";
        String loopSite = method + "#u15";
        JsonObject entry = binary(variable("I_entry"), "==", integer(1));
        JsonObject first = binary(variable("J_element"), "<",
                integer(100));
        String controlSite = method + "#u7";
        JsonObject exited = binary(variable("I_has_next"), "==",
                integer(0));
        JsonObject second = binary(variable("J_element"), "<",
                integer(200));
        JsonObject source = binary(variable("J_element"), "<",
                integer(300));
        JsonArray path = new JsonArray();
        path.add(entry);
        path.add(first);
        path.add(exited);
        path.add(second);
        path.add(source);

        JsonObject metadata = new JsonObject();
        metadata.addProperty("predicateNormalization",
                BranchWitness.IDENTITY_NORMALIZATION);
        JsonArray mappings = new JsonArray();
        mappings.add(SummaryBranchMapping.witnessed(
                BranchWitness.vmPcImmutable("SITE.ENTRY", "entry", 1, 1, true,
                        entry, 0, metadata), 0,
                SummaryBranchMapping.Policy.PATH_ASSUMPTION).toJson());
        mappings.add(SummaryBranchMapping.witnessed(
                BranchWitness.vmPcImmutable(loopSite, method, 15, 1, true,
                        first, 1, metadata), 1,
                SummaryBranchMapping.Policy.EXPLORE).toJson());
        mappings.add(SummaryBranchMapping.witnessed(
                BranchWitness.vmPcImmutable(controlSite, method, 7, 1, false,
                        exited, 2, metadata), 2,
                SummaryBranchMapping.Policy.EXPLORE).toJson());
        mappings.add(SummaryBranchMapping.witnessed(
                BranchWitness.vmPcImmutable(loopSite, method, 15, 2, true,
                        second, 3, metadata), 3,
                SummaryBranchMapping.Policy.EXPLORE).toJson());
        mappings.add(SummaryBranchMapping.witnessed(
                BranchWitness.vmPcImmutable(loopSite, method, 15, 3, true,
                        source, 4, metadata), 4,
                SummaryBranchMapping.Policy.EXPLORE).toJson());
        JsonObject summary = new JsonObject();
        summary.add("pathCondition", path);
        summary.add("branchMappings", mappings);

        JsonObject loop = new JsonObject();
        loop.addProperty("enclosingMethod", method);
        loop.addProperty(LoopBoundPolicy.LOOP_SITE_ID, controlSite);
        loop.addProperty(LoopBoundPolicy.RUNTIME_LOOP_ID,
                method + "#loop:u7");
        loop.addProperty(LoopBoundPolicy.LOOP_LATCH_UNIT_INDEX, 17);
        JsonArray controls = new JsonArray();
        controls.add(controlSite);
        loop.add(LoopBoundPolicy.LOOP_CONTROL_SITE_IDS, controls);
        JsonArray memberBranches = new JsonArray();
        memberBranches.add(controlSite);
        memberBranches.add(loopSite);
        loop.add(LoopBoundPolicy.LOOP_INNERMOST_BRANCH_SITE_IDS,
                memberBranches);
        JsonObject exit = new JsonObject();
        exit.addProperty("siteId", controlSite);
        exit.addProperty("decisionToken",
                ExactConcreteBranchObservation.binaryDecisionToken(false));
        JsonArray exits = new JsonArray();
        exits.add(exit);
        loop.add(LoopBoundPolicy.LOOP_EXIT_DECISIONS, exits);
        JsonArray retainedLoops = new JsonArray();
        retainedLoops.add(loop);

        BranchReplayContract contract = BranchReplayContract.fromSummary(
                summary, loopSite, 3);
        JsonObject envelope = new JsonObject();
        envelope.add("replayContract", contract.toJson());
        JsonObject compact = SharedExpressionTable.compact(envelope);
        BranchReplayContract.RuntimeSchedule schedule =
                BranchReplayContract.runtimeScheduleFromJson(
                        compact.getAsJsonObject("replayContract"),
                        retainedLoops);
        BranchReplayContract.ReplayProgress replay =
                new BranchReplayContract.ReplayProgress(schedule);
        assertFalse(replay.observeBinary("SITE.ENTRY", 1, true));
        assertFalse(replay.observeBinary(loopSite, 1, true,
                BranchPredicateAlgebra.symbolicSupportDigest(first)));
        assertFalse(replay.observeBinary(controlSite, 1, false,
                BranchPredicateAlgebra.symbolicSupportDigest(exited)));

        // In the second dynamic invocation, the target element arrives before
        // its seed sibling and sees a different concrete clock. Its propagated
        // symbolic leaf still identifies it.
        JsonObject movedSource = binary(variable("J_element"), ">=",
                integer(999));
        assertTrue(replay.observeBinary(loopSite, 1, false,
                BranchPredicateAlgebra.symbolicSupportDigest(movedSource)));
        assertTrue(replay.complete());

        BranchReplayContract.ReplayProgress missingEntry =
                new BranchReplayContract.ReplayProgress(schedule);
        assertFalse(missingEntry.observeBinary(loopSite, 1, true,
                BranchPredicateAlgebra.symbolicSupportDigest(first)));
        assertTrue(missingEntry.failed());

        BranchReplayContract.ReplayProgress wrongInvocation =
                new BranchReplayContract.ReplayProgress(schedule);
        assertFalse(wrongInvocation.observeBinary("SITE.ENTRY", 1, true));
        assertFalse(wrongInvocation.observeBinary(loopSite, 1, false,
                BranchPredicateAlgebra.symbolicSupportDigest(movedSource)));
        assertFalse(wrongInvocation.complete());

        // A source at the first seed iteration may move behind an equivalent
        // sibling. The wrong sibling decision is not the requested semantic
        // event; the later equal-support decision is.
        BranchReplayContract firstElement = BranchReplayContract.fromSummary(
                summary, loopSite, 1);
        BranchReplayContract.ReplayProgress repeatedSupport =
                new BranchReplayContract.ReplayProgress(
                        BranchReplayContract.runtimeScheduleFromJson(
                                firstElement.toJson(), retainedLoops));
        assertFalse(repeatedSupport.observeBinary("SITE.ENTRY", 1, true));
        assertFalse(repeatedSupport.observeBinary(loopSite, 1, true,
                BranchPredicateAlgebra.symbolicSupportDigest(first)));
        assertTrue(repeatedSupport.observeBinary(loopSite, 2, false,
                BranchPredicateAlgebra.symbolicSupportDigest(movedSource)));
        assertTrue(repeatedSupport.complete());

        BranchReplayContract.ReplayProgress exact =
                new BranchReplayContract.ReplayProgress(
                        BranchReplayContract.runtimeScheduleFromJson(
                                contract.toJson()));
        assertFalse(exact.observeBinary("SITE.ENTRY", 1, true));
        assertFalse(exact.observeBinary(loopSite, 1, false,
                BranchPredicateAlgebra.symbolicSupportDigest(movedSource)));
        assertTrue(exact.failed());
    }

    private static JsonObject variable(String name) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", name);
        return result;
    }

    private static JsonObject integer(int value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConstExpr");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", "Y_I_" + value);
        return result;
    }

    private static JsonObject binary(JsonObject left, String operator,
                                     JsonObject right) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.addProperty("_java_type", "Z");
        result.addProperty("_op", operator);
        result.add("_left", left);
        result.add("_right", right);
        return result;
    }
}

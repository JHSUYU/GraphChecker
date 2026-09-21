package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import org.junit.Assert;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The once-only-root rule and the message frame have one answer for what the
 * unit of a message is.
 *
 * <p>A region rooted at a loop INSIDE a declared port's frame method leaves
 * every leaf the frame builds outside that loop with no activation at all.
 * On hdfs-11741 that leaf is the {@code currentKey} of an {@code
 * ExportedBlockKeys}, converted at {@code PBHelper} line 262 before the
 * {@code allKeys} loop: it exported under a degraded role occurrence, which
 * the VM can only hand a concrete typed constant, so its {@code ExportRow}
 * carried no expression, {@code Arms.arm} refused the arm, and {@code
 * ComposedFamilies.eligibleSessions} emptied the whole six-leaf message --
 * the four good leaves beside it included.  Measured over campaign #8: every
 * one of 5,352 exports published under a live region carried an expression,
 * and every one of 55,397 published under a degraded role carried none.</p>
 *
 * <p>The rule reads the frame the port already declares, so it separates
 * the two shapes by the loop's OWNER: a loop in the frame method walks one
 * message's leaves, a loop anywhere else does not.</p>
 */
public class ServiceLoopIsNotAMessageFrameTest {

    // The encode side: PBHelper.convert(ExportedBlockKeys) converts
    // currentKey before its allKeys loop and each allKeys element inside it.
    private static final String ENCODE_FRAME =
            "<org.apache.hadoop.hdfs.protocolPB.PBHelper: "
                    + "HdfsServerProtos$ExportedBlockKeysProto "
                    + "convert(ExportedBlockKeys)>";
    private static final String ENCODE_LEAF =
            "<org.apache.hadoop.hdfs.protocolPB.PBHelper: "
                    + "HdfsServerProtos$BlockKeyProto convert(BlockKey)>";

    // The decode side: the frame calls convertBlockKeys, whose own loop
    // converts each element.  The loop is BELOW the frame, not in it.
    private static final String DECODE_FRAME =
            "<org.apache.hadoop.hdfs.protocolPB.PBHelper: ExportedBlockKeys "
                    + "convert(HdfsServerProtos$ExportedBlockKeysProto)>";
    private static final String DECODE_WALK =
            "<org.apache.hadoop.hdfs.protocolPB.PBHelper: BlockKey[] "
                    + "convertBlockKeys(java.util.List)>";
    private static final String DECODE_LEAF =
            "<org.apache.hadoop.hdfs.protocolPB.PBHelper: BlockKey "
                    + "convert(HdfsServerProtos$BlockKeyProto)>";

    private static final String REGION = "REGION.frame-vs-loop";

    // ------------------------------------------------------------------
    // The ruling
    // ------------------------------------------------------------------

    /**
     * A loop in the port's own frame method walks ONE message's leaves, so
     * no iteration of it is a wire value and the region stays at the frame.
     */
    @Test
    public void loopInsideThePortsFrameIsNotAServiceLoop() {
        Assert.assertNull("a region that owns a declared port's OUT site is"
                        + " rooted at that port's frame method, not at a loop"
                        + " inside it",
                rootLoopOf(encodeRegion(ENCODE_FRAME, LoopBoundPolicy
                        .LOOP_FIXED_COUNT_INDEXED)));
    }

    /**
     * The red line: a loop the frame CALLS is not a loop inside the frame.
     * This is hdfs-11741's IN region, rooted at {@code convertBlockKeys}'s
     * own loop, and it keeps that rooting.
     */
    @Test
    public void loopBelowTheFrameKeepsItsRooting() {
        Map<String, Object> rooted = rootLoopOf(decodeRegion());
        Assert.assertNotNull("the frame method is not this loop's owner, so"
                + " the port says what it always said", rooted);
        Assert.assertEquals(DECODE_WALK,
                rooted.get(LoopBoundPolicy.ROOT_LOOP_METHOD));
    }

    /**
     * A port that names no frame method is addressed within its RPC message
     * and says nothing new: the rule before this one still decides it.
     */
    @Test
    public void portWithoutAFrameMethodIsUnchanged() {
        Assert.assertNotNull("a port that declares no frame leaves the"
                        + " once-only-root rule exactly as it was",
                rootLoopOf(encodeRegion("", LoopBoundPolicy
                        .LOOP_FIXED_COUNT_INDEXED)));
    }

    /**
     * A loop that decides its own continuation is a service loop wherever it
     * stands: the frame bounds the indexed arm, never this one.
     */
    @Test
    public void conditionBoundedLoopIsAServiceLoopInsideAFrameToo() {
        Assert.assertNotNull("a CONDITION_BOUNDED loop is the shape the"
                        + " once-only-root rule is about",
                rootLoopOf(encodeRegion(ENCODE_FRAME,
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED)));
    }

    // ------------------------------------------------------------------
    // Two regions, built to the shape of the two PBHelper conversions
    // ------------------------------------------------------------------

    /** One built region and the branch order its loop was seen in. */
    private static final class Case {
        private final StaticProgram program;
        private final List<Map<String, Object>> branchObservations;

        Case(StaticProgram program,
             List<Map<String, Object>> branchObservations) {
            this.program = program;
            this.branchObservations = branchObservations;
        }
    }

    private static Map<String, Object> rootLoopOf(Case built) {
        return built.program.loopBodyRoot(
                built.program.skeletons.get(REGION),
                built.program.regionActivations(REGION),
                built.branchObservations);
    }

    /**
     * Root and frame {@code convert(ExportedBlockKeys)}, anchor {@code
     * convert(BlockKey)}, one retained loop over {@code allKeys} owned by
     * the frame itself and calling the anchor from inside it.
     */
    private static Case encodeRegion(String frameMethod,
                                     String classification) {
        return program(ENCODE_FRAME, ENCODE_LEAF,
                Arrays.asList(ENCODE_FRAME, ENCODE_LEAF),
                loop(ENCODE_FRAME, 14, 19, classification),
                port(ENCODE_LEAF, frameMethod),
                Collections.singletonList(
                        callEdge(ENCODE_FRAME, 16, ENCODE_LEAF)));
    }

    /**
     * Root and frame {@code convert(ExportedBlockKeysProto)}, anchor {@code
     * convert(BlockKeyProto)}, and the retained loop one method BELOW the
     * frame, in {@code convertBlockKeys}.
     */
    private static Case decodeRegion() {
        return program(DECODE_FRAME, DECODE_LEAF,
                Arrays.asList(DECODE_FRAME, DECODE_WALK, DECODE_LEAF),
                loop(DECODE_WALK, 5, 9,
                        LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED),
                port(DECODE_LEAF, DECODE_FRAME),
                Arrays.asList(callEdge(DECODE_FRAME, 3, DECODE_WALK),
                        callEdge(DECODE_WALK, 7, DECODE_LEAF)));
    }

    private static Case program(String rootMethod,
                                String anchorMethod,
                                List<String> methods,
                                Map<String, Object> loop,
                                Map<String, Object> port,
                                List<Map<String, Object>> graph) {
        StaticProgram program = new StaticProgram();
        Map<String, Object> region = new LinkedHashMap<>();
        region.put("schemaVersion",
                RuntimeSelectedRegionFinalizer.REGION_SCHEMA_VERSION);
        region.put("kind", RuntimeSelectedRegionFinalizer.SKELETON_KIND);
        region.put("regionId", REGION);
        region.put("rootMethod", rootMethod);
        region.put("anchorMethod", anchorMethod);
        region.put("selection", "COMMUNICATION_CONTEXT");
        region.put("methods", methods);
        region.put("retainedLoops", Collections.singletonList(loop));
        region.put("communicationPorts", Collections.singletonList(port));
        program.skeletons.put(REGION, StaticProgram.regionRows(
                Collections.singletonList(region),
                RuntimeSelectedRegionFinalizer.SKELETON_KIND,
                "test").get(0));
        program.refinedGraph = graph;
        program.activations.put("ACT.1", activation());
        return new Case(program, branchObservations(String.valueOf(
                loop.get(LoopBoundPolicy.LOOP_SITE_ID))));
    }

    /** One retained loop, with its header, its guard and its latch. */
    private static Map<String, Object> loop(String owner, int header,
                                            int latch,
                                            String classification) {
        Map<String, Object> loop = new LinkedHashMap<>();
        loop.put("schemaVersion", 4);
        loop.put("kind", "RETAINED_LOOP");
        loop.put("enclosingMethod", owner);
        loop.put(LoopBoundPolicy.LOOP_CLASSIFICATION, classification);
        loop.put(LoopBoundPolicy.RUNTIME_LOOP_ID,
                owner + "#loop:u" + header);
        loop.put(LoopBoundPolicy.LOOP_SITE_ID, owner + "#u" + header);
        loop.put(LoopBoundPolicy.LOOP_CONTROL_SITE_IDS,
                Collections.singletonList(owner + "#u" + header));
        loop.put(LoopBoundPolicy.LOOP_LATCH_UNIT_INDEX, latch);
        return loop;
    }

    /** One declared port, defined by the leaf converter. */
    private static Map<String, Object> port(String definitionMethod,
                                            String frameMethod) {
        Map<String, Object> port = new LinkedHashMap<>();
        port.put(CommunicationCatalogContract.PORT_ID,
                "XCH.0.resp.block-key-id");
        port.put(CommunicationCatalogContract.PORT_NAME, "block-key-id");
        port.put(CommunicationCatalogContract.PORT_JAVA_TYPE, "int");
        port.put(CommunicationCatalogContract.PORT_DIRECTION,
                CommunicationCatalogContract.DIRECTION_RESPONSE);
        port.put(CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                definitionMethod);
        port.put(CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX, 9);
        if (!frameMethod.isEmpty()) {
            port.put(CommunicationCatalogContract.PORT_FRAME_METHOD,
                    frameMethod);
        }
        return port;
    }

    private static Map<String, Object> callEdge(String method, int unitIndex,
                                                String invoke) {
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("method", method);
        edge.put("unitIndex", unitIndex);
        edge.put("invoke", invoke);
        edge.put("transferKind", "CALL_ARGUMENT");
        return edge;
    }

    /** One activation, on the call the loop was seen to iterate inside. */
    private static Map<String, Object> activation() {
        Map<String, Object> activation = new LinkedHashMap<>();
        activation.put("regionId", REGION);
        activation.put("activationId", "ACT.1");
        activation.put("callIds", Collections.singletonList(7L));
        return activation;
    }

    /** The loop deciding its own continuation twice inside one call. */
    private static List<Map<String, Object>> branchObservations(
            String controlSite) {
        List<Map<String, Object>> seen = new ArrayList<>();
        for (int repeat = 0; repeat < 2; repeat++) {
            Map<String, Object> observation = new LinkedHashMap<>();
            observation.put("siteId", controlSite);
            observation.put("callId", 7L);
            seen.add(observation);
        }
        return seen;
    }
}

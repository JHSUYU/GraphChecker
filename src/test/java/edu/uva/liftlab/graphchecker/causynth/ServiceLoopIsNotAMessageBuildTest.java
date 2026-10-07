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
 * The once-only-root rule's unit of work is never the build of one message.
 *
 * <p>A region rooted at a loop that builds the repeated field of ONE message
 * leaves every leaf built outside that loop with no activation at all.  On
 * hdfs-11741 that leaf is the {@code currentKey} of an {@code
 * ExportedBlockKeys}, converted at {@code PBHelper} line 262 before the
 * {@code allKeys} loop: built under a degraded role occurrence, its value
 * carried no expression, {@code Arms.arm} refused the arm, and {@code
 * ComposedFamilies.eligibleSessions} emptied the whole six-leaf message --
 * the four good leaves beside it included.  Measured over campaign #8: every
 * one of 5,352 exports published under a live region carried an expression,
 * and every one of 55,397 published under a degraded role carried none.</p>
 *
 * <p>A message field's producer capture (the builder's setter call) is no
 * unit of a loop's work, since the door exports the message whole: a loop
 * that calls it never qualifies by it.  Its consumer capture (the getter's
 * attach) still is: a loop decoding one element per turn is the decode's
 * service loop.</p>
 */
public class ServiceLoopIsNotAMessageBuildTest {

    // The encode side: PBHelper.convert(ExportedBlockKeys) converts
    // currentKey before its allKeys loop and each allKeys element inside it.
    private static final String ENCODE_ROOT =
            "<org.apache.hadoop.hdfs.protocolPB.PBHelper: "
                    + "HdfsServerProtos$ExportedBlockKeysProto "
                    + "convert(ExportedBlockKeys)>";
    private static final String ENCODE_LEAF =
            "<org.apache.hadoop.hdfs.protocolPB.PBHelper: "
                    + "HdfsServerProtos$BlockKeyProto convert(BlockKey)>";

    // The decode side: the root calls convertBlockKeys, whose own loop
    // converts each element.
    private static final String DECODE_ROOT =
            "<org.apache.hadoop.hdfs.protocolPB.PBHelper: ExportedBlockKeys "
                    + "convert(HdfsServerProtos$ExportedBlockKeysProto)>";
    private static final String DECODE_WALK =
            "<org.apache.hadoop.hdfs.protocolPB.PBHelper: BlockKey[] "
                    + "convertBlockKeys(java.util.List)>";
    private static final String DECODE_LEAF =
            "<org.apache.hadoop.hdfs.protocolPB.PBHelper: BlockKey "
                    + "convert(HdfsServerProtos$BlockKeyProto)>";

    private static final String REGION = "REGION.build-vs-loop";

    // ------------------------------------------------------------------
    // The ruling
    // ------------------------------------------------------------------

    /** Each shape, and the loop its region is rooted at (null: its root). */
    @Test
    public void onlyALoopOutsideTheFrameOrDecidingItselfIsAServiceLoop() {
        Object[][] rows = {
                // A loop building one message's repeated field: no iteration
                // of it is a wire value (the door exports the message
                // whole), so the region stays at its root.
                {"a loop building a message field",
                        encodeRegion(CODEC_FIELD,
                                LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED),
                        null},
                // The decode attaches one element per turn: hdfs-11741's IN
                // region, rooted at convertBlockKeys's own loop, keeps that
                // rooting.
                {"a loop decoding a message field", decodeRegion(),
                        DECODE_WALK},
                // SOLR-18406: a region entry folded into the root beside the
                // loop (checkpoint's onCommit, beside decRef's loop over
                // files) would be in no occurrence: the root stands.
                {"a loop that a folded entry is beside",
                        folded(decodeRegion(), DECODE_ROOT), null},
                {"a loop that a folded entry is inside",
                        folded(decodeRegion(), DECODE_WALK), DECODE_WALK},
                // A declared row's capture is exported where it runs: one
                // turn, one export.
                {"a loop capturing a declared row",
                        encodeRegion("",
                                LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED),
                        ENCODE_ROOT},
                // A loop that decides its own continuation is a service loop
                // wherever it stands: the rule bounds the indexed arm only.
                {"a CONDITION_BOUNDED loop building a message field",
                        encodeRegion(CODEC_FIELD,
                                LoopBoundPolicy.LOOP_CONDITION_BOUNDED),
                        ENCODE_ROOT},
                // The root's own loop, when its first call into the region
                // is in it: a thread's set-up before it is not work.
                {"a root that only sets up before its loop",
                        rootLoop(SET_UP), ENCODE_ROOT},
                // hdfs-11741's addKeys runs removeExpiredKeys, then its
                // copy loop: one unit of work, rooted at its entry.
                {"a root that works before its loop", rootLoop(ENCODE_LEAF),
                        null},
                // hdfs-adhoc-41: the demanded call is on the path leaving
                // the loop (INodesInPath.getExistingINodes returns it from
                // inside the loop), so no iteration frame holds it and the
                // root stands, however often the loop turned.
                {"a decoding loop whose call leaves the loop",
                        unplaceable(decodeRegion()), null},
                {"a root whose in-loop call leaves the loop",
                        unplaceable(rootLoop(SET_UP)), null}};
        for (Object[] row : rows) {
            Case built = (Case) row[1];
            Map<String, Object> rooted = rootLoopOf(built);
            Assert.assertEquals((String) row[0], row[2], rooted == null
                    ? null : rooted.get(LoopBoundPolicy.ROOT_LOOP_METHOD));
            // Where the loop turned and holds the call but no frame can
            // open, the plan says so by name; nowhere else.
            boolean stated = false;
            for (Map<String, Object> gap : built.program.planGaps) {
                stated |= String.valueOf(gap.get("subject"))
                        .startsWith("LOOP_BODY_UNPLACEABLE:");
            }
            Assert.assertEquals((String) row[0],
                    ((String) row[0]).endsWith("leaves the loop"), stated);
        }
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
     * Root {@code convert(ExportedBlockKeys)}, anchor {@code
     * convert(BlockKey)}, one retained loop over {@code allKeys} in the root
     * calling the anchor, whose capture of {@code codecField} ("" for a
     * declared row) is an export.
     */
    private static Case encodeRegion(String codecField,
                                     String classification) {
        return program(ENCODE_ROOT, ENCODE_LEAF,
                Arrays.asList(ENCODE_ROOT, ENCODE_LEAF),
                loop(ENCODE_ROOT, 14, 19, classification, 16),
                port(ENCODE_LEAF, "OUT", codecField),
                Collections.singletonList(
                        callEdge(ENCODE_ROOT, 16, ENCODE_LEAF)));
    }

    /**
     * Root {@code convert(ExportedBlockKeysProto)}, anchor {@code
     * convert(BlockKeyProto)}, and the retained loop one method below the
     * root, in {@code convertBlockKeys}, calling the anchor, whose getter
     * attaches a message field.
     */
    private static Case decodeRegion() {
        return program(DECODE_ROOT, DECODE_LEAF,
                Arrays.asList(DECODE_ROOT, DECODE_WALK, DECODE_LEAF),
                loop(DECODE_WALK, 5, 9,
                        LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED, 7),
                port(DECODE_LEAF, "IN", CODEC_FIELD),
                Arrays.asList(callEdge(DECODE_ROOT, 3, DECODE_WALK),
                        callEdge(DECODE_WALK, 7, DECODE_LEAF)));
    }

    /** {@code built}, with one region entry folded into its activation
     *  under {@code caller}. */
    private static Case folded(Case built, String caller) {
        for (Map<String, Object> activation
                : built.program.regionActivations(REGION)) {
            activation.put(RuntimeSelectedRegionFinalizer.FOLDED_ENTRY_CALLERS,
                    Collections.singletonList(DECODE_WALK.equals(caller)
                            ? Arrays.asList(DECODE_WALK, DECODE_ROOT)
                            : Collections.singletonList(DECODE_ROOT)));
        }
        return built;
    }

    private static final String SET_UP =
            "<java.lang.Thread: void setName(java.lang.String)>";

    /**
     * Root and anchor {@code convert(ExportedBlockKeys)}: a call of {@code
     * first} before its own CONDITION_BOUNDED loop, and one of the leaf in
     * it.
     */
    private static Case rootLoop(String first) {
        return program(ENCODE_ROOT, ENCODE_ROOT,
                Arrays.asList(ENCODE_ROOT, ENCODE_LEAF),
                loop(ENCODE_ROOT, 14, 19,
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 17),
                port(ENCODE_LEAF, "OUT", ""),
                Arrays.asList(callEdge(ENCODE_ROOT, 3, first),
                        callEdge(ENCODE_ROOT, 17, ENCODE_LEAF)));
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
        program.graph = graph;
        program.activations.put("ACT.1", activation());
        return new Case(program, branchObservations(String.valueOf(
                loop.get(LoopBoundPolicy.LOOP_SITE_ID))));
    }

    /** {@code built}, its loop stating no call an iteration frame can
     *  open at. */
    private static Case unplaceable(Case built) {
        for (Map<String, Object> loop : built.program.skeletons.get(REGION)
                .retainedLoops) {
            loop.put(LoopBoundPolicy.BODY_ENTRY_CALL_UNITS,
                    Collections.emptyList());
        }
        return built;
    }

    /** One retained loop, with its header, its guard, its latch and the
     *  calls an iteration frame can open at. */
    private static Map<String, Object> loop(String owner, int header,
                                            int latch,
                                            String classification,
                                            Integer... entryCalls) {
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
        loop.put(LoopBoundPolicy.BODY_ENTRY_CALL_UNITS,
                Arrays.asList(entryCalls));
        return loop;
    }

    /** The message field a block key's id is carried in. */
    private static final String CODEC_FIELD =
            "<HdfsServerProtos$BlockKeyProto: int keyId_>";

    /** One port's capture on {@code side} in the leaf converter: a message
     *  field's ({@code codecField}) or, with "", a declared row's. */
    private static Map<String, Object> port(String definitionMethod,
                                            String side, String codecField) {
        Map<String, Object> port = new LinkedHashMap<>();
        port.put(CommunicationCatalogContract.PORT_ID,
                "XCH.0.wire.block-key-id");
        port.put(RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, side);
        port.put(CommunicationCatalogContract.PORT_NAME, "block-key-id");
        port.put(CommunicationCatalogContract.PORT_JAVA_TYPE, "int");
        port.put(CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                definitionMethod);
        port.put(CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX, 9);
        if (!codecField.isEmpty()) {
            port.put(CommunicationCatalogContract.PORT_CODEC_FIELD,
                    codecField);
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

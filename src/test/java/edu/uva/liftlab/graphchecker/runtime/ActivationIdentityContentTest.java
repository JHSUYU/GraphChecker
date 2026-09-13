package edu.uva.liftlab.graphchecker.runtime;

import org.junit.Test;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.UUID;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

/**
 * A published activation name says which activation of which region on which
 * source this row plans.  Two independent recordings of one workload observe
 * that same activation, so they have to publish the same name for it.
 */
public class ActivationIdentityContentTest {
    private static final String OCCURRENCE =
            "hdfs-17899/target-dn#epoch0/region/REGION.53092d3e#1";
    private static final String METHOD = "<example.Keys: byte[] retrieve(int)>";
    private static final SourceRef SOURCE = new SourceRef(
            "HDFS_DATANODE", "DATANODE", "hdfs-17899/target-dn", 0L);

    /**
     * The same activation, aggregated out of two different recordings of one
     * workload, is published under one name.
     *
     * <p>The two roots below differ in every value a recording assigns and
     * agree on every value the workload decides: the recording JVM's thread
     * id, the recorder's global event counter behind {@code callId} and
     * {@code seq}, the trace-context lane and span tickets and the receiver's
     * object id all differ; the test, the source, the root method, the
     * receiver class and the causal request are the same.  That is exactly
     * the difference between two recordings of one obligation.</p>
     */
    @Test
    public void twoRecordingsPublishOneActivationName() {
        RuntimeRegionPlanner.MethodEvent first = root(11L, 4L, 13703L,
                452L, 458L, 313);
        RuntimeRegionPlanner.MethodEvent second = root(97L, 26L, 21847L,
                456L, 462L, 300);

        assertNotEquals("the recorded correlation key addresses one frame of "
                        + "one recording and is expected to differ",
                RuntimeRegionPlanner.recordedActivationKey(first),
                RuntimeRegionPlanner.recordedActivationKey(second));

        String firstName = publishedName(first);
        String secondName = publishedName(second);
        assertEquals("two recordings of one activation must publish one name",
                firstName, secondName);
    }

    private static String publishedName(
            RuntimeRegionPlanner.MethodEvent root) {
        return RuntimeRegionPlanner.activationId(OCCURRENCE,
                selector(root, 1));
    }

    private static Map<String, Object> selector(
            RuntimeRegionPlanner.MethodEvent root, int invocationOrdinal) {
        return RuntimeRegionPlanner.rootSelector(root, SOURCE,
                root.requestKey, root.requestApi, invocationOrdinal);
    }

    /** One recording's view of the same activation. */
    private static RuntimeRegionPlanner.MethodEvent root(
            long seq, long tid, long callId, long laneId, long spanId,
            int objectId) {
        return new RuntimeRegionPlanner.MethodEvent(seq,
                "org.apache.hadoop.hdfs.TestBlockTokenBug3", "DataXceiver",
                tid, METHOD, objectId,
                "org.apache.hadoop.hdfs.security.token.block"
                        + ".BlockTokenSecretManager",
                callId, callId - 1L, 7L, laneId, spanId, spanId - 1L, 0L,
                SOURCE, true,
                "hdfs-17899/source-dn#epoch0/request/replicate-block#1",
                "replicate-block");
    }
}

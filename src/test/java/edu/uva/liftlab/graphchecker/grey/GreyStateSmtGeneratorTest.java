package edu.uva.liftlab.graphchecker.grey;

import org.junit.Test;

import java.util.Arrays;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class GreyStateSmtGeneratorTest {
    @Test
    public void encodesNoRepairAndBuggyCacheReuse() {
        GreyStateAnalysisResult result = new GreyStateAnalysisResult();
        result.addEvent(event("VALIDATE_MAP_LOOKUP"));
        result.addEvent(event("MAP_REMOVE"));
        result.addEvent(event("SEND_METADATA"));
        result.addEvent(event("RECEIVE_METADATA"));
        result.addEvent(event("CACHE_REUSE_WITHOUT_EXPIRY_CHECK"));
        result.addEvent(event("RECOVERY_NO_REPAIR"));

        String smt = new GreyStateSmtGenerator().generate(spec(), result);

        assertTrue(smt.contains("stale cached DEK is possible"));
        assertTrue(smt.contains("noEffectiveRecovery R"));
        assertTrue(smt.contains("(assert (not (hasKey witnessRound witnessKey)))"));
    }

    @Test
    public void encodesExpiryRefreshAsAntiStaleConstraint() {
        GreyStateAnalysisResult result = new GreyStateAnalysisResult();
        result.addEvent(event("VALIDATE_MAP_LOOKUP"));
        result.addEvent(event("MAP_REMOVE"));
        result.addEvent(event("SEND_METADATA"));
        result.addEvent(event("RECEIVE_METADATA"));
        result.addEvent(event("CACHE_REFRESH_ON_EXPIRY"));
        result.addEvent(event("RECOVERY_CLEAR_OR_RETRY"));

        String smt = new GreyStateSmtGenerator().generate(spec(), result);

        assertTrue(smt.contains("Relevant cache summary includes expiry refresh"));
        assertTrue(smt.contains("(assert (not (noEffectiveRecovery 0)))"));
        assertFalse(smt.contains("stale cached DEK is possible"));
    }

    @Test
    public void prefersBalancerCacheSummaryOverGlobalClientRefresh() {
        GreyStateAnalysisResult result = new GreyStateAnalysisResult();
        result.addEvent(event("VALIDATE_MAP_LOOKUP"));
        result.addEvent(event("MAP_REMOVE"));
        result.addEvent(event("SEND_METADATA"));
        result.addEvent(event("RECEIVE_METADATA"));
        result.addEvent(event("RECOVERY_NO_REPAIR"));
        result.addEvent(event("CACHE_REUSE_WITHOUT_EXPIRY_CHECK",
                "<org.apache.hadoop.hdfs.server.balancer.KeyManager: org.apache.hadoop.hdfs.security.token.block.DataEncryptionKey newDataEncryptionKey()>"));
        result.addEvent(event("CACHE_REFRESH_ON_EXPIRY",
                "<org.apache.hadoop.hdfs.DFSClient: org.apache.hadoop.hdfs.security.token.block.DataEncryptionKey newDataEncryptionKey()>"));

        String smt = new GreyStateSmtGenerator().generate(spec(), result);

        assertTrue(smt.contains("Relevant cache summary lacks expiry refresh"));
        assertTrue(smt.contains("stale cached DEK is possible"));
        assertFalse(smt.contains("Sending stale cached DEK is disallowed"));
    }

    private GreyStateSpec spec() {
        return new GreyStateSpec(
                Arrays.asList(new GreyStateSpec.FatalSeed(
                        "seed",
                        "Example",
                        "fatal",
                        "ExampleException")),
                Arrays.asList("Example"),
                "target/grey-smt-test",
                2);
    }

    private SemanticEvent event(String type) {
        return new SemanticEvent(type, "method", "unit", null);
    }

    private SemanticEvent event(String type, String method) {
        return new SemanticEvent(type, method, "unit", null);
    }
}

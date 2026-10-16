package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;

/**
 * Where a fault door fails ({@link ClientFaults}): in the workload client's
 * root contexts only the doors of the transports the system names; anywhere
 * else, and with no transport named, every door.
 */
public class ClientFaultsTest {
    @Rule
    public TemporaryFolder tree = new TemporaryFolder();

    private static final String ZK =
            "<org.apache.solr.common.cloud.SolrZkClient: java.lang.String "
                    + "create(java.lang.String,byte[],"
                    + "org.apache.zookeeper.CreateMode,boolean)>";
    private static final String HTTP =
            "<org.apache.solr.client.solrj.impl.HttpSolrClient: "
                    + "org.apache.solr.common.util.NamedList executeMethod("
                    + "org.apache.http.client.methods.HttpRequestBase,"
                    + "org.apache.solr.client.solrj.ResponseParser,boolean)>";

    @Test
    public void onlyTheNamedTransportsFailInAClientRoot() throws Exception {
        Path doors = tree.newFile("doors.jsonl").toPath();
        Files.write(doors, Arrays.asList(
                "{\"kind\":\"HOOK\",\"transport\":\"ZOOKEEPER\","
                        + "\"method\":\"" + ZK + "\"}",
                "{\"kind\":\"HOOK\",\"transport\":\"SOLR_HTTP\","
                        + "\"method\":\"" + HTTP + "\"}",
                "{\"kind\":\"PUBLISHED_VIEW\",\"transport\":\"SOLR_ZK\","
                        + "\"path\":\"/aliases.json\"}"),
                StandardCharsets.UTF_8);
        ClientFaults solr = ClientFaults.read(doors,
                Arrays.asList("SOLR_HTTP", "SOLR_HTTP2"));
        OccurrenceAddress client = occurrence("auto0/client0",
                CausalContext.of(Role.CLIENT, "suite", 1));
        OccurrenceAddress overseer = occurrence("auto0/node0",
                CausalContext.of(Role.of("OVERSEER_TASK"), "", 1));
        // occurrence | site | fails under Solr's cut | fails with none
        Object[][] rows = {
            {client, ZK + "#u17", false, true},
            {client, ZK + "#u22", false, true},
            {client, HTTP + "#u37", true, true},
            {client, "<a.B: void c()>#u3", true, true},
            {overseer, ZK + "#u17", true, true},
        };
        for (Object[] row : rows) {
            OccurrenceAddress at = (OccurrenceAddress) row[0];
            String site = (String) row[1];
            assertEquals(site + " at " + at.render(), row[2],
                    solr.fails(at, site));
            assertEquals(site + " uncut", row[3],
                    ClientFaults.read(doors, Collections.<String>emptyList())
                            .fails(at, site));
        }
    }

    private static OccurrenceAddress occurrence(String node,
                                                CausalContext context) {
        return OccurrenceAddress.of(NodeId.parse(node + "#epoch0"),
                "REGION.6140aa2b-f992-3fec-acbd-9fd87aef994c", context,
                ExecutionIndex.empty());
    }
}

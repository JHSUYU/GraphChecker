package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;

import org.junit.After;
import org.junit.Test;

/**
 * A store location keyed in names every run spells alike: the run-only
 * names an adapter stated as a node's become the node's name, the longest
 * first, the host and port inside a stated node name too; one no adapter
 * stated is left, and named; a spelling that holds no run-only name is no
 * statement.
 */
public class RunNamesTest {
    @After
    public void reset() {
        RunNames.resetForTests();
    }

    @Test
    public void aLocationKeysByItsNodesStatedNames() {
        RunNames.spelled("auto0/node0", "10.0.0.1:8983");
        RunNames.spelled("auto0/node1", "10.0.0.1:8983_solr");
        RunNames.spelled("auto0/node0", "72088256043548677");
        RunNames.spelled("auto0/node0", "72088256043548677");
        RunNames.spelled("auto0/node2", "0");
        RunNames.spelled("auto0/node3", "10.0.0.3:9000_solr");
        String[][] rows = {
            // location, key, the run-only name left unstated
            {"/live_nodes/10.0.0.1:8983_solr", "/live_nodes/{auto0/node1}", ""},
            {"/x/10.0.0.1:8983/y", "/x/{auto0/node0}/y", ""},
            {"/e/72088256043548677-core_node3-n_",
                "/e/{auto0/node0}-core_node3-n_", ""},
            {"/live_nodes/10.0.0.2:7000_solr", "/live_nodes/10.0.0.2:7000_solr",
                "10.0.0.2:7000"},
            {"/a/0/b", "/a/0/b", ""},
            {"/u/http://10.0.0.3:9000/solr", "/u/http://{auto0/node3}/solr", ""},
        };
        for (String[] row : rows) {
            RunNames.Keyed keyed = RunNames.key(row[0]);
            assertEquals(row[0], row[1], keyed.location);
            assertEquals(row[0], row[2], keyed.unnamed);
        }
        assertEquals(true, RunNames.firstUnstated("10.0.0.2:7000"));
        assertEquals(false, RunNames.firstUnstated("10.0.0.2:7000"));
    }
}

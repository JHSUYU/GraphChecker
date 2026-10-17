package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.plan.SystemView;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

/**
 * A guard of the system's view classes is no flip site (ClosurePlanner): a
 * site's method, its owner a view class or a nested class of one, is held by
 * the view; any other site is not.
 */
public class ViewGuardsTest {
    @Test
    public void aViewClassGuardIsHeldByTheView() {
        SystemView solr = SystemView.of("org.apache.solr.common.cloud.Slice,"
                + "org.apache.solr.common.cloud.ZkStateReader");
        // site | held by Solr's view
        Object[][] rows = {
            {"<org.apache.solr.common.cloud.Slice: void <init>(java.lang.String,"
                    + "java.util.Map,java.util.Map,java.lang.String)>#u36", true},
            {"<org.apache.solr.common.cloud.ZkStateReader$StateWatcher: void "
                    + "refreshAndWatch()>#u4", true},
            {"<org.apache.solr.cloud.api.collections.SplitShardCmd: boolean "
                    + "split(org.apache.solr.common.cloud.ClusterState)>#u50",
                    false},
        };
        for (Object[] row : rows) {
            String site = (String) row[0];
            assertEquals(site, row[1],
                    solr.holds(ClosurePlanner.methodOf(site)));
            assertEquals(site, false, SystemView.of("")
                    .holds(ClosurePlanner.methodOf(site)));
        }
    }
}

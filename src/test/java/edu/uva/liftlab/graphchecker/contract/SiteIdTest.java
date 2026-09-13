package edu.uva.liftlab.graphchecker.contract;

import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

/** {@code <method>#u<unitIndex>}: one spelling of one bytecode site. */
public class SiteIdTest {
    private static final String METHOD =
            "<org.apache.hadoop.hdfs.server.namenode.FSNamesystem:"
                    + " void startFile()>";

    @Test
    public void aSiteIsItsMethodAndUnitIndex() {
        assertEquals(METHOD + "#u0", SiteId.of(METHOD, 0));
        assertEquals(METHOD + "#u137", SiteId.of(METHOD, 137));
    }
}

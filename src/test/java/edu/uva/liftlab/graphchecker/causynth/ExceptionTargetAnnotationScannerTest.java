package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.fixtures.CrossMethodExternalFieldThreeThreadWorkload;
import edu.uva.liftlab.graphchecker.fixtures.MixedTypeThreeThreadRpcWorkload;
import edu.uva.liftlab.graphchecker.fixtures.ThreeThreadRpcWorkload;
import org.junit.Test;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class ExceptionTargetAnnotationScannerTest {
    @Test
    public void findsExactNewInstructionForEachCoreWorkload()
            throws Exception {
        Path classes = Paths.get(ThreeThreadRpcWorkload.class
                .getProtectionDomain().getCodeSource().getLocation().toURI());
        List<ExceptionTargetSite> sites =
                ExceptionTargetAnnotationScanner.scan(
                        Collections.singletonList(classes.toString()));
        Map<String, ExceptionTargetSite> byId = new LinkedHashMap<>();
        for (ExceptionTargetSite site : sites) {
            byId.put(site.id, site);
        }

        assertTarget(byId.get("three-thread-rpc"),
                ThreeThreadRpcWorkload.class.getName() + "$ConsumerThread",
                ThreeThreadRpcWorkload.BugReachedException.class.getName());
        assertTarget(byId.get("cross-method-fields"),
                CrossMethodExternalFieldThreeThreadWorkload.class.getName()
                        + "$ConsumerThread",
                CrossMethodExternalFieldThreeThreadWorkload
                        .CrossMethodBugReachedException.class.getName());
        assertTarget(byId.get("multitype"),
                MixedTypeThreeThreadRpcWorkload.class.getName()
                        + "$ConsumerThread",
                MixedTypeThreeThreadRpcWorkload
                        .MixedTypeBugReachedException.class.getName());
    }

    private static void assertTarget(ExceptionTargetSite site,
                                     String owner, String exception) {
        assertTrue("missing annotation for " + exception, site != null);
        assertEquals(owner, site.className);
        assertEquals("executeWorker", site.methodName);
        assertEquals("()V", site.methodDescriptor);
        assertEquals(exception, site.exceptionClass);
        assertEquals(0, site.exceptionConstructionOrdinal);
        assertTrue(site.bytecodeInstructionIndex >= 0);
        assertTrue(site.sourceLine > 0);
    }
}

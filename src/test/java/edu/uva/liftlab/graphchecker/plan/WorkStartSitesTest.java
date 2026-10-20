package edu.uva.liftlab.graphchecker.plan;

import org.junit.Test;

import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;

public class WorkStartSitesTest {
    @Test
    public void aNettyTimerTaskOfAnyShadingIsStartedByNewTimeoutAndEnteredByRun() {
        Object[][] table = {
            {"org.apache.hbase.thirdparty.io.netty.util.TimerTask", "run", 1,
                    true, true},
            {"io.netty.util.TimerTask", "run", 1, true, true},
            {"io.netty.util.TimerTask", "run", 0, true, false},
            {"java.lang.Runnable", "run", 1, true, false},
            {"java.lang.Runnable", "run", 0, true, true},
            {"org.example.NettyUtilTimerTask", "run", 1, false, false},
        };
        for (Object[] row : table) {
            WorkStartSites.Types type = hierarchy((String) row[0]);
            String what = Arrays.toString(row);
            assertEquals(what, row[3], WorkStartSites.carriesWork(type));
            assertEquals(what, row[4], WorkStartSites.entersWork(
                    (String) row[1], (Integer) row[2], type));
        }
        assertEquals(true, WorkStartSites.submitsArguments("newTimeout", 3));
        assertEquals(true, WorkStartSites.mayEnterWork("run", 1));
        assertEquals(true, WorkStartSites.mayHandOffWork(
                "org/apache/hbase/thirdparty/io/netty/util/HashedWheelTimer",
                "newTimeout", 3));
    }

    @Test
    public void aContinuationIsRegisteredOnACompletionStageWithAFunction() {
        Object[][] table = {
            {"whenComplete", "java.util.concurrent.CompletableFuture", true},
            {"thenCompose", "java.util.concurrent.CompletionStage", true},
            {"exceptionally", "org.example.Retries", false},
            {"complete", "java.util.concurrent.CompletableFuture", false},
        };
        for (Object[] row : table) {
            assertEquals(Arrays.toString(row), row[2],
                    WorkStartSites.registersContinuation((String) row[0],
                            hierarchy((String) row[1])));
            assertEquals(Arrays.toString(row), row[2],
                    WorkStartSites.mayHandOffWork(((String) row[1])
                            .replace('.', '/'), (String) row[0], 1));
        }
        assertEquals(true, WorkStartSites.continues(
                "java.util.function.BiConsumer"));
        assertEquals(false, WorkStartSites.continues(
                "java.util.concurrent.Executor"));
    }

    private static WorkStartSites.Types hierarchy(String name) {
        List<String> names = Arrays.asList(name, "java.lang.Object");
        return typeName -> typeName.startsWith("*")
                ? names.stream().anyMatch(held
                        -> held.endsWith(typeName.substring(1)))
                : names.contains(typeName);
    }
}

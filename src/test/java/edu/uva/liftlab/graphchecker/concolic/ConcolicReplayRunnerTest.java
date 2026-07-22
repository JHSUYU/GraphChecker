package edu.uva.liftlab.graphchecker.concolic;

import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class ConcolicReplayRunnerTest {
    @Test
    public void dryRunSelectsReplayableActivationAndWritesManifest() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path root = folder.getRoot().toPath();
            Path plan = root.resolve("activation.jsonl");
            Path javaHome = root.resolve("jdk");
            Path manifest = root.resolve("manifest.jsonl");
            Files.createDirectories(javaHome);
            Files.write(plan, ("{\"activationId\":\"ACT.0\","
                    + "\"regionId\":\"REGION.0\",\"test\":\"testA\","
                    + "\"replayable\":true,\"schedulerReady\":true}\n")
                    .getBytes(StandardCharsets.UTF_8));

            ConcolicReplayRunner.Arguments arguments =
                    ConcolicReplayRunner.Arguments.parse(new String[]{
                            "--activation-plan", plan.toString(),
                            "--java-home", javaHome.toString(),
                            "--manifest", manifest.toString(),
                            "--dry-run", "true",
                            "--", "unused-command"});
            ConcolicReplayRunner.ReplayResult result =
                    ConcolicReplayRunner.replay(arguments);

            assertEquals(1, result.selected);
            assertEquals(1, result.skipped);
            assertTrue(new String(Files.readAllBytes(manifest),
                    StandardCharsets.UTF_8).contains("DRY_RUN"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void retiredSymbolicReadinessDoesNotAuthorizeReplay()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path root = folder.getRoot().toPath();
            Path plan = root.resolve("activation.jsonl");
            Path javaHome = root.resolve("jdk");
            Path manifest = root.resolve("manifest.jsonl");
            Files.createDirectories(javaHome);
            Files.write(plan, ("{\"activationId\":\"ACT.OLD\","
                    + "\"regionId\":\"REGION.0\",\"test\":\"testA\","
                    + "\"replayable\":true,\"symbolicReady\":true}\n")
                    .getBytes(StandardCharsets.UTF_8));

            ConcolicReplayRunner.ReplayResult result =
                    ConcolicReplayRunner.replay(
                            ConcolicReplayRunner.Arguments.parse(new String[]{
                                    "--activation-plan", plan.toString(),
                                    "--java-home", javaHome.toString(),
                                    "--manifest", manifest.toString(),
                                    "--dry-run", "true",
                                    "--", "unused-command"}));

            assertEquals(1, result.selected);
            assertEquals(1, result.skipped);
            assertTrue(new String(Files.readAllBytes(manifest),
                    StandardCharsets.UTF_8).contains(
                    "SKIPPED_NOT_SCHEDULER_READY"));
        } finally {
            folder.delete();
        }
    }
}

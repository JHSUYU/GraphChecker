package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.RelationSummary;
import org.junit.Assume;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ConcolicSmtComposerTest {
    @Rule
    public final TemporaryFolder temporary = new TemporaryFolder();

    @Test
    public void boxedIntegralTagsAcceptPrimitiveAndWrapperTypes() {
        String[] primitives = {"B", "C", "S", "I", "J"};
        String[] wrappers = {"java.lang.Byte", "java/lang/Character",
                "Ljava/lang/Short;", "java.lang.Integer",
                "java/lang/Long"};
        String[] tags = {"Byte", "Char", "Short", "Int", "Long"};
        for (int index = 0; index < tags.length; index++) {
            assertEquals("(V" + tags[index] + " 4)",
                    ContainerSmtCodec.boxIntegral(
                            "4", primitives[index]));
            assertEquals("(V" + tags[index] + " 4)",
                    ContainerSmtCodec.boxIntegral(
                            "4", wrappers[index]));
            assertEquals("(value" + tags[index] + " value)",
                    ContainerSmtCodec.unboxIntegral(
                            "value", wrappers[index]));
        }
    }

    @Test
    public void recursivelySelectsDifferentInstancesOfOneStaticRegion()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String outerInstance = "REGION.1@Test#call20";
        String holderInstance = "REGION.1@Test#call10";
        JsonObject outerToFatal = binding("EDGE.SHARED", outerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        JsonObject holderToOuter = binding("EDGE.SHARED", holderInstance,
                "REGION.1.out.0", outerInstance, "REGION.1.in.0", 10, 20);
        JsonObject unrelated = binding("EDGE.UNRELATED",
                "REGION.1@Test#call99", "REGION.1.out.0",
                "REGION.0@Test#call99", "REGION.0.in.0", 90, 99);

        RelationSummary outer = summary("OUTER", outerInstance, 20, 10,
                Collections.singletonList("REGION.1.in.0"),
                Collections.singletonList(outerToFatal));
        RelationSummary holder = summary("HOLDER", holderInstance, 10, 20,
                Collections.<String>emptyList(),
                Collections.singletonList(holderToOuter));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Arrays.asList(outer, holder), outerToFatal, unrelated);

        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        assertFalse(result.smtLib,
                result.smtLib.contains("ConflictingProducerRegionInstance"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "port__REGION_1_out_0__instance__REGION_1_Test_call20"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "port__REGION_1_out_0__instance__REGION_1_Test_call10"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "state_writer_value__EDGE_SHARED"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "state_writer_value__resolved_state_channel"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "port__REGION_1_out_0__instance__REGION_1_Test_call99"));
        assertEquals(1, result.manifest.getAsJsonArray(
                "resolvedEdgeBindings").size());
        assertEquals("EDGE.SHARED", result.manifest.getAsJsonArray(
                "resolvedEdgeBindings").get(0).getAsString());
    }

    @Test
    public void differentInstancesDoNotShareOneStaticPortSymbol()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String outerInstance = "REGION.1@Test#call20";
        String holderInstance = "REGION.1@Test#call10";
        JsonObject outerToFatal = binding("EDGE.OUTER", outerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        JsonObject holderToOuter = binding("EDGE.HOLDER", holderInstance,
                "REGION.1.out.0", outerInstance, "REGION.1.in.0", 10, 20);

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Arrays.asList(
                        summary("OUTER", outerInstance, 20, 10,
                                Collections.singletonList("REGION.1.in.0"),
                                Collections.singletonList(outerToFatal)),
                        summary("HOLDER", holderInstance, 10, 20,
                                Collections.<String>emptyList(),
                                Collections.singletonList(holderToOuter))),
                outerToFatal);

        String outerPort =
                "port__REGION_1_out_0__instance__REGION_1_Test_call20";
        String holderPort =
                "port__REGION_1_out_0__instance__REGION_1_Test_call10";
        assertTrue(result.smtLib.contains("(declare-const " + outerPort));
        assertTrue(result.smtLib.contains("(declare-const " + holderPort));
        assertTrue(result.smtLib.contains(
                "(= " + outerPort + " (VInt 10))"));
        assertTrue(result.smtLib.contains(
                "(= " + holderPort + " (VInt 20))"));
        assertFalse(result.smtLib.contains(
                "(= " + outerPort + " " + holderPort + ")"));
    }

    @Test
    public void logicalSummaryIsAlphaRenamedForEveryExactOccurrence()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String firstInstance = "REGION.1@Test#call10";
        String secondInstance = "REGION.1@Test#call20";
        JsonObject firstToSecond = binding("EDGE.FIRST.SECOND",
                firstInstance, "REGION.1.out.0", secondInstance,
                "REGION.1.in.1", 10, 20);
        JsonObject secondToFatal = binding("EDGE.SECOND.FATAL",
                secondInstance, "REGION.1.out.1", fatalInstance,
                "REGION.0.in.0", 20, 30);

        RelationSummary logical = logicalSummary(
                summary("LOGICAL", firstInstance, 10, 7,
                        Collections.singletonList("REGION.1.in.0"),
                        Arrays.asList(firstToSecond, secondToFatal)),
                occurrence(firstInstance, 10, "REGION.1.in.0",
                        "REGION.1.out.0", "EDGE.FIRST.SECOND"),
                occurrence(secondInstance, 20, "REGION.1.in.1",
                        "REGION.1.out.1", "EDGE.FIRST.SECOND",
                        "EDGE.SECOND.FATAL"));
        JsonObject repeatedRegion = region("REGION.1", true, true);
        repeatedRegion.getAsJsonArray("symbolicInputs").add(
                port("REGION.1.in.1", true));
        repeatedRegion.getAsJsonArray("outputs").add(
                port("REGION.1.out.1", false));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(logical), Arrays.asList(
                        region("REGION.0", true, false), repeatedRegion),
                secondToFatal);

        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        assertTrue(result.smtLib, result.smtLib.contains(
                "port__REGION_1_out_0__instance__REGION_1_Test_call10"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "port__REGION_1_out_1__instance__REGION_1_Test_call20"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "port__REGION_1_in_1__instance__REGION_1_Test_call20"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "port__REGION_1_out_0__instance__REGION_1_Test_call20"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "case_selector__region_REGION_1_instance_"
                        + "REGION_1_Test_call10_case_CASE_LOGICAL"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "case_selector__region_REGION_1_instance_"
                        + "REGION_1_Test_call20_case_CASE_LOGICAL"));
        assertEquals(2, result.manifest.getAsJsonArray(
                "resolvedEdgeBindings").size());
        if (z3Available()) {
            ConcolicConstraintSolver.SolverOutput solved =
                    ConcolicConstraintSolver.run(Paths.get("z3"),
                            result.smtLib, 10_000L);
            assertEquals(solved.diagnostic(), "sat", solved.status());
        }
    }

    @Test
    public void vmClockPlaceholdersAreScopedPerExactOccurrence()
            throws Exception {
        String firstInstance = "REGION.1@Test#call10";
        String secondInstance = "REGION.1@Test#call20";
        String fatalInstance = "REGION.0@Test#call30";
        JsonObject firstToSecond = binding("EDGE.TIME.FIRST",
                firstInstance, "REGION.1.out.0", secondInstance,
                "REGION.1.in.1", 10, 20);
        JsonObject secondToFatal = binding("EDGE.TIME.SECOND",
                secondInstance, "REGION.1.out.1", fatalInstance,
                "REGION.0.in.0", 20, 30);

        RelationSummary logical = logicalSummary(
                summary("TIME", firstInstance, 10, currentTimePlaceholder(),
                        Collections.singletonList("REGION.1.in.0"),
                        Arrays.asList(firstToSecond, secondToFatal), "long"),
                occurrence(firstInstance, 10, "REGION.1.in.0",
                        "REGION.1.out.0", "EDGE.TIME.FIRST"),
                occurrence(secondInstance, 20, "REGION.1.in.1",
                        "REGION.1.out.1", "EDGE.TIME.FIRST",
                        "EDGE.TIME.SECOND"));
        JsonObject repeatedRegion = region("REGION.1", "long", "long");
        repeatedRegion.getAsJsonArray("symbolicInputs").add(
                port("REGION.1.in.1", true, "long"));
        repeatedRegion.getAsJsonArray("outputs").add(
                port("REGION.1.out.1", false, "long"));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(logical), Arrays.asList(
                        region("REGION.0", "long", ""), repeatedRegion),
                secondToFatal);

        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        assertEquals(result.smtLib, 2,
                count(result.smtLib, "(declare-const environment__"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "environment__region_REGION_1_instance_"
                        + "REGION_1_Test_call10_case_CASE_TIME__"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "environment__region_REGION_1_instance_"
                        + "REGION_1_Test_call20_case_CASE_TIME__"));
    }

    @Test
    @SuppressWarnings("unchecked")
    public void occurrenceInstantiationSelectsEachLedgerBindingOnce()
            throws Exception {
        String firstInstance = "REGION.1@Test#call10";
        String secondInstance = "REGION.1@Test#call20";
        String fatalInstance = "REGION.0@Test#call30";
        JsonObject firstToSecond = binding("EDGE.FIRST.SECOND",
                firstInstance, "REGION.1.out.0", secondInstance,
                "REGION.1.in.1", 10, 20);
        JsonObject secondToFatal = binding("EDGE.SECOND.FATAL",
                secondInstance, "REGION.1.out.1", fatalInstance,
                "REGION.0.in.0", 20, 30);
        RelationSummary logical = logicalSummary(
                summary("LOGICAL-BINDINGS", firstInstance, 10, 7,
                        Collections.singletonList("REGION.1.in.0"),
                        Arrays.asList(firstToSecond, secondToFatal)),
                occurrence(firstInstance, 10, "REGION.1.in.0",
                        "REGION.1.out.0", "EDGE.FIRST.SECOND"),
                occurrence(secondInstance, 20, "REGION.1.in.1",
                        "REGION.1.out.1", "EDGE.FIRST.SECOND",
                        "EDGE.SECOND.FATAL"));

        Class<?> type = Class.forName(ConcolicSmtComposer.class.getName()
                + "$OccurrenceInstantiator");
        java.lang.reflect.Method expand = type.getDeclaredMethod(
                "expand", RelationSummary.class);
        expand.setAccessible(true);
        java.util.List<RelationSummary> instantiated =
                (java.util.List<RelationSummary>) expand.invoke(null,
                        logical);

        assertEquals(2, instantiated.size());
        for (RelationSummary occurrenceSummary : instantiated) {
            int expected = firstInstance.equals(
                    occurrenceSummary.regionInstanceId()) ? 1 : 2;
            assertEquals(expected, occurrenceSummary.edgeBindings().size());
            java.util.Set<String> ids = new java.util.LinkedHashSet<>();
            for (JsonObject edge : occurrenceSummary.edgeBindings()) {
                assertTrue(ids.add(edge.get("edgeId").getAsString()));
            }
        }

        RelationSummary incomplete = logicalSummary(
                summary("INCOMPLETE-BINDINGS", firstInstance, 10, 7,
                        Collections.singletonList("REGION.1.in.0"),
                        Arrays.asList(firstToSecond, secondToFatal)),
                occurrence(firstInstance, 10, "REGION.1.in.0",
                        "REGION.1.out.0", "EDGE.FIRST.SECOND"),
                occurrence(secondInstance, 20, "REGION.1.in.1",
                        "REGION.1.out.1", "EDGE.SECOND.FATAL"));
        try {
            expand.invoke(null, incomplete);
            org.junit.Assert.fail("incomplete binding ledger must fail");
        } catch (java.lang.reflect.InvocationTargetException expected) {
            assertTrue(expected.getCause().getMessage().contains(
                    "binding-id ledger is incomplete"));
        }
    }

    @Test
    public void malformedLogicalOccurrenceCatalogFailsClosed()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call10";
        JsonObject edge = binding("EDGE.BAD", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 10, 30);
        JsonObject malformedOccurrence = occurrence(producerInstance, 10,
                "REGION.1.in.0", "REGION.1.out.0", "EDGE.BAD");
        malformedOccurrence.add("outputPortMap", new JsonArray());
        RelationSummary logical = logicalSummary(summary("BAD",
                producerInstance, 10, 7,
                Collections.singletonList("REGION.1.in.0"),
                Collections.singletonList(edge)), malformedOccurrence);

        boolean rejected = false;
        try {
            compose(fatalInstance, Collections.singletonList(logical), edge);
        } catch (java.io.IOException expected) {
            rejected = expected.getMessage().contains(
                    "Malformed relation summary");
        }
        assertTrue("malformed catalog must fail before SMT emission",
                rejected);
    }

    @Test
    public void selectedSharedStateReadMustUseItsVmWriter()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.VERSION", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(summary("VERSION",
                        producerInstance, 20, 10,
                        Collections.<String>emptyList(),
                        Collections.singletonList(edge))), edge);

        String suffix = "EDGE_VERSION__REGION_0_Test_call30_REGION_0_in_0";
        String read = "state_read_position__" + suffix;
        String write = "state_write_position__" + suffix + "_0";
        String producer = "port__REGION_1_out_0__instance__"
                + "REGION_1_Test_call20";
        String consumer = "port__REGION_0_in_0__instance__"
                + "REGION_0_Test_call30";
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const " + read + " Int)"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const " + write + " Int)"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "(= " + write + " 20)"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "(= " + read + " 30)"));

        assertFalse(result.smtLib, result.smtLib.contains(
                "state_initial_value__"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "state_initial_before_writers__"));
        assertUnsat(result.smtLib, "(assert (< " + read + " " + write
                + "))\n");
        assertUnsat(result.smtLib, "(assert (< " + write + " " + read
                + "))\n(assert (distinct " + consumer + " " + producer
                + "))\n");
    }

    @Test
    public void sameLaneProgramOrderForcesWriterBeforeReader()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.PROGRAM.ORDER", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        edge.addProperty("readerLaneId", "lane.writer");
        edge.addProperty("programOrderRequired", true);
        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(summary("PROGRAM_ORDER",
                        producerInstance, 20, 10,
                        Collections.<String>emptyList(),
                        Collections.singletonList(edge))), edge);

        String suffix = "EDGE_PROGRAM_ORDER__REGION_0_Test_call30_"
                + "REGION_0_in_0";
        String read = "state_read_position__" + suffix;
        String write = "state_write_position__" + suffix + "_0";
        assertTrue(result.smtLib, result.smtLib.contains(
                "state_program_order__" + suffix));
        assertUnsat(result.smtLib, "(assert (< " + read + " " + write
                + "))\n");
    }

    @Test
    public void sameLaneWritersKeepProgramOrderInsideInterleaving()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String fatalInstance = "REGION.0@Test#call30";
        String firstInstance = "REGION.1@Test#call10";
        String secondInstance = "REGION.1@Test#call20";
        JsonObject first = binding("EDGE.FIRST", firstInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 10, 30);
        JsonObject second = binding("EDGE.SECOND", secondInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        first.addProperty("writerLaneId", "lane.shared");
        second.addProperty("writerLaneId", "lane.shared");

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Arrays.asList(
                        summary("FIRST", firstInstance, 10, 1,
                                Collections.<String>emptyList(),
                                Collections.singletonList(first)),
                        summary("SECOND", secondInstance, 20, 2,
                                Collections.<String>emptyList(),
                                Collections.singletonList(second))),
                first, second);

        assertTrue(result.smtLib, result.smtLib.contains(
                "state_writer_program_order__versioned_state_channel"));
        assertTrue(result.smtLib, result.smtLib.matches("(?s).*\\(< "
                + "state_write_position__versioned_state_channel[^ ]+_0 "
                + "state_write_position__versioned_state_channel[^ )]+_1"
                + "\\).*"));

        String suffix = "versioned_state_channel__"
                + "REGION_0_Test_call30_REGION_0_in_0__"
                + "REGION_0_Test_call30_REGION_0_in_0";
        String read = "state_read_position__" + suffix;
        String firstWrite = "state_write_position__" + suffix + "_0";
        String secondWrite = "state_write_position__" + suffix + "_1";
        String secondProducer = "port__REGION_1_out_0__instance__"
                + "REGION_1_Test_call20";
        String consumer = "port__REGION_0_in_0__instance__"
                + "REGION_0_Test_call30";
        String secondIsLatest = "(assert (< " + firstWrite + " "
                + secondWrite + "))\n(assert (< " + secondWrite + " "
                + read + "))\n";
        assertSat(result.smtLib, secondIsLatest);
        assertUnsat(result.smtLib, secondIsLatest
                + "(assert (distinct " + consumer + " "
                + secondProducer + "))\n");
    }

    @Test
    public void repeatedAccessesOnOneStaticEdgeRemainDistinctWriters()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject first = binding("EDGE.REPEATED", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 10, 30);
        JsonObject second = binding("EDGE.REPEATED", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(summary("REPEATED",
                        producerInstance, 20, 1,
                        Collections.<String>emptyList(),
                        Arrays.asList(first, second))), first, second);

        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        assertTrue(result.smtLib, result.smtLib.contains(
                "state_write_position__versioned_state_channel"));
        assertTrue(result.smtLib, result.smtLib.matches("(?s).*\\(distinct "
                + "state_read_position__versioned_state_channel[^ ]+ "
                + "state_write_position__versioned_state_channel[^ ]+_0 "
                + "state_write_position__versioned_state_channel[^ )]+_1"
                + "\\).*"));
    }

    @Test
    public void versionedOutputChannelKeepsEveryVersionChoosable()
            throws Exception {
        // Three exported site-local versions enter the composed channel as
        // three guarded cases.  The solver must be free to choose any one
        // version, and the selector partition must force exactly one.
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.VERSIONSET", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(versionedSummary(
                        producerInstance, 3,
                        Collections.singletonList(edge))), edge);

        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        String choice = "output_version_choice__"
                + "REGION_1_Test_call20_REGION_1_out_0";
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const " + choice + " Int)"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(and (<= 1 " + choice + ") (<= " + choice + " 3))"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "region_case_selector_partition_REGION_1"));
        assertEquals(result.smtLib, 3,
                count(result.smtLib, "case_selector_definition_REGION_1"));

        if (!z3Available()) return;
        String consumer = "port__REGION_0_in_0__instance__"
                + "REGION_0_Test_call30";
        // Every exported version stays reachable at the consumer.
        assertSat(result.smtLib, "(assert (= " + consumer + " (VInt 1)))\n");
        assertSat(result.smtLib, "(assert (= " + consumer + " (VInt 2)))\n");
        assertSat(result.smtLib, "(assert (= " + consumer + " (VInt 3)))\n");
        // The choice variable owns which version the consumer observed.
        assertUnsat(result.smtLib, "(assert (= " + choice + " 3))\n"
                + "(assert (= " + consumer + " (VInt 1)))\n");
        // Exactly one version: nothing outside the exported chain exists.
        assertUnsat(result.smtLib, "(assert (and (distinct " + consumer
                + " (VInt 1)) (distinct " + consumer
                + " (VInt 2)) (distinct " + consumer + " (VInt 3))))\n");
    }

    private static RelationSummary versionedSummary(
            String instance, int versionCount,
            java.util.List<JsonObject> bindings) {
        JsonObject slice = emptySlice("REGION.1.out.0",
                "<Test: int output>");
        OutputClosureContract closure = OutputClosureCodec.singleton(
                "REGION.1", instance, 20L, "REGION.1.out.0",
                "<Test: int output>", "REGION_OUTPUT", "int", slice);

        JsonObject row = new JsonObject();
        row.addProperty("summaryId", "SUMMARY.VERSIONSET");
        row.addProperty("regionId", "REGION.1");
        row.addProperty("regionInstanceId", instance);
        row.addProperty("rootCallId", 20L);
        OutputClosureCodec.writeTo(row, closure);
        JsonArray encodedBindings = new JsonArray();
        for (JsonObject binding : bindings) {
            encodedBindings.add(binding.deepCopy());
        }
        row.add("edgeBindings", encodedBindings);
        JsonObject relation = new JsonObject();
        relation.addProperty("schemaVersion", 1);
        relation.addProperty("kind", "GUARDED_PATH_MERGE");
        JsonArray cases = new JsonArray();
        for (int version = 1; version <= versionCount; version++) {
            JsonObject item = new JsonObject();
            item.addProperty("caseId", "CASE.VERSIONSET.V." + version);
            item.addProperty("sourceTaskId", "TASK.VERSIONSET");
            JsonObject guard = new JsonObject();
            guard.addProperty("kind", "PATH_CONDITION");
            JsonArray conditions = new JsonArray();
            conditions.add(edu.uva.liftlab.graphchecker.contract
                    .BoundedOutputVersions.versionSelectionCondition(
                            "REGION.1.out.0", "<Test: void run()>#u1",
                            version, versionCount));
            guard.add("conditions", conditions);
            item.add("guard", guard);
            JsonObject outputs = new JsonObject();
            outputs.add("REGION.1.out.0", integer(version));
            item.add("outputExpressions", outputs);
            cases.add(item);
        }
        relation.add("cases", cases);
        row.add("regionRelation", relation);
        row.addProperty("relationallyComplete", true);
        return RelationSummary.decode(row);
    }

    @Test
    public void protocolCausalityIsSymbolic()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = protocolBinding("EDGE.RPC", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0",
                100, 200, 300);
        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(summary("RPC", producerInstance,
                        20, 10, Collections.<String>emptyList(),
                        Collections.singletonList(edge))), edge);

        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        assertTrue(result.smtLib, result.smtLib.contains(
                "rpc_caller_before_send__"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "rpc_send_before_receive__"));
        String suffix = "edge_binding_REGION_1_to_REGION_0_0__example_rpc";
        assertFalse(result.smtLib, result.smtLib.contains(
                "(= rpc_caller_position__" + suffix + " 100)"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "(= rpc_send_position__" + suffix + " 200)"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "(= rpc_receive_position__" + suffix + " 300)"));
        assertFalse(result.smtLib, result.smtLib.contains("irrelevant"));
    }

    @Test
    public void jointClosureMayCoverASingleDemand() throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call10";
        JsonObject toFatal = binding("EDGE.JOINT", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 10, 30);
        RelationSummary singleton = summary("JOINT", producerInstance,
                10, 7, Collections.<String>emptyList(),
                Collections.singletonList(toFatal));
        JsonObject row = singleton.toJson();

        JsonObject secondSlice = emptySlice("REGION.1.out.1",
                "<Test: int other>");
        OutputClosureContract second = OutputClosureCodec.singleton(
                "REGION.1", producerInstance, 10, "REGION.1.out.1",
                "<Test: int other>", "REGION_OUTPUT", "int",
                secondSlice);
        OutputClosureContract joint = OutputClosureCodec.merge(Arrays.asList(
                singleton.outputClosure(), second));
        OutputClosureCodec.writeTo(row, joint);
        row.getAsJsonObject("regionRelation").getAsJsonArray("cases")
                .get(0).getAsJsonObject()
                .getAsJsonObject("outputExpressions")
                .add("REGION.1.out.1", integer(9));
        JsonObject producerRegion = region("REGION.1", "", "int");
        producerRegion.getAsJsonArray("outputs").add(
                port("REGION.1.out.1", false));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(RelationSummary.decode(row)),
                Arrays.asList(region("REGION.0", "int", ""),
                        producerRegion),
                toFatal);

        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        assertTrue(result.smtLib.contains(
                "port__REGION_1_out_0__instance__REGION_1_Test_call10"));
        assertTrue(result.smtLib.contains(
                "port__REGION_1_out_1__instance__REGION_1_Test_call10"));
    }

    @Test
    public void boxedFieldValueUsesPrimitiveCarrierAcrossInvocations()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String consumerInstance = "REGION.1@Test#call20";
        String producerInstance = "REGION.1@Test#call10";
        JsonObject toFatal = binding("EDGE.BOXED.CONSUMER",
                consumerInstance, "REGION.1.out.0", fatalInstance,
                "REGION.0.in.0", 20, 30);
        JsonObject toConsumer = binding("EDGE.BOXED.PRODUCER",
                producerInstance, "REGION.1.out.0", consumerInstance,
                "REGION.1.in.0", 10, 20);
        JsonObject boxedInput = new JsonObject();
        boxedInput.addProperty("_type", "SymbolExpression");
        boxedInput.addProperty("_java_type", "L");
        boxedInput.addProperty("_exp", "REGION.1.in.0");

        RelationSummary consumer = summary("BOXED_CONSUMER",
                consumerInstance, 20, boxedInput,
                Collections.singletonList("REGION.1.in.0"),
                Arrays.asList(toFatal, toConsumer),
                "java.lang.Integer");
        JsonObject consumerRow = consumer.toJson();
        JsonObject owner = new JsonObject();
        owner.addProperty("_type", "SymbolExpression");
        owner.addProperty("_java_type", "LTest$Box;");
        owner.addProperty("_exp", "BOX_OWNER");
        JsonObject field = new JsonObject();
        field.addProperty("_type", "FieldAccessExpression");
        field.addProperty("_java_type", "L");
        field.addProperty("ownerClass", "Test$Box");
        field.addProperty("fieldOffset", 24);
        field.add("owner", owner);
        JsonObject materialization = binary(field, "==", boxedInput);
        materialization.addProperty("_code_position",
                "static void java.lang.System.symbolizeExactField("
                        + "jobject, jobject, jobject, jobject, jobject):-1");
        consumerRow.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject()
                .getAsJsonObject("guard").getAsJsonArray("conditions")
                .add(materialization);
        consumer = RelationSummary.decode(consumerRow);
        RelationSummary producer = summary("BOXED_PRODUCER",
                producerInstance, 10, integer(-15),
                Collections.<String>emptyList(),
                Collections.singletonList(toConsumer),
                "java.lang.Integer");

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Arrays.asList(consumer, producer),
                Arrays.asList(region("REGION.0", "int", ""),
                        region("REGION.1", "java.lang.Integer",
                                "java.lang.Integer")),
                toFatal);

        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        String inputPort =
                "port__REGION_1_in_0__instance__REGION_1_Test_call20";
        String inputValue =
                "sym__port__REGION_1_Test_call20_REGION_1_in_0__int";
        assertTrue(result.smtLib, result.smtLib.contains(
                "(= " + inputPort + " (VInt " + inputValue + "))"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "sym__port__REGION_1_Test_call20_REGION_1_in_0"
                        + "__boxed_ref Ref"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "(= " + inputPort + " (VRef "));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(= port__REGION_1_out_0__instance__REGION_1_Test_call10"
                        + " (VInt (- 15)))"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "state_writer_value__resolved_state_channel"));
    }

    @Test
    public void compositionUsesTheSameBoxedIntegralContainerTags()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.TAGGED", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        JsonObject cleared = associativeOperation("CLEAR",
                associativeState("UNUSED_MAP"));
        JsonObject withByte = associativeOperation("PUT", cleared,
                typedIntegral("B", 7), typedIntegral("B", 9));
        JsonObject byteResult = associativeRead(
                withByte, typedIntegral("B", 7), "B");

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(summary("TAGGED",
                        producerInstance, 20, byteResult,
                        Collections.<String>emptyList(),
                        Collections.singletonList(edge))), edge);

        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        assertTrue(result.smtLib, result.smtLib.contains("(VByte 7)"));
        assertTrue(result.smtLib, result.smtLib.contains("(VByte 9)"));
        assertTrue(result.smtLib, result.smtLib.contains("(valueByte "));
        for (String tag : new String[]{"Byte", "Char", "Short", "Int",
                "Long"}) {
            assertTrue(result.smtLib,
                    result.smtLib.contains("(V" + tag + " (value"
                            + tag + " Int))"));
        }
    }

    @Test
    public void observedSnapshotObjectCannotAliasNull() throws Exception {
        Assume.assumeTrue(z3Available());
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.SNAPSHOT", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        JsonObject cleared = associativeOperation("CLEAR",
                associativeState("UNUSED_MAP"));
        JsonObject snapshot = associativeOperation("PUT", cleared,
                integer(11745), reference(
                        "M_L'example/Key'_124", "example/Key"));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(summary("SNAPSHOT",
                        producerInstance, 20, snapshot,
                        Collections.<String>emptyList(),
                        Collections.singletonList(edge), "java.util.Map")),
                Arrays.asList(region("REGION.0", "java.util.Map", ""),
                        region("REGION.1", "", "java.util.Map")), edge);

        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        assertTrue(result.smtLib, result.smtLib.contains(
                "observed_snapshot_reference_non_null_"));
        String output = "port__REGION_1_out_0__instance__"
                + "REGION_1_Test_call20";
        String nullLookup = "(assert (= (valueRef (assoc_read " + output
                + " (VInt 11745))) nullRef))\n";
        String query = result.smtLib.replace("(check-sat)",
                nullLookup + "(check-sat)");
        ConcolicConstraintSolver.SolverOutput solved =
                ConcolicConstraintSolver.run(Paths.get("z3"), query,
                        10_000L);
        assertEquals(solved.diagnostic(), "unsat", solved.status());
    }

    @Test
    public void trustedRpcProjectionBindsOneBoundedObjectArrayState()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = protocolBinding("EDGE.ARRAY.PROJECTION",
                producerInstance, "REGION.1.out.0", fatalInstance,
                "REGION.0.in.0", 20, 21, 30);
        JsonObject cleared = associativeOperation("CLEAR",
                associativeState("UNUSED_MAP"));
        JsonObject withValue = associativeOperation("PUT", cleared,
                integer(7),
                reference("M_L'example/Key'_7", "example/Key"));
        JsonObject withTwoValues = associativeOperation("PUT", withValue,
                integer(11),
                reference("M_L'example/Key'_11", "example/Key"));
        JsonObject values = associativeOperation("VALUE_VIEW",
                withTwoValues);
        JsonObject iterator = associativeOperation("ITERATOR", values);
        JsonObject selected0 = associativeOperation("NEXT", iterator,
                integer(0));
        JsonObject selected1 = associativeOperation("NEXT", iterator,
                integer(1));
        JsonObject firstWrite = indexedOperation("WRITE",
                indexedOperation("STATE", reference(
                        "AL_5-0", "L"),
                        integer(2)), integer(0), selected0);
        JsonObject snapshot = indexedOperation("WRITE", firstWrite,
                integer(1), selected1);

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(summary("ARRAY.PROJECTION",
                        producerInstance, 20, snapshot,
                        Collections.<String>emptyList(),
                        Collections.singletonList(edge),
                        "example.Key[]")),
                Arrays.asList(region("REGION.0", "example.Key[]", ""),
                        region("REGION.1", "", "example.Key[]")), edge);

        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        String producer = "port__REGION_1_out_0__instance__"
                + "REGION_1_Test_call20";
        String consumer = "port__REGION_0_in_0__instance__"
                + "REGION_0_Test_call30";
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const " + producer + " IndexedState)"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const " + consumer + " IndexedState)"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(= " + producer + " " + consumer + ")"));
        assertTrue(result.smtLib, result.smtLib.contains("assoc_value_at"));
        assertTrue(result.smtLib, count(result.smtLib,
                "(indexed_write ") >= 2);
    }

    @Test
    public void competingSummariesForOneInvocationStillFailClosed()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject producerToFatal = binding("EDGE.CONFLICT",
                producerInstance, "REGION.1.out.0", fatalInstance,
                "REGION.0.in.0", 20, 30);

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Arrays.asList(
                        summary("FIRST", producerInstance, 20, 10,
                                Collections.<String>emptyList(),
                                Collections.singletonList(producerToFatal)),
                        summary("SECOND", producerInstance, 20, 11,
                                Collections.<String>emptyList(),
                                Collections.singletonList(producerToFatal))),
                producerToFatal);

        assertEquals("CANDIDATE_WITH_GAPS",
                result.manifest.get("state").getAsString());
        assertTrue(result.manifest.toString(),
                result.manifest.toString().contains(
                        "AmbiguousExactProducerSummary"));
        assertTrue(result.smtLib.contains(
                "(assert false) ; fail closed: unsupported"));
    }

    @Test
    public void manifestsCanonicalScalarTermsByDynamicOccurrence()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.INPUT", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        JsonObject input = new JsonObject();
        input.addProperty("_type", "SymbolExpression");
        input.addProperty("_java_type", "I");
        input.addProperty("_exp", "REGION.1.in.0");

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(summary("INPUT", producerInstance,
                        20, input,
                        Collections.singletonList("REGION.1.in.0"),
                        Collections.singletonList(edge))),
                edge);

        JsonArray catalog = result.manifest.getAsJsonArray(
                "canonicalPortOccurrences");
        assertEquals(result.manifest.toString(), 1, catalog.size());
        JsonObject occurrence = catalog.get(0).getAsJsonObject();
        assertEquals("REGION.1.in.0",
                occurrence.get("portId").getAsString());
        assertEquals(producerInstance,
                occurrence.get("regionInstanceId").getAsString());
        assertEquals("INT", occurrence.get("sort").getAsString());
        assertEquals(
                "sym__port__REGION_1_Test_call20_REGION_1_in_0__int",
                occurrence.get("solverTerm").getAsString());
    }

    /**
     * A free input is an honest freedom only while nothing proved a producer
     * for it.  Once the validated runtime edges name that exact consumer
     * port, composing without it dropped evidence, and {@code gaps: 0} over
     * that is a false report.
     */
    @Test
    public void unboundInputWithConfirmedEdgeEvidenceBecomesNamedGap()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.INPUT", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        JsonObject input = new JsonObject();
        input.addProperty("_type", "SymbolExpression");
        input.addProperty("_java_type", "I");
        input.addProperty("_exp", "REGION.1.in.0");

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(summary("INPUT", producerInstance,
                        20, input,
                        Collections.singletonList("REGION.1.in.0"),
                        Collections.singletonList(edge))),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)),
                new JsonArray(),
                Collections.singletonList(validatedEdge("EDGE.DROPPED",
                        "CONFIRMED_RUNTIME_IDENTITY", "REGION.1.out.0",
                        "REGION.1.in.0")),
                edge);

        assertEquals(result.manifest.toString(), "AUDITED",
                result.manifest.get("droppedEdgeEvidenceAudit")
                        .getAsString());
        assertTrue(result.manifest.toString(),
                result.manifest.toString().contains(
                        "DROPPED_CONFIRMED_EDGE_EVIDENCE:"
                                + producerInstance + ":REGION.1.in.0"
                                + ":EDGE.DROPPED"));
        assertEquals(result.manifest.toString(), "CANDIDATE_WITH_GAPS",
                result.manifest.get("state").getAsString());
    }

    /**
     * The audit reuses the shared admission gate and never widens it.  An
     * edge the gate rejects could not have bound anything, so naming it
     * would be a false alarm.  With nothing to report the composed query is
     * byte-identical to the same composition audited against nothing, so
     * switching the audit on cannot move a relation that already held.
     */
    @Test
    public void unconfirmedEdgeEvidenceLeavesTheFreeInputUnreported()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.INPUT", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        JsonObject input = new JsonObject();
        input.addProperty("_type", "SymbolExpression");
        input.addProperty("_java_type", "I");
        input.addProperty("_exp", "REGION.1.in.0");

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(summary("INPUT", producerInstance,
                        20, input,
                        Collections.singletonList("REGION.1.in.0"),
                        Collections.singletonList(edge))),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)),
                new JsonArray(),
                Collections.singletonList(validatedEdge("EDGE.UNPROVEN",
                        "OBSERVED_RUNTIME_CANDIDATE", "REGION.1.out.0",
                        "REGION.1.in.0")),
                edge);

        assertEquals(result.manifest.toString(), "AUDITED",
                result.manifest.get("droppedEdgeEvidenceAudit")
                        .getAsString());
        assertFalse(result.manifest.toString(),
                result.manifest.toString().contains(
                        "DROPPED_CONFIRMED_EDGE_EVIDENCE"));
        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());

        ConcolicSmtComposer.Result unaudited = compose(fatalInstance,
                Collections.singletonList(summary("INPUT", producerInstance,
                        20, input,
                        Collections.singletonList("REGION.1.in.0"),
                        Collections.singletonList(edge))),
                edge);
        assertEquals(unaudited.smtLib, result.smtLib);
    }

    /**
     * Without the validated edge artifact the audit cannot run.  It says so
     * in the manifest instead of leaving the freedom silently unexamined.
     */
    @Test
    public void missingEdgeArtifactIsNamedRatherThanSilentlySkipped()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.INPUT", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        JsonObject input = new JsonObject();
        input.addProperty("_type", "SymbolExpression");
        input.addProperty("_java_type", "I");
        input.addProperty("_exp", "REGION.1.in.0");

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(summary("INPUT", producerInstance,
                        20, input,
                        Collections.singletonList("REGION.1.in.0"),
                        Collections.singletonList(edge))),
                edge);

        assertEquals(result.manifest.toString(),
                "EDGE_VALIDATIONS_NOT_SUPPLIED",
                result.manifest.get("droppedEdgeEvidenceAudit")
                        .getAsString());
    }

    @Test
    public void oneDeclaredArrayFieldReachesOneContainerEquality()
            throws Exception {
        // Both ends of this edge are the same declared byte[] field, but only
        // the producer was refined to a container by the value it bound.  The
        // consumer input nothing refined must reach the same container sort
        // instead of a sort mismatch.
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.BYTES", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 10, 11);

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(summary("BYTES", producerInstance,
                        20, indexedState("AL_2-0", 4),
                        Collections.singletonList("REGION.1.in.0"),
                        Collections.singletonList(edge))),
                Arrays.asList(
                        activationRegion("REGION.0", "REGION.0.in.0", true,
                                "<Test: byte[] nonce>"),
                        activationRegion("REGION.1", "REGION.1.out.0", false,
                                "<Test: byte[] nonce>")),
                edge);

        assertFalse(result.manifest.toString(),
                result.manifest.toString().contains("PortSortMismatch"));
        assertFalse(result.manifest.toString(),
                result.manifest.toString().contains(
                        "ArrayPortJavaTypeMismatch"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const port__REGION_0_in_0__instance__"
                        + "REGION_0_Test_call30 IndexedState)"));
    }

    @Test
    public void differentDeclaredFieldTypesKeepTheSortMismatch()
            throws Exception {
        // A neutral port is only sharpened when both ends name the same
        // declared type.  Differing declarations decide nothing.
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.BYTES", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 10, 11);

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(summary("BYTES", producerInstance,
                        20, indexedState("AL_2-0", 4),
                        Collections.singletonList("REGION.1.in.0"),
                        Collections.singletonList(edge))),
                Arrays.asList(
                        activationRegion("REGION.0", "REGION.0.in.0", true,
                                "<Test: int[] lengths>"),
                        activationRegion("REGION.1", "REGION.1.out.0", false,
                                "<Test: byte[] nonce>")),
                edge);

        assertTrue(result.manifest.toString(),
                result.manifest.toString().contains("PortSortMismatch"));
    }

    /** One region whose port records only the field path it walked. */
    private static JsonObject activationRegion(
            String id, String portId, boolean input, String declaration) {
        JsonObject port = new JsonObject();
        port.addProperty("portId", portId);
        port.addProperty("cell", "<Test: void activation()>#u10"
                + ".fieldReceiver");
        JsonArray declarations = new JsonArray();
        declarations.add(declaration);
        port.add("fieldPathDeclarations", declarations);

        JsonObject region = new JsonObject();
        region.addProperty("regionId", id);
        JsonArray inputs = new JsonArray();
        JsonArray outputs = new JsonArray();
        if (input) {
            inputs.add(port);
        } else {
            outputs.add(port);
            inputs.add(port(id + ".in.0", true, "int"));
        }
        region.add("symbolicInputs", inputs);
        region.add("outputs", outputs);
        return region;
    }

    @Test
    public void concreteReferenceIdentityBindsTheAliasItRecorded()
            throws Exception {
        // The producer never symbolised this reference; it recorded which
        // object it handed on.  Naming that object is the whole relation, so
        // the port is bound to it and nothing else is demanded of the closure.
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.REF", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 10, 11);

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(referenceIdentitySummary(
                        producerInstance, edge, false)),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)), edge);

        assertFalse(result.manifest.toString(),
                result.manifest.toString().contains(
                        "ConcreteReferenceIdentityWithoutLeafProducer"));
        assertTrue(result.smtLib,
                result.smtLib.contains("reference_identity__"));
        assertTrue(result.smtLib, result.smtLib.contains("nullRef"));
    }

    @Test
    public void demandedLeafWithoutProducerStillFailsClosed()
            throws Exception {
        // The alias says which object was handed on and nothing about what is
        // inside it.  A second demanded output with no producer is exactly the
        // leaf the alias cannot answer, so it is still reported by name.
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.REF", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 10, 11);

        JsonObject producerRegion = region("REGION.1", true, true);
        producerRegion.getAsJsonArray("outputs").add(
                port("REGION.1.out.1", false, "java.util.Map"));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(referenceIdentitySummary(
                        producerInstance, edge, true)),
                Arrays.asList(region("REGION.0", true, false),
                        producerRegion), edge);

        assertTrue(result.manifest.toString(),
                result.manifest.toString().contains(
                        "ConcreteReferenceIdentityWithoutLeafProducer@"
                                + "REGION.1:REGION.1.out.1"));
    }

    private static RelationSummary referenceIdentitySummary(
            String instance, JsonObject edge, boolean demandUnboundLeaf) {
        JsonObject slice = emptySlice("REGION.1.out.0",
                "<Test: int output>");
        OutputClosureContract closure;
        if (demandUnboundLeaf) {
            JsonObject leafSlice = emptySlice("REGION.1.out.1",
                    "<Test: java.util.Map leaf>");
            closure = OutputClosureCodec.decode(joint(instance, slice,
                    leafSlice));
        } else {
            closure = OutputClosureCodec.singleton("REGION.1", instance, 20,
                    "REGION.1.out.0", "<Test: int output>", "REGION_OUTPUT",
                    "int", slice);
        }

        JsonObject row = new JsonObject();
        row.addProperty("summaryId", "SUMMARY.REF");
        row.addProperty("regionId", "REGION.1");
        row.addProperty("regionInstanceId", instance);
        row.addProperty("rootCallId", 20);
        OutputClosureCodec.writeTo(row, closure);
        JsonArray bindings = new JsonArray();
        bindings.add(edge.deepCopy());
        row.add("edgeBindings", bindings);

        JsonObject identity = new JsonObject();
        identity.addProperty("authority",
                "CONCRETE_REFERENCE_IDENTITY_RELATION_V1");
        identity.addProperty("fieldSignature", "<Test: Held held>");
        identity.addProperty("javaType", "Test$Held");
        identity.addProperty("runtimeType", "Test$Held");
        identity.addProperty("objectId", 1);
        JsonObject identities = new JsonObject();
        identities.add("REGION.1.out.0", identity);

        JsonObject path = new JsonObject();
        path.addProperty("caseId", "CASE.REF");
        path.addProperty("sourceTaskId", "TASK.REF");
        JsonObject guard = new JsonObject();
        guard.addProperty("kind", "PATH_CONDITION");
        guard.add("conditions", new JsonArray());
        path.add("guard", guard);
        JsonObject expressions = new JsonObject();
        if (demandUnboundLeaf) {
            // A demanded leaf whose recorded value cannot bind its scalar
            // port has no producer the composition can use.
            expressions.add("REGION.1.out.1", indexedState("AL_9-0", 2));
        }
        path.add("outputExpressions", expressions);
        path.add("outputReferenceIdentities", identities);
        JsonArray cases = new JsonArray();
        cases.add(path);
        JsonObject relation = new JsonObject();
        relation.addProperty("schemaVersion", 1);
        relation.addProperty("kind", "GUARDED_PATH_MERGE");
        relation.add("cases", cases);
        row.add("regionRelation", relation);
        row.addProperty("relationallyComplete", true);
        return RelationSummary.decode(row);
    }

    private static JsonObject joint(String instance, JsonObject... slices) {
        JsonObject producer = new JsonObject();
        producer.addProperty("regionId", "REGION.1");
        producer.addProperty("regionInstanceId", instance);
        producer.addProperty("rootCallId", 20);
        JsonArray members = new JsonArray();
        for (JsonObject slice : slices) {
            JsonObject output = new JsonObject();
            output.addProperty("portId",
                    slice.get("outputPort").getAsString());
            output.addProperty("cell",
                    slice.get("outputCell").getAsString());
            output.addProperty("kind", "REGION_OUTPUT");
            output.addProperty("javaTypeDescriptor",
                    slice.get("outputCell").getAsString().contains("Map")
                            ? "Ljava/util/Map;" : "I");
            JsonObject member = new JsonObject();
            member.add("output", output);
            JsonObject memberSlice = slice.deepCopy();
            memberSlice.remove("causalEdges");
            member.add("slice", memberSlice);
            members.add(member);
        }
        JsonObject closure = new JsonObject();
        closure.addProperty("schemaVersion", 2);
        closure.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        closure.add("producer", producer);
        closure.add("causalEdges", new JsonArray());
        closure.add("members", members);
        JsonObject row = new JsonObject();
        row.add("outputClosure", closure);
        return row;
    }

    @Test
    public void mergedCaseOutputExpressionReachesTheStringCodec()
            throws Exception {
        // A merged relation publishes output expressions per guarded case,
        // never at the summary root.  The producer builds the SASL username
        // concat(toString(keyId), " ", pool, " ", nonce); the consumer splits
        // it and parses element zero out of the split array.  Reading the
        // case expression is what lets the codec prove that round trip.
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = protocolBinding("EDGE.NAME", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0",
                10, 11, 12);

        JsonObject keyId = new JsonObject();
        keyId.addProperty("_type", "SymbolExpression");
        keyId.addProperty("_java_type", "I");
        keyId.addProperty("_exp", "REGION.1.in.0");
        JsonObject username = strConcat(strToString(keyId), strLiteral(" "),
                strLiteral("BP-x"), strLiteral(" "), strLiteral("nonce"));

        JsonObject consumed = new JsonObject();
        consumed.addProperty("_type", "SymbolExpression");
        consumed.addProperty("_java_type", "java/lang/String");
        consumed.addProperty("_exp", "REGION.0.in.0");
        JsonObject parts = indexedWrite(indexedWrite(indexedWrite(
                indexedState("AL_5-0", 3),
                0, splitElement(consumed, " ", 0)),
                1, splitElement(consumed, " ", 1)),
                2, splitElement(consumed, " ", 2));

        JsonArray constraints = new JsonArray();
        constraints.add(binary(indexedSize(parts), "==", integer(3)));
        constraints.add(binary(parseInt(indexedRead(parts, 0)), "==",
                integer(11745)));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(summary("USERNAME",
                        producerInstance, 20, username,
                        Collections.singletonList("REGION.1.in.0"),
                        Collections.singletonList(edge),
                        "java.lang.String")),
                Arrays.asList(region("REGION.0", "java.lang.String", ""),
                        region("REGION.1", "int", "java.lang.String")),
                constraints, edge);

        assertFalse(result.manifest.toString(),
                result.manifest.toString().contains(
                        "MODEL_SEMANTICS_MISSING"));
        assertTrue(result.smtLib,
                result.smtLib.contains("java_int_to_string"));
    }

    @Test
    public void splitElementIntegerNamesTheProducersOwnPortWitness()
            throws Exception {
        // The rendered int belongs to the producer's relation, so it must be
        // lowered onto the producer invocation's port witness.  Reading it in
        // the fatal invocation would mint a second, unconstrained occurrence
        // of the same port and let the solver pick any value for it.
        ConcolicSmtComposer.Result result = composeUsername(0);

        assertFalse(result.manifest.toString(),
                result.manifest.toString().contains(
                        "MODEL_SEMANTICS_MISSING"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "sym__port__REGION_1_Test_call20_REGION_1_in_0__int"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "sym__port__REGION_0_Test_call30_REGION_1_in_0__int"));
    }

    @Test
    public void splitElementKeepsGapForAProducerLocalInteger()
            throws Exception {
        // A region local symbol is named only inside the invocation that
        // stated it.  There is no witness for it to enter, so the codec must
        // keep its gap rather than invent a free integer here.
        JsonObject local = new JsonObject();
        local.addProperty("_type", "SymbolExpression");
        local.addProperty("_java_type", "I");
        local.addProperty("_exp", "M_I_local");
        JsonObject username = strConcat(strToString(local), strLiteral(" "),
                strLiteral("BP-x"), strLiteral(" "), strLiteral("nonce"));

        ConcolicSmtComposer.Result result = composeUsername(username, 0);

        assertTrue(result.manifest.toString(),
                result.manifest.toString().contains(
                        "java/lang/String.splitElement:"
                                + "PRODUCER_INT_NOT_PORT_BACKED"));
    }

    @Test
    public void splitElementProvesAnElementPastTheFirst() throws Exception {
        // concat(toString(keyId), " ", "BP-x", " ", "nonce") splits on the
        // space into three elements.  Element one is the literal between the
        // first and second delimiter; the integer rendering before it cannot
        // contain a space, so the segmentation is decided.
        ConcolicSmtComposer.Result result = composeUsername(1);

        assertFalse(result.manifest.toString(),
                result.manifest.toString().contains(
                        "MODEL_SEMANTICS_MISSING"));
        assertTrue(result.smtLib, result.smtLib.contains("\"BP-x\""));
    }

    @Test
    public void splitElementSegmentsOnDelimitersInsideOneLiteral()
            throws Exception {
        // The delimiters live inside a single literal part, so segmentation
        // has to look through the literal's own characters rather than only
        // at part boundaries.
        JsonObject username = strConcat(strLiteral("a b c"));
        ConcolicSmtComposer.Result result = composeUsername(username, 1);

        assertFalse(result.manifest.toString(),
                result.manifest.toString().contains(
                        "MODEL_SEMANTICS_MISSING"));
        assertTrue(result.smtLib, result.smtLib.contains("\"b\""));
    }

    @Test
    public void splitElementKeepsGapWhenAnEarlierPartMayHoldTheDelimiter()
            throws Exception {
        // A symbolic String before the requested element could itself
        // contain a space, so which characters element one holds is not
        // decided and the gap stays.
        JsonObject opaque = new JsonObject();
        opaque.addProperty("_type", "SymbolExpression");
        opaque.addProperty("_java_type", "java/lang/String");
        opaque.addProperty("_exp", "REGION.1.in.1");
        JsonObject username = strConcat(opaque, strLiteral(" "),
                strLiteral("BP-x"), strLiteral(" "), strLiteral("nonce"));

        ConcolicSmtComposer.Result result = composeUsername(username, 1);

        assertTrue(result.manifest.toString(),
                result.manifest.toString().contains(
                        "java/lang/String.splitElement:"
                                + "PART_NOT_PROVABLY_DELIMITER_FREE"));
    }

    @Test
    public void splitElementProvesAnEmptyElementBetweenDelimiters()
            throws Exception {
        // Two adjacent delimiters produce an element Java keeps and that has
        // no characters; that is decided, not unknown.
        JsonObject username = strConcat(strLiteral("a  b"));

        ConcolicSmtComposer.Result result = composeUsername(username, 1);

        assertFalse(result.manifest.toString(),
                result.manifest.toString().contains(
                        "MODEL_SEMANTICS_MISSING"));
    }

    @Test
    public void splitElementKeepsGapForATrailingElement() throws Exception {
        // The last element is not closed by a delimiter, and Java drops a
        // trailing element that turned out empty, so nothing decides it
        // unless the walk proves it has characters.
        JsonObject username = strConcat(strLiteral("a"), strLiteral(" "));

        ConcolicSmtComposer.Result result = composeUsername(username, 1);

        assertTrue(result.manifest.toString(),
                result.manifest.toString().contains(
                        "java/lang/String.splitElement:"
                                + "TRAILING_ELEMENT_MAY_BE_EMPTY"));
    }

    private ConcolicSmtComposer.Result composeUsername(int index)
            throws Exception {
        JsonObject keyId = new JsonObject();
        keyId.addProperty("_type", "SymbolExpression");
        keyId.addProperty("_java_type", "I");
        keyId.addProperty("_exp", "REGION.1.in.0");
        return composeUsername(strConcat(strToString(keyId), strLiteral(" "),
                strLiteral("BP-x"), strLiteral(" "), strLiteral("nonce")),
                index);
    }

    /** Composes the SASL username round trip reading one split element. */
    private ConcolicSmtComposer.Result composeUsername(
            JsonObject username, int index) throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = protocolBinding("EDGE.NAME", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0",
                10, 11, 12);

        JsonObject consumed = new JsonObject();
        consumed.addProperty("_type", "SymbolExpression");
        consumed.addProperty("_java_type", "java/lang/String");
        consumed.addProperty("_exp", "REGION.0.in.0");
        // A bare split call is its own constraint: the recorded element is
        // asserted equal to the element the codec derives.
        JsonArray constraints = new JsonArray();
        constraints.add(splitElement(consumed, " ", index));

        return compose(fatalInstance,
                Collections.singletonList(summary("USERNAME",
                        producerInstance, 20, username,
                        Collections.singletonList("REGION.1.in.0"),
                        Collections.singletonList(edge),
                        "java.lang.String")),
                Arrays.asList(region("REGION.0", "java.lang.String", ""),
                        region("REGION.1", "int", "java.lang.String")),
                constraints, edge);
    }

    @Test
    public void aBooleanTestedAgainstTheIntLiteralZeroIsNotASortConflict()
            throws Exception {
        // The JVM has no boolean comparison, so `if (!it.hasNext())`
        // reaches the composer as a boolean compared with the int literal
        // 0.  Calling that a sort conflict drops the guard and forces its
        // case selector false, which alone makes the candidate unsat.
        JsonObject flag = new JsonObject();
        flag.addProperty("_type", "SymbolExpression");
        flag.addProperty("_java_type", "Z");
        flag.addProperty("_exp", "REGION.1.in.0");
        JsonArray constraints = new JsonArray();
        constraints.add(binary(flag, "!=", integer(0)));

        ConcolicSmtComposer.Result result = composeWithConstraints(
                constraints);

        assertFalse(result.manifest.toString(),
                result.manifest.toString().contains("BinarySortConflict"));
        assertTrue(result.smtLib, result.smtLib.contains("(not "));
    }

    @Test
    public void literalIndexedReadSelectsOnlyTheStoredElement()
            throws Exception {
        // select-over-store: reading index zero cannot observe what a write
        // to index one stored, so an unprovable sibling element must not
        // reach the encoder and must not be reported as a proof gap.
        JsonArray constraints = new JsonArray();
        constraints.add(binary(indexedRead(indexedWrite(indexedWrite(
                indexedState("AL_1-0", 2), 0, integer(7)),
                1, unprovableMethod()), 0), "==", integer(7)));

        ConcolicSmtComposer.Result result = composeWithConstraints(
                constraints);

        assertFalse(result.manifest.toString(),
                result.manifest.toString().contains(
                        "MODEL_SEMANTICS_MISSING"));
    }

    @Test
    public void indexedSizeSkipsSizePreservingWrites() throws Exception {
        // indexed_write rebuilds the state with indexed_size unchanged, so a
        // size query never observes the written elements.
        JsonArray constraints = new JsonArray();
        constraints.add(binary(indexedSize(indexedWrite(
                indexedState("AL_1-0", 2), 0, unprovableMethod())),
                "==", integer(2)));

        ConcolicSmtComposer.Result result = composeWithConstraints(
                constraints);

        assertFalse(result.manifest.toString(),
                result.manifest.toString().contains(
                        "MODEL_SEMANTICS_MISSING"));
    }

    @Test
    public void undecidableIndexedReadKeepsEveryStoredElement()
            throws Exception {
        // A read whose index is not an exact literal decides nothing, so the
        // ordinary select-over-store encoding is kept and every stored
        // element still has to be encoded - gaps included.
        JsonObject symbolicIndex = new JsonObject();
        symbolicIndex.addProperty("_type", "SymbolExpression");
        symbolicIndex.addProperty("_java_type", "I");
        symbolicIndex.addProperty("_exp", "REGION.0.in.0");
        JsonArray constraints = new JsonArray();
        constraints.add(binary(indexedRead(indexedWrite(indexedWrite(
                indexedState("AL_1-0", 2), 0, integer(7)),
                1, unprovableMethod()), symbolicIndex), "==", integer(7)));

        ConcolicSmtComposer.Result result = composeWithConstraints(
                constraints);

        assertTrue(result.manifest.toString(),
                result.manifest.toString().contains(
                        "MODEL_SEMANTICS_MISSING"));
    }

    @Test
    public void undecidableStoredIndexKeepsEveryStoredElement()
            throws Exception {
        // The same holds when a write's own index is not a literal: it might
        // be the index being read, so nothing below it may be selected.
        JsonObject symbolicIndex = new JsonObject();
        symbolicIndex.addProperty("_type", "SymbolExpression");
        symbolicIndex.addProperty("_java_type", "I");
        symbolicIndex.addProperty("_exp", "REGION.0.in.0");
        JsonObject writes = indexedWrite(
                indexedState("AL_1-0", 2), 0, integer(7));
        writes = indexedWriteAt(writes, symbolicIndex, unprovableMethod());
        JsonArray constraints = new JsonArray();
        constraints.add(binary(indexedRead(writes, 0), "==", integer(7)));

        ConcolicSmtComposer.Result result = composeWithConstraints(
                constraints);

        assertTrue(result.manifest.toString(),
                result.manifest.toString().contains(
                        "MODEL_SEMANTICS_MISSING"));
    }

    @Test
    public void anOmittedContainerValueIsNamedRatherThanReadAsJavaNull()
            throws Exception {
        // A recording states a null reference with its own null symbol, so
        // an operand it simply left out says nothing at all.  Reading the
        // omission as null would decide every later read of that entry -
        // the entry is provably null, so it can never be a String - which
        // is the strongest possible claim from the weakest evidence.
        JsonObject key = new JsonObject();
        key.addProperty("_type", "SymbolExpression");
        key.addProperty("_java_type", "java/lang/String");
        key.addProperty("_exp", "P_L'java/lang/String'_");

        JsonArray omitted = new JsonArray();
        omitted.add(binary(associativeRead(associativeOperation("PUT",
                associativeState("M_1"), key, null), key, "L"),
                "!=", recordedNull()));
        ConcolicSmtComposer.Result gapped =
                composeWithConstraints(omitted);

        JsonArray recorded = new JsonArray();
        recorded.add(binary(associativeRead(associativeOperation("PUT",
                associativeState("M_1"), key, recordedNull()), key, "L"),
                "!=", recordedNull()));
        ConcolicSmtComposer.Result stated =
                composeWithConstraints(recorded);

        assertTrue(gapped.manifest.toString(),
                gapped.manifest.toString().contains("ABSENT_EXPRESSION"));
        assertFalse(stated.manifest.toString(),
                stated.manifest.toString().contains("ABSENT_EXPRESSION"));
    }

    /** The recorder's own encoding of a null reference. */
    private static JsonObject recordedNull() {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "");
        expression.addProperty("_exp", "N");
        return expression;
    }

    private ConcolicSmtComposer.Result composeWithConstraints(
            JsonArray constraints) throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.0", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 10, 11);
        return compose(fatalInstance,
                Collections.singletonList(summary("PLAIN", producerInstance,
                        20, 7, Collections.singletonList("REGION.1.in.0"),
                        Collections.singletonList(edge))),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)),
                constraints, edge);
    }

    private static JsonObject unprovableMethod() {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "MethodExpression");
        expression.addProperty("_name", "java/lang/Object hashCode");
        expression.add("_param_list", new JsonArray());
        expression.add("_res_exp", integer(3));
        return expression;
    }

    private static JsonObject indexedState(String reference, int size) {
        JsonObject receiver = new JsonObject();
        receiver.addProperty("_type", "SymbolExpression");
        receiver.addProperty("_java_type", "L");
        receiver.addProperty("_exp", reference);
        JsonObject expression = new JsonObject();
        expression.addProperty("_type",
                ContainerSmtCodec.EXPRESSION_TYPE);
        expression.addProperty("shape", "INDEXED");
        expression.addProperty("operation", "STATE");
        expression.addProperty("_java_type", "L");
        expression.add("receiver", receiver);
        JsonArray arguments = new JsonArray();
        arguments.add(integer(size));
        expression.add("arguments", arguments);
        return expression;
    }

    private static JsonObject indexedWrite(JsonObject receiver, int index,
                                           JsonObject value) {
        return indexedWriteAt(receiver, integer(index), value);
    }

    private static JsonObject indexedWriteAt(JsonObject receiver,
                                             JsonObject index,
                                             JsonObject value) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type",
                ContainerSmtCodec.EXPRESSION_TYPE);
        expression.addProperty("shape", "INDEXED");
        expression.addProperty("operation", "WRITE");
        expression.addProperty("_java_type", "L");
        expression.add("receiver", receiver);
        JsonArray arguments = new JsonArray();
        arguments.add(index);
        arguments.add(value);
        expression.add("arguments", arguments);
        return expression;
    }

    private static JsonObject indexedRead(JsonObject receiver, int index) {
        return indexedRead(receiver, integer(index));
    }

    private static JsonObject indexedRead(JsonObject receiver,
                                          JsonObject index) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type",
                ContainerSmtCodec.EXPRESSION_TYPE);
        expression.addProperty("shape", "INDEXED");
        expression.addProperty("operation", "READ");
        expression.addProperty("_java_type", "Ljava/lang/String;");
        expression.add("receiver", receiver);
        JsonArray arguments = new JsonArray();
        arguments.add(index);
        expression.add("arguments", arguments);
        return expression;
    }

    private static JsonObject indexedSize(JsonObject receiver) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type",
                ContainerSmtCodec.EXPRESSION_TYPE);
        expression.addProperty("shape", "INDEXED");
        expression.addProperty("operation", "SIZE");
        expression.addProperty("_java_type", "I");
        expression.add("receiver", receiver);
        expression.add("arguments", new JsonArray());
        return expression;
    }

    private static JsonObject strLiteral(String content) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "ConStringSymbolExp");
        expression.addProperty("_java_type", "java/lang/String");
        expression.addProperty("_exp", "Y_L'String'_" + content);
        return expression;
    }

    private static JsonObject strToString(JsonObject value) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "OpStrExpression");
        expression.addProperty("_name", "toString");
        JsonArray params = new JsonArray();
        params.add(value);
        expression.add("_param_list", params);
        return expression;
    }

    private static JsonObject strConcat(JsonObject... parts) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "OpStrExpression");
        expression.addProperty("_name", "concat");
        JsonArray params = new JsonArray();
        for (JsonObject part : parts) params.add(part);
        expression.add("_param_list", params);
        return expression;
    }

    private static JsonObject splitElement(JsonObject receiver,
                                           String delimiter, int index) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "MethodExpression");
        expression.addProperty("_name", "java/lang/String splitElement");
        JsonArray params = new JsonArray();
        params.add(receiver);
        params.add(strLiteral(delimiter));
        params.add(integer(index));
        expression.add("_param_list", params);
        expression.add("_res_exp", strLiteral("element"));
        return expression;
    }

    private static JsonObject parseInt(JsonObject text) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "MethodExpression");
        expression.addProperty("_name", "java/lang/Integer parseInt");
        JsonArray params = new JsonArray();
        params.add(text);
        expression.add("_param_list", params);
        expression.add("_res_exp", integer(11745));
        return expression;
    }

    private ConcolicSmtComposer.Result compose(
            String fatalInstance, java.util.List<RelationSummary> summaries,
            JsonObject... firstHops) throws Exception {
        return compose(fatalInstance, summaries,
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)), firstHops);
    }

    private ConcolicSmtComposer.Result compose(
            String fatalInstance, java.util.List<RelationSummary> summaries,
            java.util.List<JsonObject> regionRows,
            JsonObject... firstHops) throws Exception {
        return compose(fatalInstance, summaries, regionRows,
                new JsonArray(), firstHops);
    }

    private ConcolicSmtComposer.Result compose(
            String fatalInstance, java.util.List<RelationSummary> summaries,
            java.util.List<JsonObject> regionRows, JsonArray constraints,
            JsonObject... firstHops) throws Exception {
        return compose(fatalInstance, summaries, regionRows, constraints,
                null, firstHops);
    }

    private ConcolicSmtComposer.Result compose(
            String fatalInstance, java.util.List<RelationSummary> summaries,
            java.util.List<JsonObject> regionRows, JsonArray constraints,
            java.util.List<JsonObject> edgeValidations,
            JsonObject... firstHops) throws Exception {
        Path directory = temporary.newFolder().toPath();
        Path fatal = directory.resolve("fatal.jsonl");
        Path summaryFile = directory.resolve("summaries.jsonl");
        Path regions = directory.resolve("regions.jsonl");
        Path output = directory.resolve("candidate.smt2");
        Path manifest = directory.resolve("manifest.json");

        writeJsonl(fatal, fatalQuery(fatalInstance, constraints, firstHops));
        StringBuilder encoded = new StringBuilder();
        for (RelationSummary summary : summaries) {
            encoded.append(summary.toJson()).append('\n');
        }
        Files.write(summaryFile, encoded.toString().getBytes(
                StandardCharsets.UTF_8));
        writeJsonl(regions, regionRows.toArray(
                new JsonObject[regionRows.size()]));

        java.util.List<String> argv = new java.util.ArrayList<>(
                Arrays.asList(
                        "--fatal-query", fatal.toString(),
                        "--summaries", summaryFile.toString(),
                        "--regions", regions.toString(),
                        "--output", output.toString(),
                        "--manifest", manifest.toString(),
                        "--fatal-region", "REGION.0",
                        "--region-instance-id", fatalInstance));
        if (edgeValidations != null) {
            Path validations = directory.resolve("edge_validations.jsonl");
            writeJsonl(validations, edgeValidations.toArray(
                    new JsonObject[edgeValidations.size()]));
            argv.add("--edge-validations");
            argv.add(validations.toString());
        }
        return ConcolicSmtComposer.compose(
                ConcolicSmtComposer.Arguments.parse(
                        argv.toArray(new String[argv.size()])));
    }

    /**
     * One validated runtime edge row, admissible to the shared evidence
     * gate.  {@code state} is a parameter so a test can hand the audit an
     * edge the gate rejects and check that it stays silent.
     */
    private static JsonObject validatedEdge(String edgeId, String state,
                                            String fromPort, String toPort) {
        JsonObject edge = new JsonObject();
        edge.addProperty("schemaVersion", 3);
        edge.addProperty("kind", "RUNTIME_FIELD_FLOW");
        edge.addProperty("state", state);
        edge.addProperty("transportKind", "HEAP");
        edge.addProperty("edgeId", edgeId);
        edge.addProperty("fromRegion", regionOf(fromPort));
        edge.addProperty("toRegion", regionOf(toPort));
        edge.addProperty("fromPort", fromPort);
        edge.addProperty("toPort", toPort);
        JsonArray bindings = new JsonArray();
        bindings.add(binding(edgeId, "REGION.1@Test#call10", fromPort,
                "REGION.1@Test#call20", toPort, 10, 20));
        edge.add("bindings", bindings);
        return edge;
    }

    private static RelationSummary summary(
            String id, String instance, long call, int value,
            java.util.List<String> inputPorts,
            java.util.List<JsonObject> bindings) {
        return summary(id, instance, call, integer(value), inputPorts,
                bindings);
    }

    private static RelationSummary summary(
            String id, String instance, long call, JsonObject output,
            java.util.List<String> inputPorts,
            java.util.List<JsonObject> bindings) {
        return summary(id, instance, call, output, inputPorts, bindings,
                "int");
    }

    private static RelationSummary summary(
            String id, String instance, long call, JsonObject output,
            java.util.List<String> inputPorts,
            java.util.List<JsonObject> bindings, String outputJavaType) {
        JsonObject slice = emptySlice("REGION.1.out.0",
                "<Test: " + outputJavaType + " output>");
        JsonArray inputs = new JsonArray();
        for (String input : inputPorts) inputs.add(input);
        slice.add("inputPorts", inputs);
        OutputClosureContract closure = OutputClosureCodec.singleton(
                "REGION.1", instance, call, "REGION.1.out.0",
                "<Test: " + outputJavaType + " output>", "REGION_OUTPUT",
                outputJavaType, slice);

        JsonObject row = new JsonObject();
        row.addProperty("summaryId", "SUMMARY." + id);
        row.addProperty("regionId", "REGION.1");
        row.addProperty("regionInstanceId", instance);
        row.addProperty("rootCallId", call);
        OutputClosureCodec.writeTo(row, closure);
        JsonArray encodedBindings = new JsonArray();
        for (JsonObject binding : bindings) {
            encodedBindings.add(binding.deepCopy());
        }
        row.add("edgeBindings", encodedBindings);
        JsonObject relation = new JsonObject();
        relation.addProperty("schemaVersion", 1);
        relation.addProperty("kind", "GUARDED_PATH_MERGE");
        JsonObject path = new JsonObject();
        path.addProperty("caseId", "CASE." + id);
        path.addProperty("sourceTaskId", "TASK." + id);
        JsonObject guard = new JsonObject();
        guard.addProperty("kind", "PATH_CONDITION");
        guard.add("conditions", new JsonArray());
        path.add("guard", guard);
        JsonObject outputs = new JsonObject();
        outputs.add("REGION.1.out.0", output);
        path.add("outputExpressions", outputs);
        JsonArray cases = new JsonArray();
        cases.add(path);
        relation.add("cases", cases);
        row.add("regionRelation", relation);
        row.addProperty("relationallyComplete", true);
        return RelationSummary.decode(row);
    }

    private static RelationSummary logicalSummary(
            RelationSummary canonical, JsonObject... occurrences) {
        JsonObject row = canonical.toJson();
        row.addProperty("logicalRegionId", "REGION.1@owner7");
        row.addProperty("summaryReuseKey", "REGION.1@owner7");
        JsonObject catalog = new JsonObject();
        catalog.addProperty("schemaVersion", 1);
        catalog.addProperty("kind",
                "LOGICAL_SUMMARY_OCCURRENCE_CATALOG");
        catalog.addProperty("logicalRegionId", "REGION.1@owner7");
        catalog.addProperty("summaryReuseKey", "REGION.1@owner7");
        catalog.addProperty("canonicalRegionInstanceId",
                canonical.regionInstanceId());
        catalog.addProperty("canonicalRootCallId",
                canonical.outputClosure().producer().rootCallId());
        JsonArray encoded = new JsonArray();
        for (JsonObject occurrence : occurrences) encoded.add(occurrence);
        catalog.add("occurrences", encoded);
        row.add("occurrenceInstantiationCatalog", catalog);
        return RelationSummary.decode(row);
    }

    private static JsonObject occurrence(
            String instance, long rootCall, String exactInput,
            String exactOutput, String... bindingIds) {
        JsonObject occurrence = new JsonObject();
        occurrence.addProperty("regionInstanceId", instance);
        occurrence.addProperty("rootCallId", rootCall);
        occurrence.addProperty("ownerId", 7);
        occurrence.addProperty("laneId", rootCall);
        occurrence.addProperty("spanId", rootCall + 100);
        JsonObject input = new JsonObject();
        input.addProperty("canonicalPort", "REGION.1.in.0");
        input.addProperty("exactPort", exactInput);
        JsonArray inputs = new JsonArray();
        inputs.add(input);
        occurrence.add("inputPortMap", inputs);
        JsonObject output = new JsonObject();
        output.addProperty("canonicalPort", "REGION.1.out.0");
        output.addProperty("exactPort", exactOutput);
        JsonArray outputs = new JsonArray();
        outputs.add(output);
        occurrence.add("outputPortMap", outputs);
        JsonArray bindings = new JsonArray();
        for (String id : bindingIds) bindings.add(id);
        occurrence.add("bindingIds", bindings);
        return occurrence;
    }

    private static JsonObject emptySlice(String port, String cell) {
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        slice.add("methods", new JsonArray());
        slice.add("causalEdgeIds", new JsonArray());
        slice.add("captureBindings", new JsonArray());
        slice.add("captureBindingIssues", new JsonArray());
        slice.add("causalEdges", new JsonArray());
        return slice;
    }

    private static JsonObject fatalQuery(
            String fatalInstance, JsonArray constraints,
            JsonObject... firstHops) {
        JsonObject fatal = new JsonObject();
        fatal.addProperty("schemaVersion", 1);
        fatal.addProperty("kind", "TARGET_REACH_PATH_SET_QUERY");
        fatal.addProperty("regionId", "REGION.0");
        fatal.addProperty("regionInstanceId", fatalInstance);
        fatal.addProperty("targetSiteId", "<Test: void consume()>#u1");
        fatal.addProperty("constraintAuthority",
                "CLOSED_IMPORTED_TARGET_REACH_PATH_SET_V1");
        JsonObject path = new JsonObject();
        path.add("constraints", constraints.deepCopy());
        JsonArray paths = new JsonArray();
        paths.add(path);
        fatal.add("paths", paths);
        JsonObject metadata = new JsonObject();
        metadata.addProperty("predicateNormalization", "IDENTITY");
        BranchWitness witness = BranchWitness.vmPc(
                "<Test: void consume()>#u1", "<Test: void consume()>",
                1, 1, false, binary(integer(0), "==", integer(0)),
                0, metadata);
        fatal.add("seedReplayContract", BranchReplayContract.flip(
                Collections.<BranchWitness>emptyList(), witness).toJson());

        JsonArray merges = new JsonArray();
        JsonArray equalities = new JsonArray();
        for (JsonObject firstHop : firstHops) {
            JsonObject relation = new JsonObject();
            relation.addProperty("edgeId",
                    firstHop.get("edgeId").getAsString());
            relation.addProperty("fromEndpoint",
                    firstHop.get("fromOutputPort").getAsString());
            relation.addProperty("toEndpoint",
                    firstHop.get("toInputPort").getAsString());
            JsonArray selected = new JsonArray();
            selected.add(firstHop.deepCopy());
            relation.add("selectedBindings", selected);
            if ("TRUSTED_CONFIGURED_RPC_MAPPING_V1".equals(
                    firstHop.get("evidenceKind").getAsString())) {
                equalities.add(relation);
            } else {
                merges.add(relation);
            }
        }
        JsonObject context = new JsonObject();
        context.addProperty("regionInstanceId", fatalInstance);
        context.add("equalityClasses", new JsonArray());
        context.add("equalityRelations", equalities);
        context.add("versionedStateMerges", merges);
        context.add("alternativeWriterGroups", new JsonArray());
        fatal.add("symbolicContext", context);
        return fatal;
    }

    private static JsonObject binding(
            String edgeId, String fromInstance, String fromPort,
            String toInstance, String toPort, long writer, long reader) {
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", edgeId);
        binding.addProperty("fromRegion", "REGION.1");
        binding.addProperty("toRegion", regionOf(toPort));
        binding.addProperty("fromRegionInstance", fromInstance);
        binding.addProperty("toRegionInstance", toInstance);
        binding.addProperty("fromOutputPort", fromPort);
        binding.addProperty("toInputPort", toPort);
        binding.addProperty("evidenceKind",
                "FIELD_ASSIGNMENT_READ_FROM_V1");
        binding.addProperty("schemaVersion", 3);
        binding.addProperty("correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
        binding.addProperty("writerLaneId", "lane.writer");
        binding.addProperty("readerLaneId", "lane.reader");
        binding.addProperty("programOrderRequired", false);
        binding.addProperty("writerEventSeq", writer);
        binding.addProperty("readerEventSeq", reader);
        binding.addProperty("receiverObjectId", 7);
        return binding;
    }

    private static JsonObject protocolBinding(
            String edgeId, String fromInstance, String fromPort,
            String toInstance, String toPort, long caller, long send,
            long receive) {
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", edgeId);
        binding.addProperty("fromRegion", "REGION.1");
        binding.addProperty("toRegion", regionOf(toPort));
        binding.addProperty("fromRegionInstance", fromInstance);
        binding.addProperty("toRegionInstance", toInstance);
        binding.addProperty("fromOutputPort", fromPort);
        binding.addProperty("toInputPort", toPort);
        binding.addProperty("evidenceKind",
                "TRUSTED_CONFIGURED_RPC_MAPPING_V1");
        binding.addProperty("schemaVersion", 3);
        binding.addProperty("mappingId", "example.rpc");
        binding.addProperty("correlationAuthority",
                "TRUSTED_CONFIGURED_RPC_MAPPING_V1");
        binding.addProperty("callerSiteEventSeq", caller);
        binding.addProperty("sendEventSeq", send);
        binding.addProperty("receiveEventSeq", receive);
        return binding;
    }

    private static JsonObject region(
            String id, boolean hasInput, boolean hasOutput) {
        return region(id, hasInput ? "int" : "",
                hasOutput ? "int" : "");
    }

    private static JsonObject region(
            String id, String inputType, String outputType) {
        JsonObject region = new JsonObject();
        region.addProperty("regionId", id);
        JsonArray inputs = new JsonArray();
        if (!inputType.isEmpty()) {
            inputs.add(port(id + ".in.0", true, inputType));
        }
        region.add("symbolicInputs", inputs);
        JsonArray outputs = new JsonArray();
        if (!outputType.isEmpty()) {
            outputs.add(port(id + ".out.0", false, outputType));
        }
        region.add("outputs", outputs);
        return region;
    }

    private static JsonObject port(String id, boolean input) {
        return port(id, input, "int");
    }

    private static JsonObject port(
            String id, boolean input, String javaType) {
        JsonObject port = new JsonObject();
        port.addProperty("portId", id);
        port.addProperty("cell", input
                ? "<Test: " + javaType + " input>"
                : "<Test: " + javaType + " output>");
        port.addProperty("javaType", javaType);
        return port;
    }

    private static JsonObject integer(int value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConstExpr");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", "Y_I_" + value);
        return result;
    }

    private static JsonObject currentTimePlaceholder() {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "PlaceholderExpression");
        result.addProperty("_place_holder_func", "currentTimeMills");
        result.addProperty("_count", 1);
        result.addProperty("_java_type", "J");
        return result;
    }

    private static JsonObject reference(String symbol, String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", symbol);
        return result;
    }

    private static JsonObject typedIntegral(String javaType, int value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConstExpr");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", "Y_" + javaType + "_" + value);
        return result;
    }

    private static JsonObject associativeState(String symbol) {
        JsonObject identity = new JsonObject();
        identity.addProperty("_type", "SymbolExpression");
        identity.addProperty("_java_type", "L");
        identity.addProperty("_exp", symbol);
        return associativeOperation("STATE", identity);
    }

    private static JsonObject indexedState(String symbol) {
        JsonObject identity = new JsonObject();
        identity.addProperty("_type", "SymbolExpression");
        identity.addProperty("_java_type", "[");
        identity.addProperty("_exp", symbol);
        return indexedOperation("STATE", identity);
    }

    private static JsonObject indexedOperation(
            String operation, JsonObject receiver,
            JsonObject... arguments) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ContainerRelation");
        result.addProperty("shape", "INDEXED");
        result.addProperty("operation", operation);
        result.addProperty("_java_type", "L");
        result.add("receiver", receiver);
        JsonArray encoded = new JsonArray();
        for (JsonObject argument : arguments) encoded.add(argument);
        result.add("arguments", encoded);
        return result;
    }

    private static JsonObject associativeRead(
            JsonObject receiver, JsonObject key, String javaType) {
        JsonObject read = associativeOperation("READ", receiver, key);
        read.addProperty("_java_type", javaType);
        return read;
    }

    private static JsonObject associativeOperation(
            String operation, JsonObject receiver,
            JsonObject... arguments) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ContainerRelation");
        result.addProperty("shape", "ASSOCIATIVE");
        result.addProperty("operation", operation);
        result.addProperty("_java_type", "L");
        result.add("receiver", receiver);
        JsonArray encoded = new JsonArray();
        for (JsonObject argument : arguments) encoded.add(argument);
        result.add("arguments", encoded);
        return result;
    }

    private static JsonObject binary(
            JsonObject left, String operator, JsonObject right) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.add("_left", left);
        result.addProperty("_op", operator);
        result.add("_right", right);
        return result;
    }

    private static String regionOf(String port) {
        int marker = port.indexOf(".in.");
        return marker < 0 ? port.substring(0, port.indexOf(".out."))
                : port.substring(0, marker);
    }

    private static void writeJsonl(Path path, JsonObject... rows)
            throws Exception {
        StringBuilder value = new StringBuilder();
        for (JsonObject row : rows) value.append(row).append('\n');
        Files.write(path, value.toString().getBytes(StandardCharsets.UTF_8));
    }

    private static boolean z3Available() {
        try {
            Process process = new ProcessBuilder("z3", "-version").start();
            return process.waitFor() == 0;
        } catch (Exception ignored) {
            return false;
        }
    }

    private static int count(String text, String needle) {
        int count = 0;
        for (int index = 0; (index = text.indexOf(needle, index)) >= 0;
             index += needle.length()) {
            count++;
        }
        return count;
    }

    private static void assertUnsat(String smt, String extra)
            throws Exception {
        String query = smt.replace("(check-sat)", extra + "(check-sat)");
        ConcolicConstraintSolver.SolverOutput solved =
                ConcolicConstraintSolver.run(Paths.get("z3"), query,
                        10_000L);
        assertEquals(solved.diagnostic(), "unsat", solved.status());
    }

    private static void assertSat(String smt, String extra)
            throws Exception {
        String query = smt.replace("(check-sat)", extra + "(check-sat)");
        ConcolicConstraintSolver.SolverOutput solved =
                ConcolicConstraintSolver.run(Paths.get("z3"), query,
                        10_000L);
        assertEquals(solved.diagnostic(), "sat", solved.status());
    }
}

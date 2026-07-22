package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;
import soot.IntType;
import soot.LongType;
import soot.Modifier;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.VoidType;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class ConfiguredRpcTopologyLoaderTest {
    @Test
    public void resolvesMappingAndKeepsDeclaredEqualityDownstreamOnly()
            throws Exception {
        Fixture fixture = fixture();
        JsonObject declaration = new JsonObject();
        declaration.addProperty("schemaVersion", 1);
        declaration.addProperty("kind", "DECLARED_RPC_EQUALITY");
        declaration.addProperty("fromEndpoint", "REGION.A.out.0");
        declaration.addProperty("toEndpoint", "REGION.C.in.0");
        Path mappingFile = Files.createTempFile("configured-rpc-", ".jsonl");
        try {
            String contents = "# project topology\n" + mappingRow(fixture)
                    + "\n" + declaration + "\n";
            Files.write(mappingFile, contents.getBytes(
                    StandardCharsets.UTF_8));

            ConfiguredRpcTopologyLoader.Result result =
                    ConfiguredRpcTopologyLoader.load(mappingFile,
                            fixture.classes);

            assertEquals(1, result.mappings().size());
            assertEquals(1, result.downstreamDeclarationCount);
            ConfiguredRpcTopologyLoader.Mapping mapping =
                    result.mappings().get(0);
            assertEquals(fixture.producer.getSignature(),
                    mapping.sourceMethod);
            assertEquals(fixture.producer.getSignature() + ".return",
                    mapping.sourceCell);
            assertEquals(fixture.consumer.getSignature(),
                    mapping.targetMethod);
            assertEquals(fixture.consumer.getSignature() + ".return",
                    mapping.targetCell);
            assertTrue(mapping.evidence.contains("channel orders"));
            assertTrue(mapping.evidence.contains(
                    fixture.publisher.getSignature()));
            assertTrue(mapping.evidence.contains(
                    fixture.transport.getSignature()));
            assertTrue(mapping.evidence.contains("mapping only"));
            try {
                result.mappings().add(mapping);
                fail("loader result must be immutable");
            } catch (UnsupportedOperationException expected) {
                // Expected.
            }
        } finally {
            Files.deleteIfExists(mappingFile);
        }
    }

    @Test
    public void rejectsProducerCellThatDriftsFromResolvedMethod()
            throws Exception {
        Fixture fixture = fixture();
        JsonObject row = mappingRow(fixture);
        row.addProperty("fromCell", fixture.producer.getSignature()
                + ".param0:boolean");
        Path mappingFile = Files.createTempFile("configured-rpc-invalid-",
                ".jsonl");
        try {
            Files.write(mappingFile, (row + "\n").getBytes(
                    StandardCharsets.UTF_8));
            try {
                ConfiguredRpcTopologyLoader.load(mappingFile,
                        fixture.classes);
                fail("endpoint declaration drift must fail closed");
            } catch (IllegalStateException expected) {
                assertEquals("Could not load configured RPC topology "
                                + mappingFile, expected.getMessage());
                assertTrue(expected.getCause().getMessage().contains(
                        "fromCell does not name the resolved producer return"));
            }
        } finally {
            Files.deleteIfExists(mappingFile);
        }
    }

    private static Fixture fixture() {
        SootClass producerOwner = new SootClass("example.rpc.Producer",
                Modifier.PUBLIC);
        SootMethod producer = new SootMethod("compute",
                Collections.singletonList(IntType.v()), IntType.v(),
                Modifier.PUBLIC);
        producerOwner.addMethod(producer);

        SootClass bus = new SootClass("example.rpc.Bus", Modifier.PUBLIC);
        SootField transport = new SootField("wire", IntType.v(),
                Modifier.PRIVATE);
        bus.addField(transport);
        SootMethod publisher = new SootMethod("publish",
                Arrays.asList(LongType.v(), IntType.v()), VoidType.v(),
                Modifier.PUBLIC);
        bus.addMethod(publisher);
        SootMethod consumer = new SootMethod("receive",
                Collections.emptyList(), IntType.v(), Modifier.PUBLIC);
        bus.addMethod(consumer);

        Map<String, SootClass> classes = new LinkedHashMap<>();
        classes.put(producerOwner.getName(), producerOwner);
        classes.put(bus.getName(), bus);
        return new Fixture(classes, producer, publisher, consumer, transport);
    }

    private static JsonObject mappingRow(Fixture fixture) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "RPC_TOPOLOGY");
        row.addProperty("authority", "TEST_RUNTIME_GATED_TOPOLOGY");
        row.addProperty("channel", "orders");
        row.addProperty("fromCell", fixture.producer.getSignature()
                + ".return");
        row.addProperty("toCell", fixture.transport.getSignature());

        JsonObject producer = new JsonObject();
        producer.addProperty("owner",
                fixture.producer.getDeclaringClass().getName());
        producer.addProperty("name", fixture.producer.getName());
        producer.addProperty("parameter", "int");
        producer.addProperty("role", "RETURN_VALUE");
        row.add("producer", producer);

        JsonObject publisher = new JsonObject();
        publisher.addProperty("owner",
                fixture.publisher.getDeclaringClass().getName());
        publisher.addProperty("name", fixture.publisher.getName());
        JsonArray parameters = new JsonArray();
        parameters.add("long");
        parameters.add("int");
        publisher.add("parameters", parameters);
        publisher.addProperty("payloadParameterIndex", 1);
        row.add("publisher", publisher);

        JsonObject consumer = new JsonObject();
        consumer.addProperty("owner",
                fixture.consumer.getDeclaringClass().getName());
        consumer.addProperty("name", fixture.consumer.getName());
        consumer.addProperty("role", "RETURN_VALUE");
        row.add("consumer", consumer);
        return row;
    }

    private static final class Fixture {
        private final Map<String, SootClass> classes;
        private final SootMethod producer;
        private final SootMethod publisher;
        private final SootMethod consumer;
        private final SootField transport;

        private Fixture(Map<String, SootClass> classes,
                        SootMethod producer, SootMethod publisher,
                        SootMethod consumer, SootField transport) {
            this.classes = classes;
            this.producer = producer;
            this.publisher = publisher;
            this.consumer = consumer;
            this.transport = transport;
        }
    }
}

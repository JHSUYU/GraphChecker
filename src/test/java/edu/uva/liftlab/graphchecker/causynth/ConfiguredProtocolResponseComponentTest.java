package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import soot.Body;
import soot.ArrayType;
import soot.G;
import soot.IntType;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/** Exact lowering of configured RPC response components. */
public class ConfiguredProtocolResponseComponentTest {
    @Before
    public void resetBefore() {
        G.reset();
        System.clearProperty("causynth.protocol.stubs");
    }

    @After
    public void resetAfter() {
        System.clearProperty("causynth.protocol.stubs");
        G.reset();
    }

    @Test
    public void structuralGettersLowerToOnePrimitiveResponsePath()
            throws Exception {
        Fixture fixture = fixture(false);
        Path config = writeConfig(fixture);
        try {
            System.setProperty("causynth.protocol.stubs", config.toString());
            ConfiguredProtocolStubs configured =
                    ConfiguredProtocolStubs.fromConfiguration(fixture.methods);
            HadoopCommunicationAdapter adapter =
                    new HadoopCommunicationAdapter(fixture.methods,
                            configured);
            CommunicationResolution resolution = adapter.resolve(
                    "<example.Caller: void run()>", 9,
                    fixture.client.getSignature());
            assertTrue(resolution.site != null);
            assertEquals(1, resolution.site.responseComponents.size());
            Map<String, Object> row = resolution.site
                    .responseComponents.get(0)
                    .row(resolution.site.exchangeSiteKey);
            assertEquals("int", row.get(
                    CommunicationCatalogContract.PORT_JAVA_TYPE));
            assertEquals(resolution.site.exchangeSiteKey + ".resp.keyId",
                    row.get(CommunicationCatalogContract.PORT_ID));
            assertEquals(resolution.site.exchangeSiteKey + ".resp",
                    row.get(CommunicationCatalogContract.PORT_COMPONENT_OF));
            assertEquals("resp/currentKey/keyId", row.get(
                    CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH));
            @SuppressWarnings("unchecked")
            List<Map<String, Object>> path =
                    (List<Map<String, Object>>) row.get(
                    CommunicationCatalogContract.PORT_HANDOFF_PATH);
            assertEquals(fixture.currentKey.getSignature(),
                    path.get(0).get("declaration"));
            assertEquals(fixture.keyId.getSignature(),
                    path.get(1).get("declaration"));
        } finally {
            Files.deleteIfExists(config);
        }
    }

    @Test
    public void getterWithComputationIsRejected() throws Exception {
        Fixture fixture = fixture(true);
        Path config = writeConfig(fixture);
        try {
            System.setProperty("causynth.protocol.stubs", config.toString());
            try {
                ConfiguredProtocolStubs.fromConfiguration(fixture.methods);
                fail("computed getter must not become a response path");
            } catch (IOException expected) {
                assertTrue(expected.getMessage().contains(
                        "not one structural field access"));
            }
        } finally {
            Files.deleteIfExists(config);
        }
    }

    @Test
    public void uniqueArrayElementLowersToOneContainerResponsePath()
            throws Exception {
        Map<String, SootMethod> methods = new LinkedHashMap<>();
        SootClass response = applicationClass("example.ArrayResponse");
        SootClass command = applicationClass("example.KeyCommand");
        SootClass keys = applicationClass("example.Keys");
        SootClass protocol = applicationClass("example.ArrayProtocol");
        SootClass server = applicationClass("example.ArrayServer");
        SootField commands = new SootField("commands",
                ArrayType.v(command.getType(), 1), Modifier.PRIVATE);
        SootField keyState = new SootField("keys", keys.getType(),
                Modifier.PRIVATE);
        SootField allKeys = new SootField("allKeys",
                ArrayType.v(IntType.v(), 1), Modifier.PRIVATE);
        response.addField(commands);
        command.addField(keyState);
        keys.addField(allKeys);
        SootMethod getCommands = getter(response, "getCommands", commands,
                false);
        SootMethod getKeys = getter(command, "getKeys", keyState, false);
        SootMethod getAllKeys = getter(keys, "getAllKeys", allKeys, false);
        SootMethod client = method(protocol, "getResponse",
                response.getType());
        SootMethod serverMethod = method(server, "getResponse",
                response.getType());
        for (SootMethod method : new SootMethod[]{getCommands, getKeys,
                getAllKeys, client, serverMethod}) {
            methods.put(method.getSignature(), method);
        }

        JsonObject row = baseConfig(client, serverMethod);
        JsonObject component = new JsonObject();
        component.addProperty("name", "allKeys");
        JsonArray path = new JsonArray();
        path.add(getterStep(getCommands));
        JsonObject element = new JsonObject();
        element.addProperty("uniqueArrayElementType", command.getName());
        path.add(element);
        path.add(getterStep(getKeys));
        path.add(getterStep(getAllKeys));
        component.add("path", path);
        JsonArray components = new JsonArray();
        components.add(component);
        row.add("responseComponents", components);
        Path config = Files.createTempFile("response-array", ".jsonl");
        Files.write(config, Collections.singletonList(row.toString()),
                StandardCharsets.UTF_8);
        try {
            System.setProperty("causynth.protocol.stubs", config.toString());
            CommunicationResolution resolution = new HadoopCommunicationAdapter(
                    methods, ConfiguredProtocolStubs.fromConfiguration(methods))
                    .resolve("<example.Caller: void run()>", 4,
                            client.getSignature());
            Map<String, Object> encoded = resolution.site.responseComponents
                    .get(0).row(resolution.site.exchangeSiteKey);
            assertEquals("int[]", encoded.get(
                    CommunicationCatalogContract.PORT_JAVA_TYPE));
            assertEquals("BOUNDED_CONTAINER_STATE",
                    encoded.get("symbolicDemand"));
            @SuppressWarnings("unchecked")
            List<Map<String, Object>> lowered =
                    (List<Map<String, Object>>) encoded.get(
                            CommunicationCatalogContract.PORT_HANDOFF_PATH);
            assertEquals("UNIQUE_ARRAY_ELEMENT",
                    lowered.get(1).get("kind"));
            assertEquals(command.getName(), lowered.get(1).get("elementType"));
        } finally {
            Files.deleteIfExists(config);
        }
    }

    private static Fixture fixture(boolean computedLeaf) {
        Map<String, SootMethod> methods = new LinkedHashMap<>();
        SootClass response = applicationClass("example.Response");
        SootClass key = applicationClass("example.Key");
        SootClass protocol = applicationClass("example.Protocol");
        SootClass server = applicationClass("example.Server");
        SootField currentKey = new SootField("currentKey", key.getType(),
                Modifier.PRIVATE);
        SootField keyId = new SootField("keyId", IntType.v(),
                Modifier.PRIVATE);
        response.addField(currentKey);
        key.addField(keyId);
        SootMethod getCurrentKey = getter(response, "getCurrentKey",
                currentKey, false);
        SootMethod getKeyId = getter(key, "getKeyId", keyId, computedLeaf);
        SootMethod client = method(protocol, "getKeys",
                response.getType());
        SootMethod serverMethod = method(server, "getKeys",
                response.getType());
        for (SootMethod method : new SootMethod[]{getCurrentKey, getKeyId,
                client, serverMethod}) {
            methods.put(method.getSignature(), method);
        }
        return new Fixture(methods, client, serverMethod, getCurrentKey,
                getKeyId, currentKey, keyId);
    }

    private static SootMethod getter(SootClass owner, String name,
                                     SootField field, boolean computed) {
        SootMethod method = new SootMethod(name, Collections.<Type>emptyList(),
                field.getType(), Modifier.PUBLIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local self = Jimple.v().newLocal("self", owner.getType());
        Local value = Jimple.v().newLocal("value", field.getType());
        body.getLocals().add(self);
        body.getLocals().add(value);
        body.getUnits().add(Jimple.v().newIdentityStmt(self,
                Jimple.v().newThisRef((RefType) owner.getType())));
        body.getUnits().add(Jimple.v().newAssignStmt(value,
                Jimple.v().newInstanceFieldRef(self, field.makeRef())));
        if (computed) {
            body.getUnits().add(Jimple.v().newAssignStmt(value,
                    Jimple.v().newAddExpr(value, IntConstant.v(1))));
        }
        body.getUnits().add(Jimple.v().newReturnStmt(value));
        return method;
    }

    private static SootMethod method(SootClass owner, String name,
                                     Type returns) {
        SootMethod method = new SootMethod(name,
                Collections.<Type>emptyList(), returns, Modifier.PUBLIC);
        owner.addMethod(method);
        return method;
    }

    private static SootClass applicationClass(String name) {
        SootClass sootClass = new SootClass(name, Modifier.PUBLIC);
        sootClass.setApplicationClass();
        Scene.v().addClass(sootClass);
        return sootClass;
    }

    private static Path writeConfig(Fixture fixture) throws IOException {
        JsonObject row = baseConfig(fixture.client, fixture.server);
        JsonObject component = new JsonObject();
        component.addProperty("name", "keyId");
        JsonArray path = new JsonArray();
        path.add(getterStep(fixture.getCurrentKey));
        path.add(getterStep(fixture.getKeyId));
        component.add("path", path);
        JsonArray components = new JsonArray();
        components.add(component);
        row.add("responseComponents", components);
        Path config = Files.createTempFile("response-components", ".jsonl");
        Files.write(config, Collections.singletonList(row.toString()),
                StandardCharsets.UTF_8);
        return config;
    }

    private static JsonObject baseConfig(SootMethod client,
                                         SootMethod server) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 2);
        row.addProperty("kind", "PROTOCOL_STUB_MAPPING");
        row.addProperty("id", "example.keys");
        row.addProperty("transport", "HADOOP_IPC");
        row.addProperty("clientStub", client.getSignature());
        row.addProperty("serverStub", server.getSignature());
        row.addProperty("request", "POSITIONAL");
        row.addProperty("response", true);
        return row;
    }

    private static JsonObject getterStep(SootMethod getter) {
        JsonObject step = new JsonObject();
        step.addProperty("getter", getter.getSignature());
        return step;
    }

    private static final class Fixture {
        final Map<String, SootMethod> methods;
        final SootMethod client;
        final SootMethod server;
        final SootMethod getCurrentKey;
        final SootMethod getKeyId;
        final SootField currentKey;
        final SootField keyId;

        Fixture(Map<String, SootMethod> methods, SootMethod client,
                SootMethod server, SootMethod getCurrentKey,
                SootMethod getKeyId, SootField currentKey, SootField keyId) {
            this.methods = methods;
            this.client = client;
            this.server = server;
            this.getCurrentKey = getCurrentKey;
            this.getKeyId = getKeyId;
            this.currentKey = currentKey;
            this.keyId = keyId;
        }
    }
}

package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import org.junit.Test;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.List;

import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;

/** Runtime navigation of one configured structured response component. */
public class ConcolicRegionRuntimeResponsePathTest {

    @Test
    public void uniqueTypedArrayElementLocatesTheExactContainerLeaf()
            throws Exception {
        Keys keys = new Keys(new int[]{1, 2});
        Response response = new Response(new Command[]{
                new OtherCommand(), new KeyUpdateCommand(keys)});
        Object leaf = resolve(response, path());
        Field owner = leaf.getClass().getDeclaredField("owner");
        owner.setAccessible(true);
        assertSame(keys, owner.get(leaf));
    }

    @Test
    public void zeroOrSeveralTypedElementsDoNotGuess() throws Exception {
        assertNull(resolve(new Response(new Command[]{new OtherCommand()}),
                path()));
        assertNull(resolve(new Response(new Command[]{
                new KeyUpdateCommand(new Keys(new int[]{1})),
                new KeyUpdateCommand(new Keys(new int[]{2}))}), path()));
    }

    private static Object resolve(Object root,
                                  List<CommunicationHandoffSpec.PathStep> path)
            throws Exception {
        Method method = ConcolicRegionRuntime.class.getDeclaredMethod(
                "responseFieldPathLeaf", Object.class, List.class);
        method.setAccessible(true);
        return method.invoke(null, root, path);
    }

    private static List<CommunicationHandoffSpec.PathStep> path() {
        JsonObject site = new JsonObject();
        site.addProperty("role", "EXPORT");
        site.addProperty("portId", "XCH.response.resp.allKeys");
        site.addProperty("handoffLeafPath",
                "resp/commands/[KeyUpdateCommand]/keys/allKeys");
        site.addProperty("direction", "RESPONSE");
        site.addProperty("javaType", "int[]");
        site.addProperty("exchangeSiteKey", "XCH.response");
        site.addProperty("componentOfPortId", "XCH.response.resp");
        site.addProperty("encodingAuthority", "TEST_RESPONSE_PATH_V1");
        site.addProperty("definitionMethod", "<example.Server: void run()>");
        JsonArray path = new JsonArray();
        path.add(field(Response.class, "commands", Command[].class));
        JsonObject element = new JsonObject();
        element.addProperty("kind", "UNIQUE_ARRAY_ELEMENT");
        element.addProperty("elementType", KeyUpdateCommand.class.getName());
        path.add(element);
        path.add(field(KeyUpdateCommand.class, "keys", Keys.class));
        path.add(field(Keys.class, "allKeys", int[].class));
        site.add(CommunicationCatalogContract.PORT_HANDOFF_PATH, path);
        JsonObject task = new JsonObject();
        JsonArray sites = new JsonArray();
        sites.add(site);
        task.add(CommunicationHandoffSpec.FIELD, sites);
        return CommunicationHandoffSpec.decode(task).get(0).handoffPath();
    }

    private static JsonObject field(Class<?> owner, String name,
                                    Class<?> type) {
        JsonObject step = new JsonObject();
        step.addProperty("kind", "FIELD");
        step.addProperty("declaration", "<" + owner.getName() + ": "
                + javaType(type) + " " + name + ">");
        return step;
    }

    private static String javaType(Class<?> type) {
        if (!type.isArray()) return type.getName();
        return javaType(type.getComponentType()) + "[]";
    }

    private static class Command { }
    private static final class OtherCommand extends Command { }
    private static final class KeyUpdateCommand extends Command {
        private final Keys keys;
        private KeyUpdateCommand(Keys keys) { this.keys = keys; }
    }
    private static final class Keys {
        private final int[] allKeys;
        private Keys(int[] allKeys) { this.allKeys = allKeys; }
    }
    private static final class Response {
        private final Command[] commands;
        private Response(Command[] commands) { this.commands = commands; }
    }
}

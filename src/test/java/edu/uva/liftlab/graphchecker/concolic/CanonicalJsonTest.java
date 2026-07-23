package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

public class CanonicalJsonTest {
    @Test
    public void sortsObjectKeysButPreservesArrayOrderAndEscaping() {
        JsonArray values = new JsonArray();
        values.add(true);
        values.add(JsonNull.INSTANCE);
        values.add(1.25);
        JsonObject first = new JsonObject();
        first.addProperty("z", "<>&='\"\n");
        first.add("a", values);
        JsonObject second = new JsonObject();
        second.add("a", values.deepCopy());
        second.addProperty("z", "<>&='\"\n");

        assertEquals("{\"a\":[true,null,1.25],"
                        + "\"z\":\"<>&='\\\"\\n\"}",
                CanonicalJson.render(first));
        assertEquals(CanonicalJson.render(first),
                CanonicalJson.render(second));

        JsonArray reversed = new JsonArray();
        reversed.add(1.25);
        reversed.add(JsonNull.INSTANCE);
        reversed.add(true);
        assertNotEquals(CanonicalJson.render(values),
                CanonicalJson.render(reversed));
    }
}

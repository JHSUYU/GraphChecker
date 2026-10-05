package edu.uva.liftlab.graphchecker.causynth;

import static org.junit.Assert.assertFalse;

import com.google.gson.JsonParser;
import java.util.Collections;
import org.junit.Test;

/** A system's flow declaration applies to a program that holds one of its
 *  methods; a program holding none of them carries none of its values. */
public class WireFlowCatalogTest {
    @Test
    public void aFlowNamingNoMethodOfTheProgramDoesNotApply() {
        assertFalse(WireFlowCatalog.applies(JsonParser.parseString(
                "{\"schemaVersion\":2,\"kind\":\"WIRE_FLOW\",\"id\":\"block-key-id\","
                        + "\"javaType\":\"int\","
                        + "\"producer\":{\"method\":\"<a.P: int p()>\"},"
                        + "\"consumer\":{\"method\":\"<a.C: void c(int)>\"},"
                        + "\"producerFrameMethod\":\"<a.P: void f()>\"}")
                .getAsJsonObject(), Collections.emptyMap()));
    }
}

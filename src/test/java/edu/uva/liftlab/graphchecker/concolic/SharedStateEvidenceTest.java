package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Admission of the VM's recorded shared-state evidence.
 *
 * <p>The interesting half is the refusals. An envelope that cannot prove its
 * own claim must not be repaired into one that can: a writer set silently read
 * as complete, or a cyclic relation read as an order, would let an
 * under-approximate answer be reported as a conclusion.</p>
 */
public class SharedStateEvidenceTest {


    @Test
    public void mapStateSymbolUsesItsExactOccurrenceInputPort() {
        String occurrence = "cluster0/dn0#epoch1/region/REGION.3#1";
        String input = "REGION.3.in.allKeys";
        JsonObject binding = new JsonObject();
        binding.addProperty("locationKey", "MAP_STATE/" + occurrence
                + "@" + ALL_KEYS + "#-3");
        binding.addProperty(SharedStateEvidence.SESSION_LOCATION_FIELD,
                "MAP_STATE/2147#-3");
        binding.addProperty("toOccurrenceId", occurrence);
        binding.addProperty("toInputPort", input);

        JsonObject receiver = new JsonObject();
        receiver.addProperty("_type", "SymbolExpression");
        receiver.addProperty("_java_type", "java/util/HashMap");
        receiver.addProperty("_exp", "M_L'java/util/HashMap'_2147");
        JsonObject state = new JsonObject();
        state.addProperty("_type", "ContainerRelation");
        state.addProperty("shape", "ASSOCIATIVE");
        state.addProperty("operation", "STATE");
        state.add("receiver", receiver);

        JsonObject summary = new JsonObject();
        summary.addProperty("occurrenceId", occurrence);
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        summary.add("edgeBindings", bindings);
        JsonArray path = new JsonArray();
        path.add(state);
        summary.add("pathCondition", path);

        assertTrue(SharedStateEvidence
                .canonicalizeContainerStateSymbols(summary).isEmpty());
        assertEquals(input, summary.getAsJsonArray("pathCondition").get(0)
                .getAsJsonObject().getAsJsonObject("receiver")
                .get("_exp").getAsString());
    }

    // ---- Cross-session location identity -----------------------------

    private static final String ALL_KEYS =
            "org.apache.hadoop.hdfs.security.token.block."
                    + "BlockTokenSecretManager#allKeys";

                        }

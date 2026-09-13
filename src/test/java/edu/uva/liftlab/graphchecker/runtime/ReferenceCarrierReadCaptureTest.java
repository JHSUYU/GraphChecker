package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * A region that only <em>reads</em> a declared reference carrier still
 * versions that read.
 *
 * <p>The rule that decides which reads are versioned has exactly two parts,
 * and neither of them mentions the field's type or whether the reading region
 * also writes it.  Statically, {@code ConcolicInstrumentationSelections
 * .matchesSelectedField} ends in {@code return sharedCarrier || namedTarget}
 * for an instance field -- {@code sharedCarrier} being a global set of
 * {@code owner|fieldName} keys -- so the {@code MATERIALIZE_FIELD} hook
 * stands at every instance read of a declared carrier field in every
 * instrumented method, reference-typed included; only the {@code getstatic}
 * arm above it narrows to {@code PrimType}, and for the stated reason that a
 * static read has no receiver to materialize on.  At replay,
 * {@link SharedStateCapture.SharedCarrierRequest#matchesAccess} keys on
 * declaring class, field name and descriptor, and {@code
 * selectAccessOwnerSharedCarriers} selects on the exact access owner and
 * stamps the consumer access -- both from the read hook and from the write
 * hook, with no precedence between them.</p>
 *
 * <p>These cases pin that shape against the one regression that would break a
 * consumer-side projection: narrowing either test to a primitive descriptor,
 * or to carriers the reading region also writes.  Then the consumer's read
 * would carry no arms, and a read through the reference -- {@code
 * currentKey.getKeyId()} -- would have nothing to project onto but whichever
 * object the replay happened to hold.</p>
 */
public class ReferenceCarrierReadCaptureTest {

    private static final String BTSM =
            "org.apache.hadoop.hdfs.security.token.block."
                    + "BlockTokenSecretManager";
    private static final String KEY_TYPE =
            "Lorg/apache/hadoop/hdfs/security/token/block/BlockKey;";
    private static final String CURRENT_KEY =
            "<" + BTSM + ": org.apache.hadoop.hdfs.security.token.block."
                    + "BlockKey currentKey>";
    private static final String SERIAL_NO = "<" + BTSM + ": int serialNo>";

    /** A reference-typed declared carrier is access-bound like a scalar. */
    @Test
    public void aReferenceCarrierMatchesItsAccessLikeAScalarOne() {
        SharedStateCapture.SharedCarrierRequest reference = carrier(
                "currentKey", KEY_TYPE);
        SharedStateCapture.SharedCarrierRequest scalar = carrier(
                "serialNo", "I");

        assertTrue("a reference carrier binds at its own getfield",
                reference.matchesAccess(CURRENT_KEY));
        assertTrue(scalar.matchesAccess(SERIAL_NO));
        assertFalse("the match is by location, not by class alone",
                reference.matchesAccess(SERIAL_NO));
        assertFalse(scalar.matchesAccess(CURRENT_KEY));
    }

    /**
     * And it is observed as a shared read, which is what opens path
     * recording before the getfield so the VM resolves the read against the
     * location's versions.
     */
    @Test
    public void aReferenceCarrierIsObservedAsASharedRead() {
        assertTrue(carrier("currentKey", KEY_TYPE)
                .observesSharedRead(CURRENT_KEY));
        assertTrue(carrier("serialNo", "I").observesSharedRead(SERIAL_NO));
    }

    /**
     * A task that declares the reference carrier and reads it names it, with
     * no write of its own anywhere in the declaration.
     *
     * <p>This is the consumer-side shape: {@code generateDataEncryptionKey}
     * declares {@code BTSM#currentKey} and never stores to it.  Nothing in
     * the request distinguishes it from the producer's declaration of the
     * same location.</p>
     */
    @Test
    public void aReadOnlyRegionsDeclarationIsTheProducersDeclaration() {
        ConcolicTaskPlan.RuntimeTask consumer = task(
                declaration("currentKey", KEY_TYPE));
        ConcolicTaskPlan.RuntimeTask producer = task(
                declaration("currentKey", KEY_TYPE),
                declaration("serialNo", "I"));

        assertTrue("a read-only region observes the shared read",
                consumer.observesSharedRead(CURRENT_KEY));
        assertTrue(producer.observesSharedRead(CURRENT_KEY));
        assertFalse("a location this region did not declare is not observed",
                consumer.observesSharedRead(SERIAL_NO));
    }

    /**
     * One field declared as both a whole container state and a reference
     * slot is the only shape the selection refuses, and a plain reference
     * declaration is not it.
     */
    @Test
    public void onlyTheDoubleDeclarationIsRefused() {
        List<SharedStateCapture.SharedCarrierRequest> reference =
                Collections.singletonList(carrier("currentKey", KEY_TYPE));
        assertFalse(SharedStateCapture.wholeStateAndPointerCarrier(
                reference, CURRENT_KEY));

        JsonObject asMapState = declaration("currentKey", KEY_TYPE);
        asMapState.addProperty("kind", "MAP_STATE");
        List<SharedStateCapture.SharedCarrierRequest> both = Arrays.asList(
                carrier("currentKey", KEY_TYPE),
                new SharedStateCapture.SharedCarrierRequest(asMapState,
                        true));
        assertTrue("one field is one location",
                SharedStateCapture.wholeStateAndPointerCarrier(both,
                        CURRENT_KEY));
    }

    // ---------- harness ----------

    private static JsonObject declaration(String fieldName,
                                          String descriptor) {
        JsonObject row = new JsonObject();
        row.addProperty("declaringClass", BTSM);
        row.addProperty("fieldName", fieldName);
        row.addProperty("descriptor", descriptor);
        row.addProperty("kind", "DECLARED_FIELD");
        row.addProperty("sourceKind", "ACTIVATION_FIELD_RECEIVER");
        row.add("fieldPath", new JsonArray());
        return row;
    }

    private static SharedStateCapture.SharedCarrierRequest carrier(
            String fieldName, String descriptor) {
        return new SharedStateCapture.SharedCarrierRequest(
                declaration(fieldName, descriptor), true);
    }

    private static ConcolicTaskPlan.RuntimeTask task(
            JsonObject... declarations) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("taskId", "TASK.1");
        encoded.addProperty("goalId", "GOAL.1");
        encoded.addProperty("goalKind", "REGION_PATH_CLOSURE");
        encoded.addProperty("regionId", "REGION.1");
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", "dn0#epoch0");
        encoded.addProperty("occurrenceId", "REGION.1@dn0#epoch0#1");
        encoded.addProperty("rootMethod", "<a.B: void run()>");
        encoded.addProperty("instrumentationSelector", "sel");
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        encoded.add("admission", admission);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("invocationOrdinal", 1);
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", "dn0#epoch0");
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        encoded.add("rootSelector", selector);
        encoded.add("branches", new JsonArray());
        encoded.add("inputActions", new JsonArray());
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        encoded.add("loopBound", loopBound);
        JsonArray carriers = new JsonArray();
        for (JsonObject row : declarations) carriers.add(row);
        encoded.add("sharedCarriers", carriers);
        return new ConcolicTaskPlan.RuntimeTask(
                edu.uva.liftlab.graphchecker.contract.ExecutionTask.decode(
                        encoded));
    }
}

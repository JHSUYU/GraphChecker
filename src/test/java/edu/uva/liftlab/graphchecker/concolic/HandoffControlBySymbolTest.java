package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * A handoff variable is answered by the attach that minted it, wherever in
 * this replay that attach happened.
 *
 * <p>The label {@code HOFF.<sha>} IS the identity of its attach, and the
 * attach happened in this same replay run -- in whichever region
 * activation's summary made it. Looking only at the flipped path's own
 * summary found one attach where the model assigned five, and every such
 * model was refused as not materializable.</p>
 */
public class HandoffControlBySymbolTest {
    private static final String LABEL = "M_I_field_HOFF.abc123"
            + "_edu/uva/liftlab/graphchecker/runtime/"
            + "ConcolicRegionRuntime$HandoffLeafCarrier";
    private static final String PHASE =
            "HANDOFF_PHASE.11111111-2222-3333-4444-555555555555";
    private static final String REPLAY = "REPLAY.GROUP.ONE";

    @Test
    public void aSymbolMintedInASiblingSummaryIsTheObligationsControl() {
        JsonObject task = flipTask();
        JsonObject manifest = manifest();

        ConcolicPathFlipPlanner.Wave.controlBySymbol(task, REPLAY,
                Arrays.asList(pathSummary(), siblingSummary()), manifest);

        JsonArray controls = task.getAsJsonArray(
                RegionPathWorklist.HANDOFF_CONTROLS);
        assertEquals("the attach that minted it answers it", 1,
                controls.size());
        JsonObject control = controls.get(0).getAsJsonObject();
        assertEquals(LABEL, control.get("rawSymbol").getAsString());
        assertEquals(PHASE, control.get(
                InSessionReadResolver.HANDOFF_PHASE_ID).getAsString());
        assertEquals("and names the activation it happened in",
                "node0/region/REGION.sibling#2#a1",
                control.get("consumerOccurrenceId").getAsString());
        assertEquals(0, manifest.getAsJsonArray("gaps").size());
    }

    @Test
    public void aSymbolNoSummaryMintedIsNamed() {
        JsonObject task = flipTask();
        JsonObject manifest = manifest();

        ConcolicPathFlipPlanner.Wave.controlBySymbol(task, REPLAY,
                Arrays.asList(pathSummary()), manifest);

        assertFalse("nothing to carry", task.has(
                RegionPathWorklist.HANDOFF_CONTROLS));
        JsonArray gaps = manifest.getAsJsonArray("gaps");
        assertEquals(1, gaps.size());
        assertEquals("HANDOFF_CONTROL_ROW_ABSENT",
                gaps.get(0).getAsJsonObject().get("kind").getAsString());
        assertTrue(gaps.get(0).getAsJsonObject().get("subject")
                .getAsString().contains("HOFF.abc123"));
    }

    /** One obligation whose resolved flip mentions the arrived value. */
    private static JsonObject flipTask() {
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "I");
        symbol.addProperty("_exp", LABEL);
        JsonArray predicates = new JsonArray();
        predicates.add(symbol);
        JsonObject resolved = new JsonObject();
        resolved.addProperty("schemaVersion",
                ResolvedFlipQuery.SCHEMA_VERSION);
        resolved.addProperty("kind", ResolvedFlipQuery.KIND);
        resolved.addProperty("authority", ResolvedFlipQuery.AUTHORITY);
        resolved.add("predicates", predicates);
        resolved.add("context", new JsonArray());
        resolved.add("unresolved", new JsonArray());
        JsonObject task = new JsonObject();
        task.addProperty("queryKey", "0123456789abcdef");
        task.add(ResolvedFlipQuery.FIELD, resolved);
        return task;
    }

    /** The flipped path's own summary: it minted no handoff. */
    private static JsonObject pathSummary() {
        JsonObject summary = new JsonObject();
        summary.addProperty("replayGroupId", REPLAY);
        summary.addProperty("occurrenceId",
                "node0/region/REGION.target#1#a1");
        return summary;
    }

    /** Another activation of the same replay, where the attach happened. */
    private static JsonObject siblingSummary() {
        JsonObject event = new JsonObject();
        event.addProperty("kind", "VM_HANDOFF_EVENT");
        event.addProperty("attachEventId", 77L);
        event.addProperty(InSessionReadResolver.HANDOFF_SYMBOL, LABEL);
        event.addProperty(InSessionReadResolver.HANDOFF_PHASE_ID, PHASE);
        event.addProperty("javaType", "I");
        event.addProperty("recordedValue", "119982");
        JsonArray events = new JsonArray();
        events.add(event);
        JsonObject summary = new JsonObject();
        summary.addProperty("replayGroupId", REPLAY);
        summary.addProperty("occurrenceId",
                "node0/region/REGION.sibling#2#a1");
        summary.add(VmHandoffEvidence.FIELD, events);
        return summary;
    }

    private static JsonObject manifest() {
        JsonObject manifest = new JsonObject();
        manifest.add("gaps", new JsonArray());
        return manifest;
    }
}

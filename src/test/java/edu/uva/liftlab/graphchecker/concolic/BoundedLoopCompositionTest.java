package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.Test;

import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/** The bounded-loop model's addressing and its fail-closed guard. */
public class BoundedLoopCompositionTest {

    private static final String PLANNED =
            "app/nn0#epoch0/region/REGION.a#1";
    private static final String SITE = "<C: void m()>#u7";

    /**
     * A plan row is addressed by its planned occurrence and an observed case
     * by the activation of it that ran.  The model has to reduce both to the
     * planned address, or it admits the loop and then matches no case against
     * it -- which is how a traversed backedge went unchecked.
     */
    @Test
    public void observedActivationMatchesItsPlannedDeclaration() {
        BoundedLoopComposition model = BoundedLoopComposition.ofPlanRows(
                Collections.singletonList(planRow()),
                Collections.singletonList(boundAuthority(PLANNED + "#a1")));
        model.observeCase(PLANNED + "#a1", observedCase(3));

        JsonObject manifest = model.manifest();
        JsonArray loops = manifest.getAsJsonArray("boundedLoops");
        assertEquals(1, loops.size());
        JsonArray counts = loops.get(0).getAsJsonObject()
                .getAsJsonArray("caseCounts");
        assertEquals(1, counts.size());
        assertEquals(3, counts.get(0).getAsJsonObject()
                .get(LoopBoundPolicy.LOOP_BODY_COUNT).getAsInt());
        assertEquals(0, manifest.getAsJsonArray("gaps").size());
        assertTrue(model.compositionGaps().isEmpty());
    }

    /**
     * With no declaration in scope the model used to publish an empty
     * bounded-loop set and no gaps, so a replay that traversed the loop eight
     * times read exactly like one that never entered it.  It now refuses.
     */
    @Test
    public void aTraversedLoopWithNoDeclarationIsAGap() {
        BoundedLoopComposition model = BoundedLoopComposition.ofPlanRows(
                Collections.emptyList(), Collections.emptyList());
        model.observeCase(PLANNED + "#a1", observedCase(5));

        assertEquals(0, model.manifest().getAsJsonArray("boundedLoops")
                .size());
        assertEquals(1, model.compositionGaps().size());
        JsonObject gap = model.compositionGaps().get(0);
        assertEquals(BoundedLoopComposition.GAP_KIND,
                gap.get("kind").getAsString());
        assertEquals(BoundedLoopComposition.LOOP_OBSERVED_UNDECLARED,
                gap.get("reason").getAsString());
        assertTrue(gap.get("subject").getAsString().startsWith(PLANNED));
    }

    /** A loop the case never entered needs no declaration to be sound. */
    @Test
    public void anUnenteredLoopIsNotAGap() {
        BoundedLoopComposition model = BoundedLoopComposition.ofPlanRows(
                Collections.emptyList(), Collections.emptyList());
        model.observeCase(PLANNED + "#a1", observedCase(0));
        assertTrue(model.compositionGaps().isEmpty());
    }

    private static JsonObject planRow() {
        JsonObject retained = new JsonObject();
        retained.addProperty(LoopBoundPolicy.LOOP_SITE_ID, SITE);
        retained.addProperty(LoopBoundPolicy.RUNTIME_LOOP_ID, "RL.1");
        retained.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION,
                LoopBoundPolicy.LOOP_CONDITION_BOUNDED);
        retained.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION_AUTHORITY,
                LoopBoundPolicy.LOOP_CLASSIFIED_CONDITION_CONTROLLED);
        JsonArray retainedLoops = new JsonArray();
        retainedLoops.add(retained);

        JsonObject plan = new JsonObject();
        plan.addProperty("occurrenceId", PLANNED);
        plan.add(BoundedLoopComposition.PLAN_FIELD, retainedLoops);
        return plan;
    }

    private static JsonObject boundAuthority(String occurrenceId) {
        JsonObject authority = new JsonObject();
        authority.addProperty("occurrenceId", occurrenceId);
        authority.add(LoopBoundPolicy.FIELD,
                LoopBoundPolicy.cfgBackedges(8,
                        Collections.singletonMap(SITE, 8)).toJson());
        return authority;
    }

    private static JsonObject observedCase(int bodyCount) {
        JsonObject count = new JsonObject();
        count.addProperty(LoopBoundPolicy.LOOP_SITE_ID, SITE);
        count.addProperty(LoopBoundPolicy.LOOP_BODY_COUNT, bodyCount);
        count.addProperty(LoopBoundPolicy.PATH_LOOP_REACHED, bodyCount > 0);
        count.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION,
                LoopBoundPolicy.LOOP_CONDITION_BOUNDED);
        count.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION_AUTHORITY,
                LoopBoundPolicy.LOOP_CLASSIFIED_CONDITION_CONTROLLED);
        JsonArray counts = new JsonArray();
        counts.add(count);

        JsonObject item = new JsonObject();
        item.addProperty("caseId", "LOCAL_CASE.test");
        item.add(LoopBoundPolicy.PATH_LOOP_COUNTS, counts);
        return item;
    }
}

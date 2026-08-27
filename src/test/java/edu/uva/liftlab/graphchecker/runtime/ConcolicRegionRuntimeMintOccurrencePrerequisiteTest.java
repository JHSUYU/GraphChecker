package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collections;
import java.util.Set;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * A mint site that ran answers a prerequisite pinned to one of its ordinals.
 *
 * <p>HDFS-11741's {@code allKeys} mutation boundary is anchored on the 49th
 * occurrence of {@code DelegationKey.expiryDate} -- the 49th key discovery's
 * mint walk happened to visit.  A configured source mints one symbol per
 * element, so that ordinal is the container's cardinality in the discovery
 * run, and campaign-takeover-22's replay walked a map of about a dozen keys:
 * occurrence 49 was never minted, the prerequisite could never be met, and
 * every rotating monitor iteration reported the boundary missing while the
 * {@code currentKey} write beside it -- which has no mint prerequisite --
 * was captured normally.</p>
 */
public class ConcolicRegionRuntimeMintOccurrencePrerequisiteTest {
    private static final String TASK = "TASK.mint-anchor";
    private static final String BINDING = "CAPTURE.mutation";
    private static final String FIELD =
            "<example.Key: long expiryDate>";
    private static final String PORT = "REGION.1.in.mint-";
    private static final String OTHER_PORT = "REGION.1.in.other";
    private static final String MAP_CELL =
            "<example.Keys: java.util.Map allKeys>";
    private static final String FIELD_CELL = "<example.Keys: long current>";
    private static final String ANCHOR_SITE =
            "<example.Keys: void removeExpiredKeys()>#u11";

    /** Set before {@link #load()} to state the anchor as a site. */
    private static String anchorSiteId = "";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private String previousPlan;
    private String previousTasks;
    private String previousResults;

    @Before
    public void rememberProperties() {
        previousPlan = System.getProperty("causynth.concolic.task.plan");
        previousTasks = System.getProperty("causynth.concolic.task.id");
        previousResults = System.getProperty("causynth.concolic.results");
        ConcolicRegionRuntime.resetForTests();
    }

    @After
    public void restoreProperties() {
        ConcolicRegionRuntime.resetForTests();
        anchorSiteId = "";
        restore("causynth.concolic.task.plan", previousPlan);
        restore("causynth.concolic.task.id", previousTasks);
        restore("causynth.concolic.results", previousResults);
    }

    @Test
    public void anEarlierMintOccurrenceAnswersAnAnchoredOrdinal()
            throws Exception {
        load();

        // The mint walk ran: a configured source records its occurrences as
        // call-site phases, not as instrumented field accesses, so the field
        // it minted is the evidence -- no ordinal of it is ever an observed
        // input slot.
        Set<String> minted = Collections.singleton(FIELD);
        assertTrue(ConcolicRegionRuntime
                .capturePrerequisitesSatisfiedForTests(TASK, BINDING,
                        Collections.<String>emptySet(),
                        Collections.<String>emptySet(), minted));

        // A run in which the mint site never ran at all still fails: the
        // prerequisite is the site, not the cardinality.
        assertFalse(ConcolicRegionRuntime
                .capturePrerequisitesSatisfiedForTests(TASK, BINDING,
                        Collections.singleton(OTHER_PORT),
                        Collections.<String>emptySet(),
                        Collections.<String>emptySet()));
        assertFalse(ConcolicRegionRuntime
                .capturePrerequisitesSatisfiedForTests(TASK, BINDING,
                        Collections.<String>emptySet(),
                        Collections.<String>emptySet(),
                        Collections.singleton("<example.Key: int other>")));
    }

    /**
     * An anchor stated as a site is satisfied when that exact walk site ran,
     * OR when its underlying field was minted anywhere.
     *
     * <p>The site form names the enclosing walk (HDFS-11741's is {@code
     * removeExpiredKeys()#u11}), but the runtime records a configured-source
     * mint at {@code symbolize()}'s own declaration site, never the caller's
     * walk.  So the exact-site match is a fast-accept and the field-minted
     * fallback is what actually admits the DN's {@code addKeys} mutation --
     * campaign-takeover-25 minted {@code DelegationKey.expiryDate} 35 times
     * across the DN activations yet published zero captures, because the
     * exact site string {@code removeExpiredKeys()#u11} was never in the set
     * the runtime records.</p>
     */
    @Test
    public void anAnchorSiteIsSatisfiedByItsWalkOrItsMintedField()
            throws Exception {
        anchorSiteId = ANCHOR_SITE;
        load();

        // The exact walk site ran.
        assertTrue(ConcolicRegionRuntime
                .capturePrerequisitesSatisfiedForTests(TASK, BINDING,
                        Collections.<String>emptySet(),
                        Collections.singleton(ANCHOR_SITE),
                        Collections.<String>emptySet()));

        // The walk site was not recorded, but the anchor's field was minted:
        // this is the DN case, and it must be satisfied.
        assertTrue(ConcolicRegionRuntime
                .capturePrerequisitesSatisfiedForTests(TASK, BINDING,
                        Collections.<String>emptySet(),
                        Collections.singleton("<example.Keys: void other()>#u1"),
                        Collections.singleton(FIELD)));

        // Neither the walk site nor the field: unsatisfied.
        assertFalse(ConcolicRegionRuntime
                .capturePrerequisitesSatisfiedForTests(TASK, BINDING,
                        Collections.<String>emptySet(),
                        Collections.singleton("<example.Keys: void other()>#u1"),
                        Collections.singleton("<example.Key: int other>")));
    }

    private void load() throws Exception {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", TASK);
        task.addProperty("goalId", "GOAL." + TASK);
        task.addProperty("sourceKey", "test/node#epoch0");
        task.addProperty("occurrenceId",
                "test/node#epoch0/region/REGION.1#1");
        task.addProperty("relationKey", "RELATION.REGION.1");
        task.addProperty("regionId", "REGION.1");
        task.addProperty("goalKind", "OUTPUT_RELATION_CLOSURE");
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "RECEIVER_CONTEXT");
        selector.addProperty("method", "<example.Monitor: void run()>");
        selector.addProperty("receiverClass", Object.class.getName());
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", "test/node#epoch0");
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        task.add("rootSelector", selector);

        JsonArray inputs = new JsonArray();
        for (int occurrence = 1; occurrence <= 40; occurrence++) {
            inputs.add(mintAction(PORT + occurrence));
        }
        JsonObject other = new JsonObject();
        other.addProperty("symbol", OTHER_PORT);
        other.addProperty("portId", OTHER_PORT);
        other.addProperty("mode", "CONCRETE");
        other.addProperty("location", "HEAP_OBJECT_FIELD");
        other.addProperty("accessFieldSignature", "<example.Key: int other>");
        inputs.add(other);
        task.add("inputActions", inputs);

        task.add("branches", new JsonArray());
        task.add("edgeBindings", new JsonArray());
        task.add("outputClosure", closure());
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(task);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        task.add("admission", admission);

        Path plan = folder.newFile("mint-anchor-plan.jsonl").toPath();
        Files.write(plan, (task + "\n").getBytes(StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", TASK);
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve("results.jsonl").toString());
    }

    private static JsonObject mintAction(String port) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", port);
        action.addProperty("portId", port);
        action.addProperty("mode", "CONCRETE");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("accessFieldSignature", FIELD);
        action.addProperty("symbolicDemand",
                "CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED");
        return action;
    }

    /** One member whose capture is anchored on the fortieth mint occurrence. */
    private static JsonObject closure() {
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", BINDING);
        capture.addProperty("outputPort", "REGION.1.out.map");
        capture.addProperty("captureKind", "MUTATION_STATE");
        capture.addProperty("outputCell", MAP_CELL);
        capture.addProperty("javaType", "java.util.Map");
        capture.addProperty("occurrenceScope", "DEFINITION_INVOCATION");
        capture.addProperty("outputSiteId", "MUTATION_STATE:site");
        capture.addProperty("outputOccurrence", 1);
        capture.addProperty("definitionMethod",
                "<example.Keys: boolean updateKeys()>");
        capture.addProperty("fieldSignature", MAP_CELL);
        capture.addProperty("declaredCallee",
                "<java.util.Map: java.lang.Object put(java.lang.Object,"
                        + "java.lang.Object)>");
        capture.addProperty("definitionUnitIndex", 70);
        JsonArray captures = new JsonArray();
        captures.add(capture);

        JsonArray inputPorts = new JsonArray();
        for (int occurrence = 1; occurrence <= 40; occurrence++) {
            inputPorts.add(PORT + occurrence);
        }
        JsonObject slice = new JsonObject();
        slice.add("captureBindings", captures);
        slice.add("inputPorts", inputPorts);
        slice.addProperty("captureAnchorPort", PORT + 40);
        if (!anchorSiteId.isEmpty()) {
            slice.addProperty("captureAnchorSiteId", anchorSiteId);
        }
        slice.addProperty("outputPort", "REGION.1.out.map");
        slice.addProperty("outputCell", MAP_CELL);
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        slice.add("methods", new JsonArray());
        slice.add("causalEdgeIds", new JsonArray());
        slice.add("captureBindingIssues", new JsonArray());
        slice.addProperty("outputBoundaryKind",
                "DEFINITION_INVOCATION_NORMAL_EXIT");
        slice.addProperty("activationLocalOccurrence", 1);

        JsonObject output = new JsonObject();
        output.addProperty("portId", "REGION.1.out.map");
        output.addProperty("kind", "HEAP_STATE");
        output.addProperty("outputSiteId", "MUTATION_STATE:site");
        output.addProperty("outputOccurrence", 1);
        output.addProperty("cell", MAP_CELL);
        output.addProperty("javaTypeDescriptor", "Ljava/util/Map;");

        JsonObject member = new JsonObject();
        member.add("output", output);
        member.add("slice", slice);
        JsonArray members = new JsonArray();
        members.add(member);
        // A second member keeps the relation non-singleton, so the anchor
        // path decides the prerequisite rather than the exit-snapshot path.
        members.add(secondMember());

        JsonObject producer = new JsonObject();
        producer.addProperty("relationKey", "RELATION.REGION.1");
        producer.addProperty("regionId", "REGION.1");

        JsonObject closure = new JsonObject();
        closure.addProperty("schemaVersion", 3);
        closure.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        closure.add("producer", producer);
        closure.add("members", members);
        return closure;
    }

    private static JsonObject secondMember() {
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE.field");
        capture.addProperty("outputPort", "REGION.1.out.field");
        capture.addProperty("captureKind", "FIELD_WRITE_STATE");
        capture.addProperty("outputCell", FIELD_CELL);
        capture.addProperty("javaType", "long");
        capture.addProperty("occurrenceScope", "REGION_ACTIVATION");
        capture.addProperty("outputSiteId", "FIELD_WRITE_STATE:site");
        capture.addProperty("outputOccurrence", 1);
        capture.addProperty("fieldSignature", FIELD_CELL);
        capture.addProperty("definitionMethod",
                "<example.Keys: boolean updateKeys()>");
        capture.addProperty("definitionUnitIndex", 44);
        JsonArray captures = new JsonArray();
        captures.add(capture);

        JsonObject slice = new JsonObject();
        slice.add("captureBindings", captures);
        slice.add("inputPorts", new JsonArray());
        slice.addProperty("outputPort", "REGION.1.out.field");
        slice.addProperty("outputCell", FIELD_CELL);
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        slice.add("methods", new JsonArray());
        slice.add("causalEdgeIds", new JsonArray());
        slice.add("captureBindingIssues", new JsonArray());
        slice.addProperty("outputBoundaryKind",
                "EXACT_FIELD_WRITE_AFTER_ASSIGNMENT");
        slice.addProperty("activationLocalOccurrence", 1);

        JsonObject output = new JsonObject();
        output.addProperty("portId", "REGION.1.out.field");
        output.addProperty("kind", "HEAP_STATE");
        output.addProperty("outputSiteId", "FIELD_WRITE_STATE:site");
        output.addProperty("outputOccurrence", 1);
        output.addProperty("cell", FIELD_CELL);
        output.addProperty("javaTypeDescriptor", "J");

        JsonObject member = new JsonObject();
        member.add("output", output);
        member.add("slice", slice);
        return member;
    }

    private static void restore(String key, String value) {
        if (value == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, value);
        }
    }
}

package edu.uva.liftlab.graphchecker.plan;


import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.causynth.StaticProgram;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * What an experiment's {@code symbolic-inputs.jsonl} governs.
 *
 * <p>Everything: a read is symbolic only where a declaration says so -- a
 * name this file declares, a fault marker in the workload's own source, a
 * field a hook owns, or a wire cut port the communication catalog declared.
 * Every other proposed read is concrete, and the declared cell's write
 * sites are the only stores the replay observes.</p>
 */
public class SymbolicRootPolicyTest {

    private static final String NN = "REGION.nn";
    private static final String NN_TWIN = "REGION.nn-twin";
    private static final String DN = "REGION.dn";
    private static final String CLOCK_CELL =
            "<org.apache.hadoop.util.Timer: long now()>.return";
    private static final String KEY_ID = "<org.apache.hadoop.security.token"
            + ".delegation.DelegationKey: int keyId>";
    private static final String CLASS = "org.apache.hadoop.hdfs.security"
            + ".token.block.BlockTokenSecretManager";
    private static final String UPDATE_KEYS = "boolean updateKeys()";
    /** hdfs-11741's declared site, planned as a region of its own. */
    private static final String EXPIRE = "REGION.expire";
    private static final String REMOVE_EXPIRED =
            "<" + CLASS + ": void removeExpiredKeys()>";
    private static final String ROOT = InputActionCatalog
            .DECLARED_SYMBOLIC_ROOT;

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    /**
     * A declared cell is stamped so the replay knows the row was named by
     * hand rather than proposed; an undeclared read is concrete by name; and
     * a declared wire-flow cut port hands over a producer expression: it is
     * tracked and mints no root, so refusing it would only cut propagation.
     */
    @Test
    public void onlyADeclarationMakesAReadSymbolic() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection = read(
                "{\"regionId\":\"" + NN + "\",\"cells\":[\"" + CLOCK_CELL
                        + "\"],\"clock\":true}");
        JsonArray selected = selection.select(NN, proposals());

        assertTrue("the declared clock carries the mint marker",
                selected.get(0).getAsJsonObject().get(ROOT).getAsBoolean());
        // WHICH reads are wall clocks is declared by the case, never matched
        // against a list of callee signatures: the flag travels from the
        // declaration row onto the action, and the replay reads it there.
        assertTrue("and the clock the case declared",
                selected.get(0).getAsJsonObject()
                        .get(InputActionCatalog.DECLARED_WALL_CLOCK)
                        .getAsBoolean());
        assertFalse("a declared read the case did not call a clock is none",
                declaredWithoutClockFlag().select(NN, proposals()).get(0)
                        .getAsJsonObject()
                        .has(InputActionCatalog.DECLARED_WALL_CLOCK));
        assertEquals("a read no declaration names is concrete by name",
                "CONCRETE", member(selected, 1, "mode"));
        assertEquals(ConcolicScheduler.SymbolicInputSelection.UNDECLARED,
                member(selected, 1, "symbolicDemand"));
        assertEquals("and the fault marker the workload wrote stays symbolic",
                "SYMBOLIC", member(selected, 2, "mode"));
        assertFalse("without the marker, whose mint the runtime finds by "
                        + "sourceKind",
                selected.get(2).getAsJsonObject().has(ROOT));
        JsonArray actions = proposals();
        actions.add(action("COMMUNICATION_SITE_PORT", "<C: int getKeyId()>#u2",
                "<C: int getKeyId()>.return"));
        JsonObject cut = selection.select(DN, actions).get(3).getAsJsonObject();
        assertEquals("SYMBOLIC", cut.get("mode").getAsString());
        assertFalse("a cut port is not a declared root", cut.has(ROOT));

        // And the write side of a DECLARED cell: the VM retains a location
        // by value, so the stores of a declared counter publish nothing
        // until the location is observed, and the graph already names those
        // stores as field_mutation edges carrying the callee that performed
        // them.  Selection only -- which sites the replay observes.
        JsonObject mutation = json("{\"kind\":\"field_mutation\","
                + "\"transferKind\":\"HEAP_WRITE\",\"fromCell\":\""
                + DELETE + "#u35\",\"toCell\":\"" + NUM_SNAPSHOTS
                + "\",\"method\":\"" + DELETE + "\",\"siteId\":\""
                + DELETE + "#u35\",\"unitIndex\":35,\"invoke\":\""
                + DECREMENT + "\"}");
        // One owner: the static scope map already names every write site of
        // the slice with the cell it stores into and the callee that
        // performs it, so the answer is a join over its rows and not a
        // second walk of a graph.
        StaticScopeMap map = writeSiteMap(mutation);
        JsonArray sites = map.writeSitesOf(
                Collections.singleton(ATOMIC_VALUE));
        assertEquals("one write site of the declared cell", 1, sites.size());
        assertEquals(DELETE + "#u35", member(sites, 0, "siteId"));
        assertEquals(ATOMIC_VALUE, member(sites, 0, "cell"));
        assertEquals(DECREMENT, member(sites, 0, "declaredCallee"));
        assertEquals("no declared cell, no observation", 0,
                map.writeSitesOf(Collections.singleton(KEY_ID)).size());
        assertTrue("the declared cell is read off the declared action alone",
                ConcolicScheduler.declaredInputCells(null).isEmpty());

        // A declaration names a VALUE, and the graph names one value once
        // per local it is copied into: the case knows the accessor's own
        // return cell, while the port that materializes it names the local
        // the value lands in.  Soot proves which edges are exact copies, so
        // following only those renames the declaration onto the port --
        // which is how hdfs-17960's declared region input stops matching
        // nothing.
        JsonObject accessorPort = accessorPort();
        assertTrue("the proven rename selects the port",
                renamed(exactCopy()).select(NN, actions(accessorPort))
                        .get(0).getAsJsonObject().get(ROOT).getAsBoolean());
        assertFalse("an edge Soot did not prove a copy is not a rename",
                renamed(plainCopy()).select(NN, actions(accessorPort))
                        .get(0).getAsJsonObject().has(ROOT));
    }

    /**
     * The published static scope map of one write edge, through the artifact
     * the way PLAN publishes it and EXPLORE reads it.
     */
    private StaticScopeMap writeSiteMap(JsonObject mutation)
            throws IOException {
        java.util.Map<String, Object> edge =
                new java.util.LinkedHashMap<String, Object>();
        for (java.util.Map.Entry<String, com.google.gson.JsonElement> member
                : mutation.entrySet()) {
            edge.put(member.getKey(), member.getValue().isJsonPrimitive()
                    && member.getValue().getAsJsonPrimitive().isNumber()
                    ? member.getValue().getAsInt()
                    : member.getValue().getAsString());
        }
        java.util.Map<String, Object> region =
                new java.util.LinkedHashMap<String, Object>();
        region.put("regionId", NN);
        region.put("methods", Collections.singletonList(DELETE));
        List<StaticScopeMap.Site> found = StaticScopeMap.sites(
                Collections.singletonList(edge),
                Collections.singletonList(region));
        StringBuilder text = new StringBuilder();
        for (JsonObject row : StaticScopeMap.rows(found, null)) {
            text.append(row.toString()).append('\n');
        }
        Path file = folder.newFolder().toPath().resolve(StaticScopeMap.FILE);
        Files.write(file, text.toString().getBytes(StandardCharsets.UTF_8));
        return StaticScopeMap.read(file);
    }

    /** The accessor's return cell, as a case declares a manual read. */
    private static final String ACCESSOR_RETURN =
            "<S: int getNumSnapshots()>.return";
    /** The local the accessor copies it into, which the port names. */
    private static final String ACCESSOR_LOCAL =
            "<S: int getNumSnapshots()>::$i0";

    /** One declaration of {@link #ACCESSOR_RETURN}, resolved over one graph. */
    private ConcolicScheduler.SymbolicInputSelection renamed(JsonObject edge)
            throws IOException {
        ConcolicScheduler.SymbolicInputSelection selection = read(
                "{\"regionId\":\"" + NN + "\",\"cells\":[\""
                        + ACCESSOR_RETURN + "\"]}");
        selection.resolveDeclaredNames(Collections.singletonList(edge));
        return selection;
    }

    /** The declared counter of hdfs-17960 and the store the graph names. */
    private static final String ATOMIC_VALUE =
            "<java.util.concurrent.atomic.AtomicInteger: int value>";
    private static final String NUM_SNAPSHOTS =
            "<S: java.util.concurrent.atomic.AtomicInteger numSnapshots>";
    private static final String DECREMENT = "<java.util.concurrent.atomic"
            + ".AtomicInteger: int getAndDecrement()>";
    private static final String DELETE = "<S: void deleteSnapshot()>";

    private static String member(JsonArray rows, int index, String name) {
        JsonObject row = rows.get(index).getAsJsonObject();
        return row.has(name) ? row.get(name).getAsString() : "";
    }

    private static JsonArray actions(JsonObject action) {
        JsonArray actions = new JsonArray();
        actions.add(action.deepCopy());
        return actions;
    }

    /** The accessor-return port: its cell is the Atomic's value leaf. */
    private static JsonObject accessorPort() {
        JsonObject port = action("ACCESSOR_RETURN",
                "<S: int getNumSnapshots()>#u2",
                "<java.util.concurrent.atomic.AtomicInteger: int value>");
        port.addProperty("accessFieldSignature",
                "<java.util.concurrent.atomic.AtomicInteger: int value>");
        JsonArray cells = new JsonArray();
        cells.add(ACCESSOR_LOCAL);
        port.add("dependencyCells", cells);
        return port;
    }

    private static JsonObject exactCopy() {
        JsonObject edge = plainCopy();
        edge.addProperty("valueFlowAuthority",
                "SOOT_EXACT_LOCAL_DIRECT_COPY_V1");
        return edge;
    }

    private static JsonObject plainCopy() {
        return json("{\"kind\":\"local_def_use\",\"transferKind\":"
                + "\"VALUE_PASS\",\"fromCell\":\"" + ACCESSOR_LOCAL
                + "\",\"toCell\":\"" + ACCESSOR_RETURN + "\"}");
    }

    /**
     * A manual root is declared by the site it is read at, not by a region hash.
     *
     * <p>A region id moves whenever the retained selection moves; a static
     * site is what the experiment knows, and the plan resolves it to the
     * regions covering it -- one method planned twice is two regions, and
     * both mean it.</p>
     */
    @Test
    public void aManualRootIsDeclaredByItsSite() throws Exception {
        declaresAt("\"class\":\"" + CLASS + "\",\"method\":\"" + UPDATE_KEYS
                + "\"", Arrays.asList(NN, NN_TWIN), Arrays.asList(DN));
        // a node scope narrows the same site to the regions planned there
        declaresAt("\"class\":\"" + CLASS + "\",\"method\":\"void addKeys()\","
                        + "\"node\":\"dn0\",\"epoch\":\"0\"",
                Arrays.asList(DN), Arrays.asList(NN, NN_TWIN));

        // A declared method is a region ROOT by declaration, and the region
        // it roots opens on whatever anchor the recording selected -- on
        // hdfs-11741, removeExpiredKeys is held by the updateKeys region and
        // its own region's plan row names that enclosing method.  The
        // declaration still means the region it roots, so the anchor column
        // alone does not decide this.
        declaresAt("\"class\":\"" + CLASS
                        + "\",\"method\":\"void removeExpiredKeys()\"",
                Arrays.asList(EXPIRE), Arrays.asList(NN, NN_TWIN, DN));

        // A site the plan carries no region for is refused by name.  Under
        // the rule it can mean only one thing: this plan was built without
        // the declaration, because a declared root the recording never
        // entered is refused at aggregation instead (below).  The refusal
        // names the declared roots the plan did honour, which is what tells
        // the reader to re-plan rather than to edit the case.
        try {
            read("{\"class\":\"" + CLASS + "\",\"method\":\"long absent()\","
                    + "\"cells\":[\"" + CLOCK_CELL + "\"]}");
            fail("a site outside every planned region was admitted");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage()
                    .contains("DECLARED_INPUT_NOT_PLANNED"));
            assertTrue(refused.getMessage(), refused.getMessage()
                    .contains("long absent()"));
            assertTrue(refused.getMessage(), refused.getMessage()
                    .contains(REMOVE_EXPIRED));
        }

        // And the other failure mode, where the count is a fact: PLAN plans
        // the declared root whether or not the recording entered it, and the
        // aggregation refuses it by name with the activation count, so the
        // case author reads "your workload never reached this site" rather
        // than "the engine dropped your root".
        List<StaticProgram.RegionRow> declared = StaticProgram.regionRows(
                Collections.singletonList(declaredRootSkeleton()),
                "REGION_SKELETON", "test");
        try {
            RuntimeSelectedRegionFinalizer.refuseUnactivatedDeclaredInputs(
                    declared, Collections.<Map<String, Object>>emptyList(),
                    Collections.<Map<String, Object>>emptyList());
            fail("a declared root the recording never entered was planned");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage()
                    .contains("DECLARED_INPUT_NEVER_ACTIVATED"));
            assertTrue(refused.getMessage(), refused.getMessage()
                    .contains(REMOVE_EXPIRED));
            assertTrue(refused.getMessage(), refused.getMessage()
                    .contains("0 times"));
        }
        Map<String, Object> activation = new LinkedHashMap<String, Object>();
        activation.put("regionId", EXPIRE);
        RuntimeSelectedRegionFinalizer.refuseUnactivatedDeclaredInputs(
                declared, Collections.singletonList(activation),
                Collections.<Map<String, Object>>emptyList());

        // F1: AND A FOLDED ENTRY IS AN ENTRY.  A declared region entered
        // synchronously inside a running occurrence opens none of its own,
        // so it has no activation and never will; the recording reached the
        // declared site all the same, and its sites are planned at the
        // occurrence that folded it.  hdfs-11741 campaign #5 died here --
        // every entry of updateKeys() ran inside the NameNode's key-manager
        // tick -- so the fold is what this guard reads, not only the
        // activation.
        Map<String, Object> fold = new LinkedHashMap<String, Object>();
        fold.put("kind", RuntimeSelectedRegionFinalizer.REGION_FOLD_KIND);
        fold.put("regionId", EXPIRE);
        fold.put("enclosingRegionId", NN);
        RuntimeSelectedRegionFinalizer.refuseUnactivatedDeclaredInputs(
                declared, Collections.<Map<String, Object>>emptyList(),
                Collections.singletonList(fold));

        // A fold of ANOTHER region is not an entry of this one.
        Map<String, Object> elsewhere = new LinkedHashMap<String, Object>();
        elsewhere.put("kind",
                RuntimeSelectedRegionFinalizer.REGION_FOLD_KIND);
        elsewhere.put("regionId", NN);
        try {
            RuntimeSelectedRegionFinalizer.refuseUnactivatedDeclaredInputs(
                    declared, Collections.<Map<String, Object>>emptyList(),
                    Collections.singletonList(elsewhere));
            fail("a fold of another region was read as this one's entry");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage()
                    .contains("DECLARED_INPUT_NEVER_ACTIVATED"));
        }

        // CLK: A CALLEE DECLARATION IS ABOUT NO SITE.  It says every read of
        // that method's return is a root, wherever in the application scope
        // it is called, so it declares the RETURN cell in every planned
        // region of its scope -- and `kind: CLOCK` is the same statement
        // `clock: true` is for the cell form.  The per-method cell form
        // named ONE site per declared method, and hdfs-11741's slice calls
        // Timer.now() at seven: the reads in generateKeys and
        // generateDataEncryptionKey entered every formula as constants.
        ConcolicScheduler.SymbolicInputSelection everywhere = read(
                "{\"callee\":\"<org.apache.hadoop.util.Timer: long now()>\","
                        + "\"kind\":\"CLOCK\"}");
        for (String id : Arrays.asList(NN, NN_TWIN, DN, EXPIRE)) {
            assertTrue("a declared callee's return is a root in " + id,
                    everywhere.declares(id, CLOCK_CELL));
        }
        assertTrue("and the case declared it a clock by its kind",
                everywhere.select(NN, proposals()).get(0).getAsJsonObject()
                        .get(InputActionCatalog.DECLARED_WALL_CLOCK)
                        .getAsBoolean());
        // A node scope still narrows it, because a declaration's scope is
        // one rule whatever it names.
        ConcolicScheduler.SymbolicInputSelection onDn = read(
                "{\"callee\":\"<org.apache.hadoop.util.Timer: long now()>\","
                        + "\"kind\":\"CLOCK\",\"node\":\"dn0\"}");
        assertTrue(onDn.declares(DN, CLOCK_CELL));
        assertFalse("and not the regions planned elsewhere",
                onDn.declares(NN, CLOCK_CELL));
        // A callee stated twice at two kinds is a contradiction in the case
        // file, refused by name rather than letting the later row win.
        Path twice = folder.newFolder().toPath()
                .resolve("symbolic-inputs.jsonl");
        Files.write(twice, ("{\"callee\":\"" + TIMER_NOW
                + "\",\"kind\":\"CLOCK\"}\n{\"callee\":\"" + TIMER_NOW
                + "\",\"kind\":\"INTEGRAL\"}\n")
                .getBytes(StandardCharsets.UTF_8));
        try {
            DeclaredSymbolicInputs.callees(twice);
            fail("one callee was admitted at two kinds");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(),
                    refused.getMessage().contains("at two kinds"));
        }
        assertEquals("and the cell a callee declaration names is its return",
                CLOCK_CELL, DeclaredSymbolicInputs.returnCell(TIMER_NOW));
    }

    /** The callee hdfs-11741 and hdfs-17897 declare a CLOCK. */
    private static final String TIMER_NOW =
            "<org.apache.hadoop.util.Timer: long now()>";

    /** The skeleton PLAN publishes for hdfs-11741's declared clock site. */
    private static Map<String, Object> declaredRootSkeleton() {
        Map<String, Object> row = new LinkedHashMap<String, Object>();
        row.put("schemaVersion", 3);
        row.put("kind", "REGION_SKELETON");
        row.put("regionId", EXPIRE);
        row.put("rootMethod", REMOVE_EXPIRED);
        row.put("rootAuthority", DeclaredSymbolicInputs.AUTHORITY);
        row.put("anchorMethod", REMOVE_EXPIRED);
        row.put("methods", Collections.singletonList(REMOVE_EXPIRED));
        row.put(DeclaredSymbolicInputs.ROOT_FIELD, true);
        return row;
    }

    /** One site declaration, and the regions it must and must not reach. */
    private void declaresAt(String site, List<String> declaring,
            List<String> silent) throws IOException {
        ConcolicScheduler.SymbolicInputSelection selection =
                read("{" + site + ",\"cells\":[\"" + CLOCK_CELL + "\"]}");
        for (String id : declaring) assertTrue(site, selection.declares(id, CLOCK_CELL));
        for (String id : silent) assertFalse(site, selection.declares(id, CLOCK_CELL));
    }

    /** The same declaration of {@link #CLOCK_CELL}, stating no clock. */
    private ConcolicScheduler.SymbolicInputSelection
            declaredWithoutClockFlag() throws IOException {
        return read("{\"regionId\":\"" + NN + "\",\"cells\":[\""
                + CLOCK_CELL + "\"]}");
    }

    /** One declaration row, written where the campaign would put the file. */
    private ConcolicScheduler.SymbolicInputSelection read(String row)
            throws IOException {
        Path path = folder.newFolder().toPath().resolve("symbolic-inputs.jsonl");
        Files.write(path, (row + "\n").getBytes(StandardCharsets.UTF_8));
        return ConcolicScheduler.SymbolicInputSelection.read(path,
                Arrays.asList(json("{\"regionId\":\"" + NN + "\"}"),
                        json("{\"regionId\":\"" + NN_TWIN + "\"}"),
                        json("{\"regionId\":\"" + DN + "\"}"),
                        json("{\"regionId\":\"" + EXPIRE
                                + "\",\"rootMethod\":\"" + REMOVE_EXPIRED
                                + "\",\"" + DeclaredSymbolicInputs.ROOT_FIELD
                                + "\":true}")), plans());
    }

    /** Two nn0 regions of one method, and one dn0 region of another. */
    private static List<RegionInstancePlan> plans() {
        String updateKeys = "<" + CLASS + ": " + UPDATE_KEYS + ">";
        return Arrays.asList(plan(NN, updateKeys, "wl/nn0#epoch0", 1),
                plan(NN_TWIN, updateKeys, "wl/nn0#epoch0", 2),
                plan(DN, "<" + CLASS + ": void addKeys()>", "wl/dn0#epoch0", 1),
                // the declared root's own region, anchored on the enclosing
                // method the recording selected
                plan(EXPIRE, updateKeys, "wl/nn0#epoch0", 3));
    }

    private static RegionInstancePlan plan(String regionId, String method,
            String key, int occurrence) {
        String id = key + "/region/" + regionId + "#" + occurrence;
        return RegionInstancePlan.decode(json("{\"regionId\":\"" + regionId
                + "\",\"targetMethod\":\"" + method + "\",\"sourceKey\":\""
                + key + "\",\"occurrenceId\":\"" + id + "\",\"relationKey\":\""
                + key + "/relation/" + regionId + "\",\"closureGoals\":[{"
                + "\"goalId\":\"GOAL." + id + "\",\"kind\":"
                + "\"REGION_PATH_CLOSURE\",\"runtimeDefinitionMethods\":[]}]}"));
    }

    /** One automatic clock return, one accessor field, one fault marker. */
    private static JsonArray proposals() {
        JsonArray actions = new JsonArray();
        JsonObject clock = action("EXTERNAL_CALL_RETURN",
                "<C: void removeExpiredKeys()>#u2", CLOCK_CELL);
        clock.addProperty("declaredCallee", "<org.apache.hadoop.util.Timer: long now()>");
        actions.add(clock);
        JsonObject field = action("ACCESSOR_RETURN", "<C: boolean f()>#u9", KEY_ID);
        field.addProperty("accessFieldSignature", KEY_ID);
        actions.add(field);
        actions.add(action("EXPLICIT_SYMBOLIC_FAULT",
                "<C: void sendRpcRequest(D)>#u17",
                "<C: void sendRpcRequest(D)>::$z5"));
        return actions;
    }

    private static JsonObject action(String sourceKind, String siteId,
            String cell) {
        return json("{\"mode\":\"SYMBOLIC\",\"sourceKind\":\"" + sourceKind
                + "\",\"siteId\":\"" + siteId + "\",\"portId\":\"port."
                + siteId + "\",\"symbol\":\"port." + siteId + "\",\"cell\":\""
                + cell + "\"}");
    }

    private static JsonObject json(String row) {
        return JsonParser.parseString(row).getAsJsonObject();
    }
}

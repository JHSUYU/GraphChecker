package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.StaticSymbolicSourceDeclaration;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * The one surviving job of the symbolic-input allowlist: it decides WHICH
 * DECLARED FIELDS a region materializes symbolically.  Which minted symbol
 * reaches which read is not predicted here -- at replay the VM's propagated
 * expression is the authority -- so there is nothing about selectors,
 * selected phases, producer versions or output-version boundaries to pin.
 */
public class StaticSymbolicSourceSelectionTest {
    private static final List<String> IDS = Arrays.asList(
            "RPC_COMPARE.A", "RPC_COMPARE.B", "RPC_COMPARE.C",
            "RPC_COMPARE.D", "RPC_COMPARE.E");

    /** With no configuration file the Java hook sites are the allowlist, and
     * every field they mint is left CONCRETE for the hook to symbolize. */
    @Test
    public void discoveredHookFieldsAreOwnedAndLeftConcrete()
            throws Exception {
        JsonObject regionA = region("REGION.A", "getCausynthValueA");
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(null,
                        Collections.singletonList(regionA));
        JsonObject action = fieldAction("<Node: long value0>");
        JsonObject selected = selection.select("REGION.A", one(action))
                .get(0).getAsJsonObject();
        assertEquals("CONCRETE", selected.get("mode").getAsString());
        assertEquals("CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED",
                selected.get("symbolicDemand").getAsString());
        assertFalse(selection.selectedForDiscovery("REGION.A", action));
    }

    /** A field no hook and no configuration names is not a symbolic root. */
    @Test
    public void undeclaredFieldIsDemotedAsUnselected() throws Exception {
        JsonObject regionA = region("REGION.A", "getCausynthValueA");
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(null,
                        Collections.singletonList(regionA));
        JsonObject action = fieldAction("<Node: long unrelated>");
        JsonObject selected = selection.select("REGION.A", one(action))
                .get(0).getAsJsonObject();
        assertEquals("CONCRETE", selected.get("mode").getAsString());
        assertEquals("CONFIGURED_SYMBOLIC_INPUT_UNSELECTED",
                selected.get("symbolicDemand").getAsString());
    }

    /** A declared field signature is the manual input, and it is the one
     * thing that keeps a materialization action SYMBOLIC. */
    @Test
    public void configuredFieldSignatureStaysSymbolic() throws Exception {
        Path file = selectionFile("REGION.CONFIG", "<Node: int keyId>");
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(file,
                            catalog("REGION.CONFIG"));
            JsonObject action = fieldAction("<Node: int keyId>");
            JsonObject selected = selection.select("REGION.CONFIG",
                    one(action)).get(0).getAsJsonObject();
            assertEquals("SYMBOLIC", selected.get("mode").getAsString());
            assertTrue(selection.selectedForDiscovery("REGION.CONFIG",
                    action));
        } finally {
            Files.deleteIfExists(file);
        }
    }

    /** A configured field that a Java hook already mints stays the hook's:
     * one field is one root, and the hook owns it. */
    @Test
    public void configuredFileCannotMintSecondRootForHookField()
            throws Exception {
        JsonObject regionA = region("REGION.A", "getCausynthValueA");
        Path file = selectionFile("REGION.A", "<Node: long value0>");
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(file,
                            Collections.singletonList(regionA));
            JsonObject action = fieldAction("<Node: long value0>");
            JsonObject selected = selection.select("REGION.A", one(action))
                    .get(0).getAsJsonObject();
            assertEquals("CONCRETE", selected.get("mode").getAsString());
            assertEquals("CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED",
                    selected.get("symbolicDemand").getAsString());
            assertFalse(selection.selectedForDiscovery("REGION.A", action));
        } finally {
            Files.deleteIfExists(file);
        }
    }

    /**
     * The refusal that decides a cross-service key path: once a selection
     * file exists it is the whole allowlist, so a region it simply does not
     * mention admits nothing at all.  A row for a sibling region is not a row
     * for this one.
     */
    @Test
    public void aRegionWithNoRowOfItsOwnAdmitsNothing() throws Exception {
        Path file = selectionFile("REGION.OTHER", "<Node: int keyId>");
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(file,
                            catalog("REGION.OTHER", "REGION.CONFIG"));
            JsonObject action = fieldAction("<Node: int keyId>");
            JsonObject selected = selection.select("REGION.CONFIG",
                    one(action)).get(0).getAsJsonObject();
            assertEquals("CONCRETE", selected.get("mode").getAsString());
            assertEquals("CONFIGURED_SYMBOLIC_INPUT_UNSELECTED",
                    selected.get("symbolicDemand").getAsString());
            assertFalse(selection.selectedForDiscovery("REGION.CONFIG",
                    action));
            // The region that does own the row still keeps its field.
            assertEquals("SYMBOLIC", selection.select("REGION.OTHER",
                    one(fieldAction("<Node: int keyId>"))).get(0)
                    .getAsJsonObject().get("mode").getAsString());
        } finally {
            Files.deleteIfExists(file);
        }
    }

    /**
     * An accessor read names its field only as the callee's declared field,
     * and that name is the one the allowlist has to match; matching the
     * access name alone would silently refuse every accessor-reached leaf.
     */
    @Test
    public void aDeclaredFieldSignatureIsMatchedToo() throws Exception {
        Path file = selectionFile("REGION.CONFIG", "<Node: int keyId>");
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(file,
                            catalog("REGION.CONFIG"));
            JsonObject action = new JsonObject();
            action.addProperty("mode", "SYMBOLIC");
            action.addProperty("declaredFieldSignature", "<Node: int keyId>");
            action.addProperty("symbol", "IN.0");
            assertEquals("SYMBOLIC", selection.select("REGION.CONFIG",
                    one(action)).get(0).getAsJsonObject()
                    .get("mode").getAsString());
            // A different declared field is still refused.
            JsonObject other = new JsonObject();
            other.addProperty("mode", "SYMBOLIC");
            other.addProperty("declaredFieldSignature", "<Node: int other>");
            other.addProperty("symbol", "IN.1");
            assertEquals("CONFIGURED_SYMBOLIC_INPUT_UNSELECTED",
                    selection.select("REGION.CONFIG", one(other)).get(0)
                            .getAsJsonObject().get("symbolicDemand")
                            .getAsString());
        } finally {
            Files.deleteIfExists(file);
        }
    }

    /** A port id and a cell are the other two names the allowlist accepts. */
    @Test
    public void aDeclaredPortIdOrCellAlsoAdmits() throws Exception {
        JsonObject row = emptySelectionRow("REGION.CONFIG");
        row.getAsJsonArray("portIds").add("REGION.CONFIG.in.7");
        row.getAsJsonArray("cells").add("<Node: void run()>#u3.fieldReceiver");
        Path file = Files.createTempFile("causynth-symbolic-inputs",
                ".jsonl");
        try {
            Files.write(file, (CanonicalJson.render(row) + "\n")
                    .getBytes(StandardCharsets.UTF_8));
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(file,
                            catalog("REGION.CONFIG"));
            JsonObject byPort = new JsonObject();
            byPort.addProperty("mode", "SYMBOLIC");
            byPort.addProperty("portId", "REGION.CONFIG.in.7");
            assertEquals("SYMBOLIC", selection.select("REGION.CONFIG",
                    one(byPort)).get(0).getAsJsonObject()
                    .get("mode").getAsString());

            JsonObject byCell = new JsonObject();
            byCell.addProperty("mode", "SYMBOLIC");
            byCell.addProperty("cell",
                    "<Node: void run()>#u3.fieldReceiver");
            assertEquals("SYMBOLIC", selection.select("REGION.CONFIG",
                    one(byCell)).get(0).getAsJsonObject()
                    .get("mode").getAsString());
        } finally {
            Files.deleteIfExists(file);
        }
    }

    /**
     * The allowlist can only refuse.  A read an earlier pass already decided
     * is concrete - a leaf reached across a reference boundary, say - is
     * carried through untouched, so no selection file can overturn that
     * decision or restate it under the allowlist's own name.
     */
    @Test
    public void anAlreadyConcreteActionIsCarriedThroughUnchanged()
            throws Exception {
        Path file = selectionFile("REGION.CONFIG", "<Node: int keyId>");
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(file,
                            catalog("REGION.CONFIG"));
            JsonObject action = fieldAction("<Node: int keyId>");
            action.addProperty("mode", "CONCRETE");
            action.addProperty("symbolicDemand",
                    "CONCRETE_REFERENCE_BOUNDARY_REPLAY");
            JsonObject selected = selection.select("REGION.CONFIG",
                    one(action)).get(0).getAsJsonObject();
            assertEquals(action, selected);
        } finally {
            Files.deleteIfExists(file);
        }
    }

    @Test(expected = java.io.IOException.class)
    public void configuredRegionMustExistInTheFreshStaticCatalog()
            throws Exception {
        Path file = selectionFile("REGION.CONFIG", "<Node: int keyId>");
        try {
            ConcolicScheduler.SymbolicInputSelection.read(file,
                    catalog("REGION.DIFFERENT"));
        } finally {
            Files.deleteIfExists(file);
        }
    }

    @Test
    public void malformedExplicitSelectionArraysAreRejected()
            throws Exception {
        List<JsonObject> malformedRows = new ArrayList<>();

        JsonObject nonArrayFields = emptySelectionRow("REGION.CONFIG");
        nonArrayFields.addProperty("fieldSignatures", "not-an-array");
        malformedRows.add(nonArrayFields);

        JsonObject numericPort = emptySelectionRow("REGION.CONFIG");
        numericPort.getAsJsonArray("portIds").add(7);
        malformedRows.add(numericPort);

        JsonObject emptyCell = emptySelectionRow("REGION.CONFIG");
        emptyCell.getAsJsonArray("cells").add("  ");
        malformedRows.add(emptyCell);

        JsonObject noRegion = emptySelectionRow("REGION.CONFIG");
        noRegion.addProperty("regionId", "");
        malformedRows.add(noRegion);

        for (JsonObject malformed : malformedRows) {
            Path file = Files.createTempFile(
                    "causynth-malformed-symbolic-inputs", ".jsonl");
            try {
                Files.write(file, (CanonicalJson.render(malformed) + "\n")
                        .getBytes(StandardCharsets.UTF_8));
                try {
                    ConcolicScheduler.SymbolicInputSelection.read(file,
                            catalog("REGION.CONFIG"));
                    fail("malformed explicit selection must be rejected: "
                            + malformed);
                } catch (java.io.IOException expected) {
                    // Expected.
                }
            } finally {
                Files.deleteIfExists(file);
            }
        }
    }

    @Test(expected = java.io.IOException.class)
    public void malformedStaticHookDeclarationIsRejected() throws Exception {
        JsonObject regionA = region("REGION.A", "getCausynthValueA");
        regionA.getAsJsonArray(StaticSymbolicSourceDeclaration.FIELD).get(0)
                .getAsJsonObject().addProperty("authority", "GUESSED");
        ConcolicScheduler.SymbolicInputSelection.read(null,
                Collections.singletonList(regionA));
    }

    @Test(expected = java.io.IOException.class)
    public void oneStaticSourceIdCannotDeclareTwoFields() throws Exception {
        JsonObject regionA = region("REGION.A", "getCausynthValueA");
        JsonArray sources = regionA.getAsJsonArray(
                StaticSymbolicSourceDeclaration.FIELD);
        JsonObject repeated = sources.get(0).getAsJsonObject().deepCopy();
        repeated.addProperty("fieldSignature", "<Node: long other>");
        repeated.addProperty("declarationUnitIndex", 99);
        sources.add(repeated);
        ConcolicScheduler.SymbolicInputSelection.read(null,
                Collections.singletonList(regionA));
    }

    private static JsonArray one(JsonObject action) {
        JsonArray actions = new JsonArray();
        actions.add(action);
        return actions;
    }

    private static JsonObject fieldAction(String fieldSignature) {
        JsonObject action = new JsonObject();
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("accessFieldSignature", fieldSignature);
        action.addProperty("symbol", "IN.0");
        return action;
    }

    private static Path selectionFile(String regionId, String fieldSignature)
            throws java.io.IOException {
        JsonObject row = emptySelectionRow(regionId);
        row.getAsJsonArray("fieldSignatures").add(fieldSignature);
        Path file = Files.createTempFile(
                "causynth-symbolic-inputs", ".jsonl");
        Files.write(file, (CanonicalJson.render(row) + "\n")
                .getBytes(StandardCharsets.UTF_8));
        return file;
    }

    private static JsonObject emptySelectionRow(String regionId) {
        JsonObject row = new JsonObject();
        row.addProperty("regionId", regionId);
        row.add("fieldSignatures", new JsonArray());
        row.add("portIds", new JsonArray());
        row.add("cells", new JsonArray());
        return row;
    }

    private static List<JsonObject> catalog(String... regionIds) {
        List<JsonObject> result = new ArrayList<>();
        for (String regionId : regionIds) {
            JsonObject region = new JsonObject();
            region.addProperty("regionId", regionId);
            result.add(region);
        }
        return result;
    }

    private static JsonObject region(String regionId, String method) {
        JsonObject region = new JsonObject();
        region.addProperty("schemaVersion", 3);
        region.addProperty("kind", "SYMBOLIC_REGION");
        region.addProperty("regionId", regionId);
        JsonArray sources = new JsonArray();
        for (int index = 0; index < IDS.size(); index++) {
            JsonObject source = new JsonObject();
            source.addProperty("schemaVersion",
                    StaticSymbolicSourceDeclaration.SCHEMA_VERSION);
            source.addProperty("kind",
                    StaticSymbolicSourceDeclaration.KIND);
            source.addProperty("authority",
                    StaticSymbolicSourceDeclaration.AUTHORITY);
            source.addProperty("sourceId", IDS.get(index));
            source.addProperty("fieldSignature",
                    "<Node: long value" + index + ">");
            source.addProperty("declarationMethod", "<Node: void "
                    + method + "Symbols()>");
            source.addProperty("declarationUnitIndex", index);
            sources.add(source);
        }
        region.add(StaticSymbolicSourceDeclaration.FIELD, sources);
        return region;
    }
}

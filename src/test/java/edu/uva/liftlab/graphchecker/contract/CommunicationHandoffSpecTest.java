package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class CommunicationHandoffSpecTest {
    @Test
    public void decodesTheFourCaptureKindsWithOneSideModel() {
        JsonObject task = new JsonObject();
        JsonArray rows = new JsonArray();
        rows.add(site("p0", CommunicationHandoffSpec.OUT,
                CommunicationCatalogContract.CAPTURE_METHOD_RETURN));
        rows.add(site("p1", CommunicationHandoffSpec.IN,
                CommunicationCatalogContract.CAPTURE_METHOD_PARAMETER));
        rows.add(site("p2", CommunicationHandoffSpec.OUT,
                CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT));
        rows.add(site("p3", CommunicationHandoffSpec.IN,
                CommunicationCatalogContract.CAPTURE_CALL_RETURN));
        task.add(CommunicationHandoffSpec.FIELD, rows);

        List<CommunicationHandoffSpec> sites =
                CommunicationHandoffSpec.decode(task);
        assertEquals(4, sites.size());
        assertTrue(sites.get(0).outgoing());
        assertTrue(sites.get(1).incoming());
        assertEquals(CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT,
                sites.get(2).captureKind());
        assertFalse(sites.get(3).outgoing());
        assertEquals("<example.Flow: int run()>#u7",
                sites.get(3).siteId());
    }

    @Test(expected = IllegalArgumentException.class)
    public void rejectsRowsWithoutTheNewSideAndCaptureKind() {
        JsonObject task = new JsonObject();
        JsonArray rows = new JsonArray();
        JsonObject old = site("old", CommunicationHandoffSpec.OUT,
                CommunicationCatalogContract.CAPTURE_CALL_RETURN);
        old.remove(CommunicationHandoffSpec.SIDE);
        old.remove(CommunicationHandoffSpec.CAPTURE_KIND);
        old.addProperty("role", "ATTACH");
        rows.add(old);
        task.add(CommunicationHandoffSpec.FIELD, rows);
        CommunicationHandoffSpec.decode(task);
    }

    private static JsonObject site(String port, String side, String capture) {
        JsonObject row = new JsonObject();
        row.addProperty("portId", port);
        row.addProperty("handoffLeafPath", port);
        row.addProperty("direction", "RESPONSE");
        row.addProperty("javaType", "int");
        row.addProperty(CommunicationHandoffSpec.SIDE, side);
        row.addProperty(CommunicationHandoffSpec.CAPTURE_KIND, capture);
        row.addProperty("definitionMethod", "<example.Flow: int run()>");
        if (CommunicationCatalogContract.CAPTURE_METHOD_PARAMETER.equals(
                capture)) {
            row.addProperty("argumentIndex", 0);
        } else if (CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT.equals(
                capture)) {
            row.addProperty("argumentIndex", 0);
            row.addProperty("definitionUnitIndex", 7);
            row.addProperty("declaredCallee", "<example.Http: int send(int)>");
        } else if (CommunicationCatalogContract.CAPTURE_CALL_RETURN.equals(
                capture)) {
            row.addProperty("definitionUnitIndex", 7);
            row.addProperty("declaredCallee", "<example.Http: int send(int)>");
        }
        return row;
    }
}

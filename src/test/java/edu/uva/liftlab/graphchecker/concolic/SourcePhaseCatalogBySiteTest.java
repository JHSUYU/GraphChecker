package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.SiteId;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * One phase id across two executions is a catalog, not a malformed one.
 *
 * <p>A configured source is declared by SITE, so it is one variable per
 * replay and its catalog carries one id for every execution of that site.
 * The importer indexed the catalog by id and raised on the second row, which
 * rejected every region path whose site ran more than once: lane BH's 50
 * {@code REGION_PATH_ADMISSION_REJECTED}, every one of them naming
 * {@code SOURCE_PHASE.05975245-3fb5-356a-913e-d5e369ce3b2e}.</p>
 */
public class SourcePhaseCatalogBySiteTest {
    private static final String SOURCE_ID = "HDFS.CONFIG.ORDERED";
    private static final String METHOD =
            "<a.Manager: boolean isSnapshotDeletionOrdered()>";
    private static final String FIELD =
            "<a.Manager: boolean snapshotDeletionOrdered>";
    private static final int UNIT = 1;
    private static final String OCCURRENCE =
            "hdfs/nn0#epoch1/region/REGION.r#1";

    /** Two executions of one site, one id, and the mint is admitted. */
    @Test
    public void aRepeatedPhaseIdIsOneVariableNotAMalformedCatalog() {
        List<ConfiguredSourcePhaseContract.Occurrence> catalog = catalog();
        assertEquals("the catalog holds both executions", 2, catalog.size());
        assertEquals("under one identity", catalog.get(0).phaseId(),
                catalog.get(1).phaseId());

        List<String> issues = new ArrayList<>();
        JsonArray admitted = ConcolicSummaryImporter.symbolicSourceEvidence(
                row(catalog.get(0).phaseId(), 1), catalog, issues);

        assertEquals(issues.toString(), 0, issues.size());
        assertEquals("the mint is admitted", 1, admitted.size());
    }

    /** A second observation of one site is the same root, admitted once. */
    @Test
    public void aSecondObservationOfOneSiteIsNotASecondRoot() {
        List<ConfiguredSourcePhaseContract.Occurrence> catalog = catalog();
        List<String> issues = new ArrayList<>();

        JsonArray admitted = ConcolicSummaryImporter.symbolicSourceEvidence(
                row(catalog.get(0).phaseId(), 2), catalog, issues);

        assertEquals(issues.toString(), 0, issues.size());
        assertEquals("one variable, admitted once", 1, admitted.size());
    }

    /** A mint naming no declared site is still refused. */
    @Test
    public void anUndeclaredPhaseIsStillRefused() {
        List<String> issues = new ArrayList<>();

        ConcolicSummaryImporter.symbolicSourceEvidence(
                row("SOURCE_PHASE.00000000-0000-3000-8000-000000000000", 1),
                catalog(), issues);

        assertEquals(1, issues.size());
        assertTrue(issues.get(0),
                issues.get(0).startsWith("SYMBOLIC_SOURCE_EVIDENCE_NOT_"
                        + "DECLARED"));
    }

    // ---------- fixtures ----------

    private static List<ConfiguredSourcePhaseContract.Occurrence> catalog() {
        JsonObject declaration = ConfiguredSourcePhaseContract.declaration(
                ConfiguredSourcePhaseContract.Phase.PUBLISH, SOURCE_ID,
                FIELD, METHOD, UNIT);
        JsonArray declarations = new JsonArray();
        declarations.add(declaration);
        ConfiguredSourcePhaseContract.Declaration declared =
                ConfiguredSourcePhaseContract.declarationsOf(declarations)
                        .get(0);
        JsonArray phases = new JsonArray();
        phases.add(ConfiguredSourcePhaseContract.occurrence(declared,
                OCCURRENCE, 1, 11L, 7L, 3L, METHOD, Arrays.asList(7L, 5L)));
        phases.add(ConfiguredSourcePhaseContract.occurrence(declared,
                OCCURRENCE, 2, 12L, 7L, 4L, METHOD, Arrays.asList(7L, 5L)));
        return ConfiguredSourcePhaseContract.occurrencesOf(phases);
    }

    /** One replay row publishing {@code mints} mint events of one site. */
    private static ConcolicSummaryImporter.ResultRow row(String phaseId,
                                                         int mints) {
        // The mint's root carries this phase's own engine label, which is
        // what makes it this phase's mint rather than a value that only
        // travelled here.
        String raw = "M_Z_field_" + SymbolicSourceEvidence
                .engineLabelForPhase(phaseId, SOURCE_ID) + "_1";
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_exp", raw);
        symbol.addProperty("_java_type", "boolean");
        JsonArray events = new JsonArray();
        for (int index = 1; index <= mints; index++) {
            events.add(SymbolicSourceEvidence.event(phaseId, SOURCE_ID,
                    OCCURRENCE, FIELD, symbol, index, false, raw, "true"));
        }
        JsonObject result = new JsonObject();
        result.addProperty("event", "CONCOLIC_REGION_RESULT");
        result.addProperty("occurrenceId", OCCURRENCE);
        result.add(SymbolicSourceEvidence.FIELD, events);
        return new ConcolicSummaryImporter.ResultRow(result, 0);
    }
}

package edu.uva.liftlab.graphchecker.grey;

import org.junit.Test;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class GreyTraceEvidenceIngestorTest {
    @Test
    public void marksStaticEventsAsUnobservedWhenTraceFileIsMissing() throws Exception {
        GreyStateAnalysisResult result = new GreyStateAnalysisResult();
        result.addEvent(new SemanticEvent("GREY_ENCODE", "m", "u", null));

        GreyTraceEvidenceIngestor.EvidenceResult evidence =
                new GreyTraceEvidenceIngestor().ingest(result, Files.createTempDirectory("grey").resolve("missing.jsonl"));

        assertEquals(1, evidence.getStaticEvents());
        assertEquals(0, evidence.getObservedEvents());
        assertEquals(false, evidence.getEvidence().get(0).get("trace_observed"));
    }

    @Test
    public void matchesTraceObservationByStableEventId() throws Exception {
        SemanticEvent event = new SemanticEvent("GREY_DECODE", "method", "unit",
                Collections.singletonMap("parsedIndex", "0"));
        GreyStateAnalysisResult result = new GreyStateAnalysisResult();
        result.addEvent(event);
        Path trace = Files.createTempFile("grey-trace", ".jsonl");
        String line = "{\"event_id\":\"" + event.stableId()
                + "\",\"event_type\":\"GREY_DECODE\",\"test\":\"unit\"}\n";
        Files.write(trace, line.getBytes(StandardCharsets.UTF_8));

        GreyTraceEvidenceIngestor.EvidenceResult evidence =
                new GreyTraceEvidenceIngestor().ingest(result, trace);

        assertEquals(1, evidence.getStaticEvents());
        assertEquals(1, evidence.getObservedEvents());
        assertEquals(true, evidence.getEvidence().get(0).get("trace_observed"));
        assertTrue(evidence.observedEventTypes().contains("GREY_DECODE"));
    }
}

package edu.uva.liftlab.graphchecker.grey;

import edu.uva.liftlab.graphchecker.grey.fixture.GreyStateFixture;
import org.junit.After;
import org.junit.Test;
import soot.G;
import soot.Scene;
import soot.SootClass;
import soot.options.Options;

import java.util.Arrays;

import static org.junit.Assert.assertTrue;

public class GreyStateConeExtractorTest {
    @After
    public void tearDown() {
        G.reset();
    }

    @Test
    public void extractsGreyStateEventsFromFixtureCone() {
        loadFixtureClass(GreyStateFixture.class.getName());
        GreyStateSpec spec = new GreyStateSpec(
                Arrays.asList(new GreyStateSpec.FatalSeed(
                        "fixture",
                        GreyStateFixture.class.getName(),
                        "retrieveDataEncryptionKey",
                        GreyStateFixture.InvalidEncryptionKeyException.class.getName())),
                Arrays.asList(GreyStateFixture.class.getName()),
                "target/grey-fixture-output",
                3);

        GreyStateAnalysisResult result = new GreyStateConeExtractor().extract(spec);

        assertTrue(hasEvent(result, "VALIDATE_MAP_LOOKUP"));
        assertTrue(hasEvent(result, "MAP_PUT"));
        assertTrue(hasEvent(result, "MAP_REMOVE"));
        assertTrue(hasEvent(result, "CACHE_PUT"));
        assertTrue(hasEvent(result, "DERIVE_METADATA"));
        assertTrue(hasEvent(result, "SEND_METADATA"));
        assertTrue(hasEvent(result, "RECEIVE_METADATA"));
        assertTrue(hasEvent(result, "PERIODIC_TRANSITION"));
        assertTrue(hasEvent(result, "RECOVERY_NO_REPAIR"));
        assertTrue(hasSummary(result, "fatal_predicate"));
    }

    private boolean hasEvent(GreyStateAnalysisResult result, String type) {
        for (SemanticEvent event : result.getEvents()) {
            if (type.equals(event.getEventType())) {
                return true;
            }
        }
        return false;
    }

    private boolean hasSummary(GreyStateAnalysisResult result, String type) {
        for (TransitionSummary summary : result.getTransitionSummaries()) {
            if (type.equals(summary.getSummaryType())) {
                return true;
            }
        }
        return false;
    }

    private SootClass loadFixtureClass(String className) {
        G.reset();
        Options.v().set_prepend_classpath(true);
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_output_format(Options.output_format_none);
        Options.v().set_whole_program(true);
        Options.v().set_soot_classpath(System.getProperty("java.class.path"));
        SootClass sootClass = Scene.v().forceResolve(className, SootClass.BODIES);
        sootClass.setApplicationClass();
        Scene.v().loadNecessaryClasses();
        return sootClass;
    }
}

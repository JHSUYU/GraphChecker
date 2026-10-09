package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.DeclaredSiteCapture;
import edu.uva.liftlab.graphchecker.plan.RuntimeWorkflowDiscovery;
import edu.uva.liftlab.graphchecker.plan.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveBoxing;
import java.io.IOException;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.junit.After;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import soot.ArrayType;
import soot.DoubleType;
import soot.G;
import soot.IntType;
import soot.Local;
import soot.LongType;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.VoidType;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * The region graph joins on an address.  It only scopes: it never decides
 * what matters, picks an arm, or names a writer.
 */
public class RegionGraphOccurrenceKeyTest {
    /** One planned occurrence, as identity v3 addresses it. */
    private static final String PLANNED =
            "hdfs-17960/nn0#epoch1/region/"
                    + "REGION.9492ec77-0f65-34ba-a3af-14753ac7347d"
                    + "/ctx:Root:KEY_MANAGER_TICK#1"
                    + "/idx:o.a.h.h.s.n.FSNamesystem#saveNamespace#12@0";

    @Rule
    public TemporaryFolder tree = new TemporaryFolder();

    @After
    public void resetSoot() {
        G.reset();
    }

    /**
     * An address two activations landed on STATES ITS CLASS, which is
     * whether the kept closure retains that occurrence: then a task
     * addresses it and the ambiguity withholds; otherwise no plan row, no
     * task and no session row names it and the row is telemetry, whatever
     * else of its region is planned.  All three rows of the reviewed
     * hdfs-17960 run were the second case -- {@code FSDirectory$InitQuotaTask}
     * ForkJoin siblings, whose regions the closure drops -- and they were
     * published with no class at all, which the campaign reads as blocking.
     */
    @Test
    public void aSharedAddressStatesItsClass() throws Exception {
        assertEquals("BLOCKING", sharedAddressClass(PLANNED));
        assertEquals("DIAGNOSTIC", sharedAddressClass(
                PLANNED.replace("TICK#1", "TICK#2")));
    }

    /** The class the finalizer states for one shared address of the kept
     *  region, the closure retaining {@code retained} of it. */
    private static String sharedAddressClass(String retained)
            throws Exception {
        String regionId = "REGION.kept";
        StaticProgram program = new StaticProgram();
        Map<String, Object> kept = new LinkedHashMap<String, Object>();
        kept.put("regionId", regionId);
        kept.put("runtimeOccurrenceIds", Collections.singletonList(retained));
        program.regions.add(kept);
        Map<String, Object> shared = new LinkedHashMap<String, Object>();
        shared.put("occurrenceId", PLANNED);
        shared.put("regionId", regionId);
        shared.put(RuntimeSelectedRegionFinalizer.SHARED_ADDRESS_ROOT_CALLS,
                Arrays.asList(26744L, 26745L));
        Method rule = RuntimeSelectedRegionFinalizer.class
                .getDeclaredMethod("stateSharedAddressClasses",
                        StaticProgram.class, List.class);
        rule.setAccessible(true);
        rule.invoke(null, program,
                Collections.singletonList(shared));
        assertEquals(1, program.planGaps.size());
        Map<String, Object> row = program.planGaps.get(0);
        assertEquals("OCCURRENCE_ADDRESS_SHARED", row.get("kind"));
        // The detail says WHICH rule answered, so a reader is not left to
        // infer the class from the code.
        assertTrue(String.valueOf(row.get("detail")),
                String.valueOf(row.get("detail"))
                        .contains(row.get("cls") + ": the closure"));
        return String.valueOf(row.get("cls"));
    }

    /**
     * WHAT THE RECORDING HELD decides where the failure's demand crosses
     * (SYMBOL-SCOPE §4.4).  A stored field is one object's: of the
     * occurrences on the reader's node that ran its storing method, the walk
     * plans those the recording saw access it on the object the reader read
     * it on, or on no object (a store on an arm it did not take), never one
     * that held other objects only, nor one on another node.  A message is
     * one exchange leg: an attach whose value reaches what is demanded plans
     * the occurrence that exported it on that leg, never an export of the
     * same port on another leg -- the unconditional admission of every
     * capture planned 2673 occurrences for one ad-hoc check (a40h-5).  An
     * attach no export of its leg pairs with is a RELAY: its message's sender
     * handed on what it had received, so the walk plans the exports of the
     * port on the legs the sender's captures took it from before it sent,
     * never one it received after (hdfs-adhoc-07: the QJM client hands a
     * journal node's segment to jn0's acceptRecovery).  An occurrence whose
     * address two activations share is planned by no rule: no plan row can
     * name one run of it (hdfs-adhoc-07 EX1: two of jn1's edit-log scans in
     * unnamed work, reached as writers, were planned and BLOCKING).  A
     * store writes its holder's field, so a writer holding what the reader
     * held through another holder is none (a40s ReindexCollectionCmd-369:
     * every lambda capturing one ZooKeeper client), where a mutation through
     * the field writes what it held; and an edge of a method
     * the occurrence never ran demands nothing (the target never ran ALT,
     * which reads OTHER).  An occurrence that took the arm of a guard of the
     * store away from it is a writer too: the store is on the arm it did not
     * take, one flip away (hdfs-bugs slowdisk-zero: the detector's turns
     * decide {@code max > 0}, over a tracked read, and never ran the store
     * behind it); one that ran the guard's method without reaching the
     * guard, took its arm toward the store, or left it at a decision no
     * tracked read, root or attach reaches there, is not -- the last stated
     * per region.
     */
    @Test
    public void theWalkCrossesWhatTheRecordingHeld() throws Exception {
        Object[][] activations = {
                // name, node, region, owners of EPOCH, its referents, attach
                // leg, export leg
                {"target", "wl/nn0#epoch0", "REGION.check", 7, 9, "", ""},
                {"same-object", "wl/nn0#epoch0", "REGION.bump", 7, 0, "L1",
                        ""},
                {"other-object", "wl/nn0#epoch0", "REGION.bump", 8, 0, "L2",
                        ""},
                {"same-referent", "wl/nn0#epoch0", "REGION.bump", 8, 9, "",
                        ""},
                {"mutation", "wl/nn0#epoch0", "REGION.grow", 8, 9, "", ""},
                {"no-access", "wl/nn0#epoch0", "REGION.bump", 0, 0, "", ""},
                {"other-node", "wl/dn0#epoch0", "REGION.bump", 7, 0, "", ""},
                {"paired-export", "wl/dn0#epoch0", "REGION.send", 0, 0, "",
                        "L1"},
                {"other-leg", "wl/dn0#epoch0", "REGION.send", 0, 0, "", "L2"},
                {"unran-edge", "wl/nn0#epoch0", "REGION.side", 0, 0, "", ""},
                {"decider", "wl/nn0#epoch0", "REGION.loop", 0, 0, "", ""},
                {"undecided", "wl/nn0#epoch0", "REGION.loop", 0, 0, "", ""},
                {"toward", "wl/nn0#epoch0", "REGION.loop", 0, 0, "", ""},
                {"fixed", "wl/nn0#epoch0", "REGION.loop", 0, 0, "", ""},
                // + the leg it sent at seq 20, its attach's seq
                {"relay-consumer", "wl/nn0#epoch0", "REGION.bump", 7, 0, "L3",
                        "", "", 0L},
                {"relay-sender", "wl/client0#epoch0", "REGION.send", 0, 0,
                        "L4", "", "L3", 10L},
                {"late-sender", "wl/client0#epoch0", "REGION.send", 0, 0,
                        "L5", "", "L3", 30L},
                {"relayed-export", "wl/dn1#epoch0", "REGION.send", 0, 0, "",
                        "L4"},
                {"late-export", "wl/dn1#epoch0", "REGION.send", 0, 0, "",
                        "L5"},
                // two activations of one address, each a writer of EPOCH
                {"shared-writer", "wl/nn0#epoch0", "REGION.bump", 7, 0, "",
                        ""},
                {"shared-writer-again", "wl/nn0#epoch0", "REGION.bump", 7, 0,
                        "", ""},
        };
        List<Map<String, Object>> instances = new ArrayList<>();
        Map<String, String> addresses = new LinkedHashMap<>();
        for (int index = 0; index < activations.length; index++) {
            Object[] row = activations[index];
            String address = OccurrenceAddress.of(
                    NodeId.parse((String) row[1]), (String) row[2],
                    CausalContext.of(Role.of("CLIENT"), "",
                            ((String) row[0]).startsWith("shared") ? 999
                                    : index + 1),
                    ExecutionIndex.empty()).render();
            addresses.put((String) row[0], address);
            String method = "REGION.check".equals(row[2]) ? CHECK
                    : "REGION.bump".equals(row[2]) ? BUMP
                    : "REGION.side".equals(row[2]) ? SIDE
                    : "REGION.grow".equals(row[2]) ? GROW
                    : "REGION.loop".equals(row[2]) ? LOOP : SEND;
            Map<String, Object> activation = row(
                    "kind", "RUNTIME_REGION_ACTIVATION",
                    "regionId", row[2],
                    "rootCallId", (long) index + 1,
                    "occurrenceAddress", address,
                    "selection", "REGION.check".equals(row[2])
                            ? "EXCEPTION_CONTEXT" : "STATE_CONTEXT",
                    "callIds", Collections.singletonList((long) index + 1),
                    "observedMethods", Collections.singletonList(method));
            if ((Integer) row[3] != 0) {
                activation.put(RuntimeSelectedRegionFinalizer.FIELD_OWNERS,
                        Collections.singletonMap(EPOCH,
                                Collections.singleton(row[3])));
            }
            if ((Integer) row[4] != 0) {
                activation.put(RuntimeSelectedRegionFinalizer.FIELD_REFERENTS,
                        Collections.singletonMap(EPOCH,
                                Collections.singleton(row[4])));
            }
            List<Map<String, Object>> captures = new ArrayList<>();
            if (!((String) row[5]).isEmpty()) {
                captures.add(row("side", "IN", "portId", PORT,
                        "exchangeLeg", row[5], "eventSeq",
                        row.length > 8 ? row[8] : 0L));
            }
            if (row.length > 7 && !((String) row[7]).isEmpty()) {
                activation.put(RuntimeSelectedRegionFinalizer
                        .SENT_EXCHANGE_LEGS, Collections.singletonList(row(
                        "exchangeLeg", row[7], "transportEventSeq", 20L)));
            }
            if (!((String) row[6]).isEmpty()) {
                captures.add(row("side", "OUT", "portId", PORT,
                        "exchangeLeg", row[6]));
            }
            activation.put(RuntimeSelectedRegionFinalizer
                    .OBSERVED_COMMUNICATION_CAPTURES, captures);
            instances.add(activation);
        }
        RuntimeSelectedRegionFinalizer.Result closure =
                RuntimeSelectedRegionFinalizer.finalizeRegions(walkGraph(),
                        walkSkeletons(), "test", Arrays.asList(CHECK, BUMP,
                                SEND, SIDE, GROW, LOOP), instances,
                        Arrays.asList(row("kind", "BRANCH",
                                "eventSeq", 5L, "method", CHECK,
                                "callId", 1L, "siteId", CHECK + "#u5",
                                "outcome", Boolean.TRUE),
                                row("kind", "BRANCH", "eventSeq", 6L,
                                        "method", LOOP, "callId", 11L,
                                        "siteId", LOOP + "#u3",
                                        "outcome", Boolean.FALSE),
                                row("kind", "BRANCH", "eventSeq", 7L,
                                        "method", LOOP, "callId", 13L,
                                        "siteId", LOOP + "#u3",
                                        "outcome", Boolean.TRUE),
                                row("kind", "BRANCH", "eventSeq", 8L,
                                        "method", LOOP, "callId", 14L,
                                        "siteId", LOOP + "#u5",
                                        "outcome", Boolean.FALSE)),
                        walkScopeMap(), RuntimeWorkflowDiscovery.FIRST,
                        Collections.<ScheduleEvent>emptyList(),
                        new RecordedAccesses.Builder().build(),
                new RecordedHeap.Builder().build());
        List<String> planned = new ArrayList<>();
        for (Map<String, Object> region : closure.regions) {
            for (Object occurrence
                    : (List<?>) region.get("runtimeOccurrenceIds")) {
                for (Map.Entry<String, String> named : addresses.entrySet()) {
                    if (named.getValue().equals(occurrence)) {
                        planned.add(named.getKey());
                    }
                }
            }
        }
        Collections.sort(planned);
        assertEquals(Arrays.asList("decider", "mutation", "no-access",
                "paired-export", "relay-consumer", "relayed-export",
                "same-object", "target"), planned);
        List<String> fixed = new ArrayList<>();
        for (Map<String, Object> gap : closure.gaps) {
            if (String.valueOf(gap.get("detail")).contains("no world the "
                    + "engine expresses makes them store")) {
                fixed.add(gap.get("subject") + " "
                        + String.valueOf(gap.get("detail")).split(" ")[0]);
            }
        }
        assertEquals(Collections.singletonList("REGION.loop 1"), fixed);
    }

    /**
     * A READER THAT NEVER TOUCHED THE FIELD read it on an arm the recording
     * did not take, on an object it could reach there (solr-adhoc-10 SG1:
     * the target reads NamedList.nvPairs only so, and 3,815 request
     * handlers' writes of their own responses were each its writer): one
     * its events name, one a static field held, or one those held over the
     * recorded heap.  A writer is not crossed to only when no object it
     * wrote the field on is reachable, and each was seen held or, held by
     * nothing recorded, was mentioned by its own occurrence alone or on one
     * thread alone, not the reader's; one held by nothing and mentioned on
     * a second thread or on the reader's, or a static field's location, is
     * crossed to.  The reader states, per field, how many it did not cross
     * to by each rule, and how many it crossed to for a mention.
     */
    @Test
    public void aReaderThatNeverTouchedTheFieldReachesWhatItNames()
            throws Exception {
        Object[][] activations = {
                // name, region, owner of EPOCH (-1: none)
                {"target", "REGION.check", -1},
                {"reachable", "REGION.bump", 7},
                {"held-elsewhere", "REGION.bump", 8},
                {"never-held", "REGION.bump", 9},
                {"under-a-static", "REGION.bump", 11},
                {"static", "REGION.bump", 0},
                {"confined", "REGION.bump", 12},
                {"thread-confined", "REGION.bump", 13},
                {"escaped", "REGION.bump", 14},
                {"on-the-readers-thread", "REGION.bump", 15},
        };
        RecordedHeap.Builder heap = new RecordedHeap.Builder();
        heap.edge(1, 7);
        heap.edge(50, 8);
        heap.root(10);
        heap.edge(10, 11);
        // Held by nothing recorded, the reader (root call 1) on thread 50:
        // 12 mentioned by its writer (root call 7) alone; 13 by its writer
        // (8) and another occurrence, both on thread 51; 14 by its writer
        // (9) on threads 51 and 52; 15 by its writer (10) and another
        // occurrence on the reader's thread.
        heap.rootThread(1L, 50L);
        heap.mention(12, 7L, 51L);
        heap.mention(13, 8L, 51L);
        heap.mention(13, 99L, 51L);
        heap.mention(14, 9L, 51L);
        heap.mention(14, 9L, 52L);
        heap.mention(15, 10L, 50L);
        heap.mention(15, 99L, 50L);
        List<Map<String, Object>> instances = new ArrayList<>();
        Map<String, String> addresses = new LinkedHashMap<>();
        for (int index = 0; index < activations.length; index++) {
            Object[] row = activations[index];
            String address = OccurrenceAddress.of(
                    NodeId.parse("wl/nn0#epoch0"), (String) row[1],
                    CausalContext.of(Role.of("CLIENT"), "", index + 1),
                    ExecutionIndex.empty()).render();
            addresses.put((String) row[0], address);
            Map<String, Object> activation = row(
                    "kind", "RUNTIME_REGION_ACTIVATION",
                    "regionId", row[1],
                    "rootCallId", (long) index + 1,
                    "occurrenceAddress", address,
                    "selection", "REGION.check".equals(row[1])
                            ? "EXCEPTION_CONTEXT" : "STATE_CONTEXT",
                    "callIds", Collections.singletonList((long) index + 1),
                    "observedMethods", Collections.singletonList(
                            "REGION.check".equals(row[1]) ? CHECK : BUMP),
                    RuntimeSelectedRegionFinalizer.NAMED_OBJECTS,
                    new int[] {index + 1});
            if ((Integer) row[2] >= 0) {
                activation.put(RuntimeSelectedRegionFinalizer.FIELD_OWNERS,
                        Collections.singletonMap(EPOCH,
                                Collections.singleton(row[2])));
            }
            activation.put(RuntimeSelectedRegionFinalizer
                    .OBSERVED_COMMUNICATION_CAPTURES,
                    Collections.emptyList());
            instances.add(activation);
        }
        RuntimeSelectedRegionFinalizer.Result closure =
                RuntimeSelectedRegionFinalizer.finalizeRegions(walkGraph(),
                        walkSkeletons(), "test", Arrays.asList(CHECK, BUMP),
                        instances, Collections.singletonList(row(
                                "kind", "BRANCH", "eventSeq", 5L,
                                "method", CHECK, "callId", 1L,
                                "siteId", CHECK + "#u5",
                                "outcome", Boolean.TRUE)),
                        walkScopeMap(), RuntimeWorkflowDiscovery.FIRST,
                        Collections.<ScheduleEvent>emptyList(),
                        new RecordedAccesses.Builder().build(), heap.build());
        List<String> planned = new ArrayList<>();
        for (Map<String, Object> region : closure.regions) {
            for (Object occurrence
                    : (List<?>) region.get("runtimeOccurrenceIds")) {
                for (Map.Entry<String, String> named : addresses.entrySet()) {
                    if (named.getValue().equals(occurrence)) {
                        planned.add(named.getKey());
                    }
                }
            }
        }
        Collections.sort(planned);
        assertEquals(Arrays.asList("escaped", "never-held",
                "on-the-readers-thread", "reachable", "static", "target",
                "under-a-static"), planned);
        for (String member : Arrays.asList(
                RuntimeSelectedRegionFinalizer.UNREACHABLE_WRITERS,
                RuntimeSelectedRegionFinalizer.CONFINED_WRITERS,
                RuntimeSelectedRegionFinalizer.THREAD_CONFINED_WRITERS)) {
            assertEquals(member, Collections.singletonMap(EPOCH, 1),
                    instances.get(0).get(member));
        }
        assertEquals("never-held, escaped and on-the-readers-thread",
                Collections.singletonMap(EPOCH, 3), instances.get(0).get(
                        RuntimeSelectedRegionFinalizer.ESCAPED_WRITERS));
    }

    /**
     * EQUIVALENT DECIDERS ARE PLANNED ONCE A CLASS (hdfs-adhoc-16: 1218 to
     * 1520 polling turns of the block scrubber, each leaving removeBlock's
     * store at its guard, one job each): turns of one region, node and
     * context shape that did the same on the same state (one signature) are
     * one class while nobody else touches a demanded cell between them; the
     * first is planned and states the class.  So are occurrences that ran
     * the storing method and stored nothing.  An access of EPOCH by another
     * call between two turns starts a new class; another signature, a root
     * read and a recorded store are never merged.
     */
    @Test
    public void equivalentDecidersArePlannedOnceAClass() throws Exception {
        Object[][] activations = {
                // name, region, signature, first and last seq, root read
                {"target", "REGION.check", "", 1L, 2L, false},
                {"turn1", "REGION.loop", "S", 10L, 11L, false},
                {"turn2", "REGION.loop", "S", 20L, 21L, false},
                {"turn3", "REGION.loop", "S", 40L, 41L, false},
                {"turn4", "REGION.loop", "S", 50L, 51L, false},
                {"other", "REGION.loop", "T", 60L, 61L, false},
                {"rooted", "REGION.loop", "S", 55L, 56L, true},
                {"store1", "REGION.bump", "B", 80L, 81L, false},
                {"store2", "REGION.bump", "B", 90L, 91L, false},
                {"ran1", "REGION.bump", "B", 100L, 101L, false},
                {"ran2", "REGION.bump", "B", 110L, 111L, false},
        };
        List<Map<String, Object>> instances = new ArrayList<>();
        List<Map<String, Object>> branches = new ArrayList<>();
        branches.add(row("kind", "BRANCH", "eventSeq", 1L, "method", CHECK,
                "callId", 1L, "siteId", CHECK + "#u5",
                "outcome", Boolean.TRUE));
        Map<String, String> addresses = new LinkedHashMap<>();
        for (int index = 0; index < activations.length; index++) {
            Object[] row = activations[index];
            long call = index + 1;
            String address = OccurrenceAddress.of(
                    NodeId.parse("wl/nn0#epoch0"), (String) row[1],
                    CausalContext.of(Role.of("CLIENT"), "", index + 1),
                    ExecutionIndex.empty()).render();
            addresses.put((String) row[0], address);
            String region = (String) row[1];
            Map<String, Object> activation = row(
                    "kind", "RUNTIME_REGION_ACTIVATION",
                    "regionId", region,
                    "rootCallId", call,
                    "occurrenceAddress", address,
                    "selection", "REGION.check".equals(region)
                            ? "EXCEPTION_CONTEXT" : "STATE_CONTEXT",
                    "callIds", Collections.singletonList(call),
                    "observedMethods", Collections.singletonList(
                            "REGION.check".equals(region) ? CHECK
                                    : "REGION.loop".equals(region) ? LOOP
                                    : BUMP),
                    RuntimeSelectedRegionFinalizer.FIELD_OWNERS,
                    Collections.singletonMap(EPOCH,
                            Collections.singleton(7)),
                    RuntimeSelectedRegionFinalizer.FIRST_SEQ, row[3],
                    RuntimeSelectedRegionFinalizer.LAST_SEQ, row[4]);
            if (!((String) row[2]).isEmpty()) {
                activation.put(RuntimeSelectedRegionFinalizer.SIGNATURE,
                        row[2]);
            }
            if ((Boolean) row[5]) {
                activation.put(DeclaredSiteCapture.PLAN_FIELD,
                        Collections.singletonList(row(SiteId.MEMBER,
                                LOOP + "#u1", DeclaredSiteCapture
                                        .DECLARED_CALLEE, CLOCK)));
            }
            if ("REGION.loop".equals(region)) {
                branches.add(row("kind", "BRANCH", "eventSeq", row[3],
                        "method", LOOP, "callId", call,
                        "siteId", LOOP + "#u3", "outcome", Boolean.FALSE));
            }
            instances.add(activation);
        }
        // rooted reads a clock there.
        JsonObject clock = new JsonObject();
        clock.addProperty("kind", "STATIC_SCOPE_SITE");
        clock.addProperty("role", "DECLARED_SITE");
        clock.addProperty("regionId", "REGION.loop");
        clock.addProperty("siteId", LOOP + "#u1");
        clock.addProperty("cell", CLOCK + ".return");
        clock.addProperty("declaredCallee", CLOCK);
        clock.addProperty("declaredKind", "CALL_RETURN");
        clock.addProperty("dependencyCell", LOOP + "::$l1");
        clock.addProperty("javaType", "long");
        clock.addProperty("inputKind", "CLOCK");
        clock.addProperty("clockNanos", 1000000L);
        clock.addProperty("clockSource", "nanoTime");
        // Each turn reads EPOCH itself, store1 and store2 store it, ran1 and
        // ran2 read it; a call of no occurrence stores it between turn2 and
        // turn3.
        RecordedAccesses.Builder accesses = new RecordedAccesses.Builder();
        for (long call = 2; call <= 11; call++) {
            accesses.add(EPOCH, (long) activations[(int) call - 1][3], call,
                    call == 8 || call == 9);
        }
        accesses.add(EPOCH, 30L, 99L, true);
        RuntimeSelectedRegionFinalizer.Result closure =
                RuntimeSelectedRegionFinalizer.finalizeRegions(walkGraph(),
                        walkSkeletons(), "test", Arrays.asList(CHECK, BUMP,
                                LOOP), instances, branches, walkScopeMap(clock),
                        RuntimeWorkflowDiscovery.FIRST,
                        Collections.<ScheduleEvent>emptyList(),
                        accesses.build(),
                        new RecordedHeap.Builder().build());
        List<String> planned = new ArrayList<>();
        for (Map<String, Object> region : closure.regions) {
            for (Object occurrence
                    : (List<?>) region.get("runtimeOccurrenceIds")) {
                for (Map.Entry<String, String> named : addresses.entrySet()) {
                    if (named.getValue().equals(occurrence)) {
                        planned.add(named.getKey());
                    }
                }
            }
        }
        Collections.sort(planned);
        assertEquals(Arrays.asList("other", "ran1", "rooted", "store1",
                "store2", "target", "turn1", "turn3"), planned);
        Map<String, Object> first = row("members", 2,
                "first", addresses.get("turn1"),
                "last", addresses.get("turn2"));
        assertEquals(first, instances.get(1).get(
                RuntimeSelectedRegionFinalizer.DECIDER_CLASS));
        assertEquals(row("members", 2, "first", addresses.get("turn3"),
                "last", addresses.get("turn4")), instances.get(3).get(
                RuntimeSelectedRegionFinalizer.DECIDER_CLASS));
        assertEquals(row("members", 2, "first", addresses.get("ran1"),
                "last", addresses.get("ran2")), instances.get(9).get(
                RuntimeSelectedRegionFinalizer.DECIDER_CLASS));
        assertFalse(instances.get(5).containsKey(
                RuntimeSelectedRegionFinalizer.DECIDER_CLASS));
        assertFalse(instances.get(7).containsKey(
                RuntimeSelectedRegionFinalizer.DECIDER_CLASS));
    }

    private static final String CHECK = "<ex.Server: void check()>";
    private static final String BUMP = "<ex.State: void bump(ex.Proto)>";
    private static final String SEND = "<ex.Client: ex.Proto send()>";
    private static final String EPOCH = "<ex.State: int epoch>";
    private static final String ALT = "<ex.Server: void alt()>";
    private static final String SIDE = "<ex.Side: void set(int)>";
    private static final String OTHER = "<ex.Side: int other>";
    private static final String GROW = "<ex.Grower: void grow()>";
    private static final String LOOP = "<ex.Loop: void turn()>";
    private static final String CLOCK = "<ex.Time: long now()>";
    private static final String GET = "<ex.Proto: int getEpoch()>";
    private static final String SET =
            "<ex.Proto$Builder: ex.Proto$Builder setEpoch(int)>";
    private static final String PORT = "XCH.ex.wire.epoch";

    /** The target reads EPOCH into its fatal guard, and so would its
     *  region's alt, OTHER; bump stores what it attached into EPOCH; send
     *  exports it; side stores OTHER. */
    private static List<Map<String, Object>> walkGraph() {
        return Arrays.asList(
                row("kind", "exception_guard", "transferKind", "GUARD",
                        "fromCell", CHECK + "::$i0",
                        "toCell", CHECK + "#u5#exception:ex.Fail",
                        "method", CHECK, "siteId", CHECK + "#u5",
                        "unitIndex", 5),
                row("kind", "field_read", "fromCell", EPOCH,
                        "toCell", CHECK + "::$i0", "method", CHECK,
                        "siteId", CHECK + "#u3", "unitIndex", 3),
                row("kind", "field_read", "fromCell", OTHER,
                        "toCell", CHECK + "::$i0", "method", ALT,
                        "siteId", ALT + "#u1", "unitIndex", 1),
                row("kind", "field_write", "fromCell", SIDE + "::$i0",
                        "toCell", OTHER, "method", SIDE,
                        "siteId", SIDE + "#u2", "unitIndex", 2),
                row("kind", "call_return", "fromCell", GET + ".return",
                        "toCell", BUMP + "::$i1", "method", BUMP,
                        "siteId", BUMP + "#u1", "unitIndex", 1),
                row("kind", "field_write", "fromCell", BUMP + "::$i1",
                        "toCell", EPOCH, "method", BUMP,
                        "siteId", BUMP + "#u2", "unitIndex", 2),
                row("kind", "guard_dependency", "transferKind", "GUARD",
                        "fromCell", LOOP + "::$i3", "toCell", LOOP + "#u3",
                        "method", LOOP, "siteId", LOOP + "#u3",
                        "unitIndex", 3),
                row("kind", "field_read", "fromCell", EPOCH,
                        "toCell", LOOP + "::$i3", "method", LOOP,
                        "siteId", LOOP + "#u2", "unitIndex", 2),
                row("kind", "guard_dependency", "transferKind", "GUARD",
                        "fromCell", LOOP + "::$i5", "toCell", LOOP + "#u5",
                        "method", LOOP, "siteId", LOOP + "#u5",
                        "unitIndex", 5),
                row("kind", "wire_capture_argument",
                        "fromCell", SEND + "::$i2",
                        "toCell", SET + ".param0:int", "method", SEND,
                        "siteId", SEND + "#u4", "unitIndex", 4));
    }

    private static List<StaticProgram.RegionRow> walkSkeletons() {
        Map<String, Object> attach = row("portId", PORT,
                RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, "IN",
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND,
                CommunicationCatalogContract.CAPTURE_CALL_RETURN,
                CommunicationCatalogContract.CALL_SITE_ID, BUMP + "#u1",
                CommunicationCatalogContract.PORT_DEFINITION_METHOD, BUMP,
                CommunicationCatalogContract.DECLARED_CALLEE, GET,
                "javaType", "int");
        Map<String, Object> export = row("portId", PORT,
                RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, "OUT",
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND,
                CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT,
                CommunicationCatalogContract.CALL_SITE_ID, SEND + "#u4",
                CommunicationCatalogContract.PORT_DEFINITION_METHOD, SEND,
                CommunicationCatalogContract.DECLARED_CALLEE, SET,
                CommunicationCatalogContract.PORT_ARGUMENT_INDEX, 0,
                "javaType", "int");
        List<Map<String, Object>> none = Collections.emptyList();
        return StaticProgram.regionRows(Arrays.asList(
                walkSkeleton("REGION.check", CHECK, "EXCEPTION_CONTEXT",
                        none, ALT),
                walkSkeleton("REGION.bump", BUMP, "STATE_CONTEXT",
                        Collections.singletonList(attach)),
                walkSkeleton("REGION.send", SEND, "COMMUNICATION_CONTEXT",
                        Collections.singletonList(export)),
                walkSkeleton("REGION.side", SIDE, "STATE_CONTEXT", none),
                walkSkeleton("REGION.grow", GROW, "STATE_CONTEXT", none),
                walkSkeleton("REGION.loop", LOOP, "STATE_CONTEXT", none)),
                RuntimeSelectedRegionFinalizer.SKELETON_KIND, "test");
    }

    private static Map<String, Object> walkSkeleton(
            String regionId, String method, String selection,
            List<Map<String, Object>> ports, String... more) {
        List<String> methods = new ArrayList<>(Arrays.asList(more));
        methods.add(0, method);
        return row("schemaVersion",
                RuntimeSelectedRegionFinalizer.REGION_SCHEMA_VERSION,
                "kind", RuntimeSelectedRegionFinalizer.SKELETON_KIND,
                "regionId", regionId, "rootMethod", method,
                "rootAuthority", "STATE_WRITER_ENTRY",
                "anchorMethod", method,
                "anchorMethods", Collections.singletonList(method),
                "selection", selection,
                "methods", methods,
                RuntimeSelectedRegionFinalizer.COMMUNICATION_PORTS, ports);
    }

    /** The guard that decides the throw, and bump's store of EPOCH; and
     *  {@code more} rows. */
    private StaticScopeMap walkScopeMap(JsonObject... more)
            throws IOException {
        JsonObject target = new JsonObject();
        target.addProperty("kind", "STATIC_SCOPE_SITE");
        target.addProperty("role", "TARGET_SITE");
        target.addProperty("regionId", "REGION.check");
        target.addProperty("siteId", CHECK + "#u7");
        JsonArray guards = new JsonArray();
        guards.add(CHECK + "#u5");
        target.add("guards", guards);
        JsonArray outcomes = new JsonArray();
        outcomes.add(true);
        target.add("guardOutcomes", outcomes);
        JsonObject write = new JsonObject();
        write.addProperty("kind", "STATIC_SCOPE_SITE");
        write.addProperty("role", "WRITE_SITE");
        write.addProperty("regionId", "REGION.bump");
        write.addProperty("siteId", BUMP + "#u2");
        write.addProperty("cell", EPOCH);
        write.addProperty("carrier", EPOCH);
        JsonObject side = write.deepCopy();
        side.addProperty("regionId", "REGION.side");
        side.addProperty("siteId", SIDE + "#u2");
        side.addProperty("cell", OTHER);
        side.addProperty("carrier", OTHER);
        JsonObject grow = write.deepCopy();
        grow.addProperty("regionId", "REGION.grow");
        grow.addProperty("siteId", GROW + "#u4");
        grow.addProperty("declaredCallee",
                "<java.util.Map: java.lang.Object put(java.lang.Object,"
                        + "java.lang.Object)>");
        JsonArray storeGuards = new JsonArray();
        storeGuards.add(LOOP + "#u3");
        storeGuards.add(LOOP + "#u5");
        write.add("guards", storeGuards);
        JsonArray towardStore = new JsonArray();
        towardStore.add(true);
        towardStore.add(true);
        write.add("guardOutcomes", towardStore);
        // The loop's guard reads EPOCH, which the replay versions.
        JsonObject tracked = new JsonObject();
        tracked.addProperty("kind", "STATIC_SCOPE_SITE");
        tracked.addProperty("role", "READ_SITE");
        tracked.addProperty("regionId", "REGION.loop");
        tracked.addProperty("siteId", LOOP + "#u2");
        tracked.addProperty("cell", EPOCH);
        tracked.addProperty("carrier", EPOCH);
        Path file = tree.newFolder().toPath().resolve(StaticScopeMap.FILE);
        StringBuilder rows = new StringBuilder(target + "\n" + write + "\n"
                + side + "\n" + grow + "\n" + tracked + "\n");
        for (JsonObject row : more) rows.append(row).append('\n');
        Files.write(file, rows.toString().getBytes(StandardCharsets.UTF_8));
        return StaticScopeMap.read(file);
    }

    /**
     * What the slice PUBLISHES about the cells it names (SYMBOL-SCOPE §3):
     * every write site of such a cell, under the innermost region that would
     * run it, with the guard set post-dominance gives that site -- and the
     * guard set is where a may-reach guard and a control-dependence guard
     * differ, which is the difference between finding 17960's marker flip and
     * not finding it.
     *
     * <p>That is the whole of what the static side contributes to the demand
     * walk.  {@code writerRegionsByCell} is the join the region finalizer
     * crosses on: one location, the REGIONS whose text stores into it, under
     * both names a read can reach it by -- the leaf the VM versions and the
     * declared field that owns it.  It names no activation and no writer: a
     * region the recording never entered contributes no occurrence, and WHICH
     * of the entered ones wrote the value the VM's own expression decides.</p>
     */
    @Test
    public void theMapScopesTheDemandWalkAndNamesNoWriter()
            throws IOException {
        theSliceNamesEveryWriteSiteOfACellItNames();
        theGuardSetIsPostDominanceAndNotMayReach();
    }

    /**
     * 17960's shape: one counter, two writers, and the writer the seed never
     * ran is in the map exactly like the one it did.
     */
    private void theSliceNamesEveryWriteSiteOfACellItNames()
            throws IOException {
        String leaf = "<java.util.concurrent.atomic.AtomicInteger: int value>";
        String increment = "<example.Manager: java.lang.String create()>";
        String decrement = "<example.Manager: void delete(int,long)>";
        String saver = "<example.Saver: void save(java.io.OutputStream)>";
        String carrier =
                "<example.Manager: java.util.concurrent.atomic.AtomicInteger"
                        + " count>";
        List<Map<String, Object>> edges = Arrays.asList(
                row("kind", "field_mutation", "method", increment,
                        "unitIndex", 27, "toCell", carrier,
                        "invoke", "<java.util.concurrent.atomic."
                                + "AtomicInteger: int getAndIncrement()>"),
                row("kind", "field_mutation", "method", decrement,
                        "unitIndex", 35, "toCell", carrier,
                        "invoke", "<java.util.concurrent.atomic."
                                + "AtomicInteger: int getAndDecrement()>"),
                row("kind", "exception_throw", "method", saver,
                        "unitIndex", 64, "toCell", saver
                                + "#u64#exception:java.lang.IllegalState"),
                // A local-held container mutation names no shared location,
                // so it is no candidate writer of one.
                row("kind", "container_mutation_argument", "method", decrement,
                        "unitIndex", 12, "toCell", decrement + "::$r5"));
        Map<String, Object> port = row(
                CommunicationCatalogContract.PORT_ID, "XCH.a.resp.count",
                RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, "OUT",
                CommunicationCatalogContract.PORT_DEFINITION_METHOD, saver,
                CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX, 9);
        // The same port's attach defines nothing: no export site.
        Map<String, Object> attach = row(
                CommunicationCatalogContract.PORT_ID, "XCH.a.resp.count",
                RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, "IN",
                CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                decrement,
                CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX, 3);
        List<Map<String, Object>> regions = Arrays.asList(
                // The enclosing request region holds every method below it.
                row("regionId", "REGION.request", "methods", Arrays.asList(
                        "<example.Rpc: void handle()>", increment, decrement)),
                row("regionId", "REGION.delete", "methods",
                        Collections.singletonList(decrement),
                        "communicationPorts",
                        Collections.singletonList(attach)),
                row("regionId", "REGION.create", "methods",
                        Collections.singletonList(increment)),
                row("regionId", "REGION.save", "methods",
                        Collections.singletonList(saver),
                        "communicationPorts",
                        Collections.singletonList(port)));

        List<StaticScopeMap.Site> sites = StaticScopeMap.sites(edges, regions,
                Collections.<String, edu.uva.liftlab.graphchecker.contract.Clock>emptyMap(), (m, u, c) -> null, (demandSite, demandCell) -> null, method -> false,
                cell -> SharedFieldFlow.TrackedKind.VALUE, cell -> false,
                cell -> false);
        Path file = tree.newFolder("scope-map").toPath()
                .resolve(StaticScopeMap.FILE);
        StringBuilder text = new StringBuilder();
        for (JsonObject written : StaticScopeMap.rows(sites,
                siteId -> siteId.endsWith("#u35")
                        ? Arrays.asList(
                        new StaticScopeMap.Guard(decrement + "#u7", true),
                        new StaticScopeMap.Guard(decrement + "#u15", false))
                        : Collections.<StaticScopeMap.Guard>emptyList(),
                method -> false)) {
            text.append(written.toString()).append('\n');
        }
        Files.write(file, text.toString().getBytes(StandardCharsets.UTF_8));
        StaticScopeMap map = StaticScopeMap.read(file);

        // The counter's carrier is found from the site the recording DID
        // write at, spelled the way the VM spells an endpoint site.
        Set<String> carriers = map.carriersAt(
                "example.Manager#create()Ljava/lang/String;#621:WRITE", "I",
                LocationKind.INSTANCE);
        assertEquals(Collections.singleton(carrier), carriers);
        // A write row of another type at that method is not that cell.
        assertTrue(map.carriersAt(
                "example.Manager#create()Ljava/lang/String;#621:WRITE", "Z",
                LocationKind.INSTANCE)
                .isEmpty());
        List<String> writers = new ArrayList<>();
        for (StaticScopeMap.Site site : map.writersOf(carrier)) {
            writers.add(site.regionId + " " + site.siteId);
        }
        assertEquals("the writer the seed never ran is in the map, under the "
                        + "innermost region that would run it: " + writers,
                Arrays.asList("REGION.create " + increment + "#u27",
                        "REGION.delete " + decrement + "#u35"), writers);
        List<String> guards = new ArrayList<>();
        List<Boolean> arms = new ArrayList<>();
        for (StaticScopeMap.Site site : map.writersOf(carrier)) {
            assertEquals("<java.util.concurrent.atomic.AtomicInteger: int"
                    + " value>", site.cell);
            if (site.siteId.equals(decrement + "#u35")) {
                guards.addAll(site.guards);
                arms.addAll(site.guardOutcomes);
            }
        }
        assertEquals("the write site carries its post-dominance guard set",
                Arrays.asList(decrement + "#u7", decrement + "#u15"), guards);
        assertEquals("and the arm of each guard that reaches it",
                Arrays.asList(Boolean.TRUE, Boolean.FALSE), arms);
        // The port's producer side only, and the declared target.
        assertEquals("the attach in REGION.delete is no export", 1,
                map.exportsOf("XCH.a.resp.count").size());
        assertEquals("REGION.save",
                map.exportsOf("XCH.a.resp.count").get(0).regionId);
        assertEquals(1, map.targetSites().size());
        assertEquals(saver + "#u64", map.targetSites().get(0).siteId);
        assertEquals("example.Saver#save(Ljava/io/OutputStream;)V",
                map.targetSites().get(0).vmSite);

        // The join the demand walk crosses on: both names of the location
        // answer with the same two sites, each naming the region AND the
        // method an activation has to have entered to have written there.
        Map<String, List<StaticScopeMap.Site>> writeSites =
                map.writeSitesByCell();
        assertEquals("the leaf the VM keeps versions of",
                Arrays.asList("REGION.create " + increment + "#u27",
                        "REGION.delete " + decrement + "#u35"),
                scoped(writeSites.get(leaf)));
        assertEquals("and the declared field that owns it",
                scoped(writeSites.get(leaf)),
                scoped(writeSites.get(carrier)));
        assertEquals("the storing method is what the recording is joined on",
                Arrays.asList(increment, decrement),
                methodsOf(writeSites.get(leaf)));
        assertFalse("a local-held container mutation names no shared "
                        + "location, so it scopes no writer",
                writeSites.containsKey(decrement + "::$r5"));
        assertFalse("the declared target is not a write site",
                writeSites.containsKey(saver
                        + "#u64#exception:java.lang.IllegalState"));
    }

    /**
     * The guard set of a write is post-dominance, not may-reach: the branch
     * BOTH of whose arms can reach the write still decides it, because on one
     * arm the write is unavoidable and on the other it is not.  That branch is
     * 17960's ordered-deletion marker.
     */
    private void theGuardSetIsPostDominanceAndNotMayReach() {
        G.reset();
        SootClass owner = new SootClass("example.Guarded");
        owner.setApplicationClass();
        Scene.v().addClass(owner);
        SootMethod method = new SootMethod("delete",
                Collections.<soot.Type>emptyList(), VoidType.v(),
                Modifier.PUBLIC);
        owner.addMethod(method);
        JimpleBody body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local marker = Jimple.v().newLocal("i0", IntType.v());
        Local earliest = Jimple.v().newLocal("i1", IntType.v());
        Local count = Jimple.v().newLocal("i2", IntType.v());
        body.getLocals().addAll(Arrays.asList(marker, earliest, count));
        Unit u0 = Jimple.v().newAssignStmt(marker, IntConstant.v(0));
        Unit u1 = Jimple.v().newAssignStmt(earliest, IntConstant.v(0));
        Unit u2 = Jimple.v().newAssignStmt(count, IntConstant.v(0));
        Unit write = Jimple.v().newAssignStmt(count, IntConstant.v(1));
        Unit assertFirst = Jimple.v().newNopStmt();
        IfStmt ordered = Jimple.v().newIfStmt(Jimple.v().newEqExpr(marker,
                IntConstant.v(0)), write);
        IfStmt first = Jimple.v().newIfStmt(Jimple.v().newEqExpr(earliest,
                IntConstant.v(0)), assertFirst);
        Unit deferred = Jimple.v().newReturnVoidStmt();
        Unit done = Jimple.v().newReturnVoidStmt();
        for (Unit unit : Arrays.asList(u0, u1, u2, ordered, first, deferred,
                assertFirst, write, done)) {
            body.getUnits().add(unit);
        }
        String decrement = SiteId.of(method.getSignature(), 7);
        List<String> expected = Arrays.asList(
                SiteId.of(method.getSignature(), 3),
                SiteId.of(method.getSignature(), 4));
        assertEquals(expected, guardSites(SiteControlDependence.over(
                Collections.singletonList(decrement)).of(decrement)));
        // Each kept branch also NAMES the arm that makes the write
        // unavoidable: that is the site's fatal polarity, and it is stated
        // once, here, instead of derived by a second rule downstream.
        assertEquals(Arrays.asList(Boolean.TRUE, Boolean.TRUE),
                guardArms(SiteControlDependence.over(
                        Collections.singletonList(decrement)).of(decrement)));
        // Both arms of the marker branch CAN reach the write, which is why
        // the graph's may-reach guard rule drops it.
        assertEquals(2, new soot.toolkits.graph.BriefUnitGraph(body)
                .getSuccsOf(ordered).size());

        // And after INSTRUMENT has woven a hook into the same body, the guard
        // ids are STILL the ids the branches were planned and woven under: a
        // published site id is in the ORIGINAL numbering, and reading the
        // guards off positions in a woven body shifted every one of them past
        // the first hook ("0 of the 27 installed guard ids is decided
        // anywhere in the session").
        CausynthPipeline.tagOriginalUnits(new ArrayList<Unit>(
                body.getUnits()));
        Unit hook = Jimple.v().newAssignStmt(count, IntConstant.v(7));
        body.getUnits().insertBefore(hook, ordered);
        assertEquals("the hook shifted the positions", 8,
                new ArrayList<Unit>(body.getUnits()).indexOf(write));
        assertEquals(expected, guardSites(SiteControlDependence.over(
                Collections.singletonList(decrement)).of(decrement)));
    }

    /**
     * SYMBOL-SCOPE F2: a field is tracked by what it holds.  An integral
     * instance field, boxed or not, is a VALUE; a field a store re-points
     * holding any other object, an array or a static one included, is a
     * REFERENCE; a final map, set, list, queue or deque is a CONTAINER (its
     * contents change in place); any other final one, a String, a float and
     * a static value are none.  A wrapper-typed field is a value cell as its primitive is
     * (solr-18413's {@code RoutingRule.expireAt}, a Long): its {@code
     * getfield} is the READ_SITE a branch decides on through the unboxing,
     * observed like its {@code putfield}; the box's own {@code value} is no
     * tracked cell; and a write row stating the value's type ({@code J}),
     * or a null ({@code L}), names the field as its carrier.  A static
     * reference cell is observed too, as {@code static} (on its class's
     * mirror).
     */
    @Test
    public void aWrapperFieldIsAValueCell() throws IOException {
        G.reset();
        SootClass rule = new SootClass("example.Rule");
        rule.setApplicationClass();
        Scene.v().addClass(rule);
        SootClass box = new SootClass("java.lang.Long");
        box.addField(new SootField("value", LongType.v(), Modifier.FINAL));
        Scene.v().addClass(box);
        SharedFieldFlow.TrackedKind held = SharedFieldFlow.TrackedKind.VALUE;
        SharedFieldFlow.TrackedKind reference =
                SharedFieldFlow.TrackedKind.REFERENCE;
        SharedFieldFlow.TrackedKind none = SharedFieldFlow.TrackedKind.NONE;
        Object[][] fields = {
                {LongType.v(), 0, held},
                {RefType.v("java.lang.Long"), 0, held},
                {RefType.v("java.lang.Boolean"), 0, held},
                {RefType.v("java.lang.Long"), Modifier.STATIC, none},
                {RefType.v("java.lang.Double"), 0, none},
                {DoubleType.v(), 0, none},
                {RefType.v("java.lang.String"), 0, none},
                {RefType.v("java.util.Map"), Modifier.VOLATILE, reference},
                {RefType.v("java.util.Map"), Modifier.FINAL,
                        SharedFieldFlow.TrackedKind.CONTAINER},
                {RefType.v("java.util.Map"), Modifier.STATIC, reference},
                {ArrayType.v(LongType.v(), 1), 0, reference},
                {ArrayType.v(LongType.v(), 1), Modifier.FINAL, none},
                {RefType.v("example.Rule"), Modifier.FINAL, none}};
        for (int index = 0; index < fields.length; index++) {
            SootField field = new SootField("f" + index,
                    (soot.Type) fields[index][0], (Integer) fields[index][1]);
            rule.addField(field);
            assertEquals(field.getSignature(), fields[index][2],
                    CausynthStaticFacts.trackedKind(field.getSignature()));
            assertEquals(field.getSignature(),
                    ((Integer) fields[index][1] & Modifier.STATIC) != 0,
                    CausynthStaticFacts.staticField(field.getSignature()));
        }
        assertTrue("Boolean's unboxing passes its receiver's value on",
                JavaPrimitiveBoxing.unboxing(
                        "<java.lang.Boolean: boolean booleanValue()>"));

        String init = "<example.Rule: void <init>(java.util.Map)>";
        String expired = "<example.Rule: boolean isExpired()>";
        String expireAt = "<example.Rule: java.lang.Long f1>";
        String value = "<java.lang.Long: long value>";
        String unbox = "<java.lang.Long: long longValue()>";
        String registry = "<example.Rule: java.util.Map f9>";
        String getter = "<example.Rule: java.lang.Long getExpireAt()>";
        List<Map<String, Object>> edges = Arrays.asList(
                row("kind", "field_write", "method", init, "unitIndex", 34,
                        "fromCell", init + "::$r16", "toCell", expireAt),
                row("kind", "field_write", "method", init, "unitIndex", 40,
                        "fromCell", init + "::$r20", "toCell", registry),
                row("kind", "field_read", "method", expired, "unitIndex", 8,
                        "fromCell", registry, "toCell", expired + "::$r3",
                        "declaredFieldSignature", registry),
                row("kind", "guard_dependency", "method", expired,
                        "unitIndex", 9, "fromCell", expired + "::$r3",
                        "toCell", expired + "#u9"),
                row("kind", "field_read", "method", expired, "unitIndex", 1,
                        "fromCell", expireAt, "toCell", expired + "::$r1",
                        "declaredFieldSignature", expireAt),
                row("kind", "local_def_use", "method", expired,
                        "unitIndex", 2, "fromCell", expired + "::$r1",
                        "toCell", expired + "::$l0", "invoke", unbox),
                row("kind", "accessor_field_return", "method", expired,
                        "unitIndex", 2, "fromCell", value,
                        "toCell", expired + "::$l0", "invoke", unbox,
                        "declaredFieldSignature", value,
                        "accessorImplementationMethod", unbox),
                row("kind", "guard_dependency", "method", expired,
                        "unitIndex", 6, "fromCell", expired + "::$l0",
                        "toCell", expired + "#u6"),
                row("kind", "accessor_field_return", "method", expired,
                        "unitIndex", 12, "fromCell", expireAt,
                        "toCell", expired + "::$r5", "invoke", getter,
                        "declaredFieldSignature", expireAt,
                        "accessorImplementationMethod", getter),
                row("kind", "guard_dependency", "method", expired,
                        "unitIndex", 13, "fromCell", expired + "::$r5",
                        "toCell", expired + "#u13"));
        List<Map<String, Object>> regions = Arrays.asList(
                row("regionId", "REGION.update", "methods",
                        Collections.singletonList(expired)),
                row("regionId", "REGION.overseer", "methods",
                        Collections.singletonList(init)));
        StringBuilder text = new StringBuilder();
        for (JsonObject written : StaticScopeMap.rows(StaticScopeMap.sites(
                edges, regions, Collections.<String, edu.uva.liftlab.graphchecker.contract.Clock>emptyMap(), (m, u, c) -> null, (demandSite, demandCell) -> null,
                method -> !method.startsWith("<example."),
                CausynthStaticFacts::trackedKind,
                CausynthStaticFacts::staticField,
                CausynthStaticFacts::constructionOnly), null,
                method -> false)) {
            text.append(written.toString()).append('\n');
        }
        Path file = tree.newFolder("wrapper").toPath()
                .resolve(StaticScopeMap.FILE);
        Files.write(file, text.toString().getBytes(StandardCharsets.UTF_8));
        StaticScopeMap map = StaticScopeMap.read(file);

        Map<String, String> observed = new LinkedHashMap<>();
        for (int index = 0; index < map.observedSites().size(); index++) {
            JsonObject site = map.observedSites().get(index)
                    .getAsJsonObject();
            String callee = site.get("declaredCallee").getAsString();
            observed.put(site.get("siteId").getAsString(),
                    site.get("cell").getAsString()
                            + (site.has("static") ? " static" : "")
                            + (callee.isEmpty() ? "" : " via " + callee));
        }
        Map<String, String> expected = new LinkedHashMap<>();
        expected.put(init + "#u34", expireAt);
        expected.put(expired + "#u1", expireAt);
        expected.put(init + "#u40", registry + " static");
        expected.put(expired + "#u8", registry + " static");
        expected.put(expired + "#u12", expireAt + " via " + getter);
        assertEquals("the wrapper's putfield and getfield, not the box's"
                + " value, the static map's store and read, and a read"
                + " through an application getter at its call", expected,
                observed);
        assertEquals(Collections.singleton("REGION.update"),
                map.trackedRegions());
        String store = "example.Rule#<init>(Ljava/util/Map;)V#376:WRITE";
        for (String javaType : new String[]{"J", "L"}) {
            assertEquals(javaType, Collections.singleton(expireAt),
                    map.carriersAt(store, javaType, LocationKind.INSTANCE));
        }
        assertTrue(map.carriersAt(store, "I", LocationKind.INSTANCE)
                .isEmpty());
        assertEquals("a class's location joins the static map, never an"
                        + " object's field", Collections.singleton(registry),
                map.carriersAt(store, "L", LocationKind.STATIC));
        assertEquals("a read's INITIAL names it too",
                Collections.singleton(expireAt),
                map.carriersAt("example.Rule#isExpired()Z#30:READ", "J",
                        LocationKind.INSTANCE));
        assertEquals("a read through the getter is recorded in its body",
                Collections.singleton(expireAt), map.carriersAt(
                        "example.Rule#getExpireAt()Ljava/lang/Long;#1:READ",
                        "L", LocationKind.INSTANCE));
    }

    private static List<String> scoped(List<StaticScopeMap.Site> sites) {
        List<String> scopes = new ArrayList<>();
        for (StaticScopeMap.Site site : sites) {
            scopes.add(site.regionId + " " + site.siteId);
        }
        return scopes;
    }

    private static List<String> methodsOf(List<StaticScopeMap.Site> sites) {
        List<String> methods = new ArrayList<>();
        for (StaticScopeMap.Site site : sites) {
            methods.add(SiteId.methodOf(site.siteId));
        }
        return methods;
    }

    private static List<String> guardSites(
            List<StaticScopeMap.Guard> guards) {
        List<String> sites = new ArrayList<>();
        for (StaticScopeMap.Guard guard : guards) sites.add(guard.siteId());
        return sites;
    }

    private static List<Boolean> guardArms(
            List<StaticScopeMap.Guard> guards) {
        List<Boolean> arms = new ArrayList<>();
        for (StaticScopeMap.Guard guard : guards) arms.add(guard.outcome());
        return arms;
    }



    private static Map<String, Object> row(Object... fields) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (int index = 0; index < fields.length; index += 2) {
            result.put((String) fields[index], fields[index + 1]);
        }
        return result;
    }
}

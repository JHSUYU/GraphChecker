package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.WorkStartSites;
import edu.uva.liftlab.graphchecker.runtime.MessageDoors;
import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * The instrumentation ABI: every hook {@code HookCatalog.concolic()} and
 * {@code HookCatalog.trace()} weave into application bytecode must exist as
 * a public static method of {@code ConcolicRegionRuntime} or {@code
 * CausynthTraceRecorder} with exactly the woven signature.
 *
 * <p>Both catalogs, because the identity is computed in both passes: the
 * recording states an occurrence address at the entry hook of a region root
 * and files a start frame at the work-start hook, so a trace hook whose
 * signature drifts costs the recording its addresses -- at campaign SEED,
 * with a NoSuchMethodError from woven bytecode.</p>
 *
 * <p>Soot resolves those references lazily against a phantom class, so a
 * rename or a moved method fails only in a full campaign run. This test
 * reads the catalog out of the pipeline source and resolves every entry
 * reflectively instead.</p>
 *
 * <p>The launcher is the third half of the same boundary: {@code
 * JUnitMethodRunner} drives every workload's lifecycle by reflection against
 * annotations it names as strings, so an annotation it stops recognizing, or
 * a lifecycle it stops invoking, is a workload that quietly never ran -- and,
 * like the woven hooks, that shows up only at campaign SEED. The fixtures
 * below stand in for the workload classes, in both vocabularies the corpus's
 * checkouts use.</p>
 *
 * <p>The other half of the ABI is not woven at all: the workload checkouts
 * and Solr call GraphChecker from their own source, compiled against an
 * older jar, so a {@code git grep} of this repository returns empty for
 * every one of them and the reference resolves only at campaign SEED.
 * {@code external-callers.txt} is that list.</p>
 */
public class ConcolicHookAbiTest {
    private static final String PIPELINE_SOURCE =
            "src/main/java/edu/uva/liftlab/graphchecker/causynth/"
                    + "CausynthPipeline.java";
    private static final String RUNTIME_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime";
    private static final String RECORDER_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder";
    /** The class every {@code execute.sh} launches, by name. */
    private static final String RUNNER_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.JUnitMethodRunner";
    /** The reflective JUnit lifecycle that runner drives. */
    private static final String LIFECYCLE_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.JUnitLifecycle";
    private static final String PACKAGE = "edu.uva.liftlab.graphchecker.";
    /** APIs called from outside this repository; see the class javadoc. */
    private static final String EXTERNAL_CALLERS =
            "src/test/resources/external-callers.txt";

    @Test
    public void everyWovenHookAndCalledApiResolves() throws Throwable {
        assertEquals("the custom VM keeps three java.lang.System hooks",
                3, resolveCatalog("concolic", RUNTIME_CLASS));
        // The recording's own hooks, against the recorder: startWork files
        // the start frame and enterMethod states the occurrence address of
        // a region root, and both are woven into application bytecode.
        assertEquals("no java.lang.System hook is woven by the trace pass",
                0, resolveCatalog("trace", RECORDER_CLASS));
        assertEveryTimedWaitHasItsStandIn();
        assertExternalCallersResolve();
        assertTheRunnerDrivesTheJupiterLifecycle();
    }

    /**
     * The calls the weave REPLACES: every timed-wait shape has its stand-in
     * on the class the weave names, with exactly the signature it calls --
     * the receiver first, the call's own parameters, the site last, and the
     * call's return type.  A mismatch is a NoSuchMethodError inside a
     * replay, which is the one place it cannot be seen.
     */
    private static void assertEveryTimedWaitHasItsStandIn() throws Exception {
        Class<?> owner = Class.forName(WorkStartSites.TIMED_WAITS_CLASS);
        for (WorkStartSites.TimedWait shape : WorkStartSites.timedWaits()) {
            List<Class<?>> parameters = new ArrayList<>();
            for (String name : shape.replacementParameters()) {
                parameters.add(declaredType(name));
            }
            Method method = owner.getMethod(shape.replacement,
                    parameters.toArray(new Class<?>[0]));
            assertTrue(shape.replacement + " is static",
                    Modifier.isStatic(method.getModifiers()));
            assertEquals(shape.replacement + " returns what the call did",
                    declaredType(shape.returns), method.getReturnType());
        }
    }

    /** A type as a Java signature spells it: a primitive, else a class. */
    private static Class<?> declaredType(String name)
            throws ClassNotFoundException {
        return name.contains(".") ? Class.forName(name) : javaType(name);
    }

    /**
     * Resolves one catalog's hooks against {@code ownerClass}.
     *
     * @return how many of its entries are woven on {@code java.lang.System}
     */
    private static int resolveCatalog(String factory, String ownerClass)
            throws Exception {
        Class<?> owner = Class.forName(ownerClass);
        List<String[]> entries = catalogEntries(factory);
        assertFalse("no hook entries parsed out of " + PIPELINE_SOURCE,
                entries.isEmpty());
        int wovenOnSystem = 0;
        for (String[] entry : entries) {
            if ("system".equals(entry[0])) {
                wovenOnSystem++;
                continue;
            }
            String name = entry[1];
            Class<?> result = javaType(entry[2]);
            Class<?>[] parameters = new Class<?>[entry.length - 3];
            for (int i = 0; i < parameters.length; i++) {
                parameters[i] = javaType(entry[i + 3]);
            }
            Method hook;
            try {
                hook = owner.getMethod(name, parameters);
            } catch (NoSuchMethodException missing) {
                fail("woven " + factory + " hook " + name + " is no longer a"
                        + " public method of " + ownerClass + ": " + missing);
                return wovenOnSystem;
            }
            assertTrue(name + " must stay static",
                    Modifier.isStatic(hook.getModifiers()));
            assertEquals(name + " return type", result, hook.getReturnType());
        }
        return wovenOnSystem;
    }

    /**
     * The launcher half of the ABI: the runner drives a workload class.
     *
     * <p>Three things a replay depends on and nothing else states: the whole
     * lifecycle runs in order, in either annotation vocabulary the corpus
     * uses (five checkouts are Jupiter, hdfs-17960's is JUnit 4); a failing
     * test surfaces its own throwable after teardown still ran; and a method
     * name no workload declares is refused by name instead of publishing a
     * session for a workload that never ran.</p>
     */
    private static void assertTheRunnerDrivesTheJupiterLifecycle()
            throws Throwable {
        for (Class<?> workload : Arrays.asList(
                JupiterWorkload.class, JUnit4Workload.class)) {
            LIFECYCLE.clear();
            runWorkloadMethod(workload, "theWorkloadBody");
            assertEquals("the runner owes " + workload.getSimpleName()
                            + " the whole lifecycle, in order",
                    Arrays.asList("beforeAll", "beforeEach",
                            "theWorkloadBody", "afterEach", "afterAll"),
                    new ArrayList<>(LIFECYCLE));
        }

        // What a Jupiter class states about its own set-up: a directory in
        // each @TempDir field, an extension's callbacks around the methods
        // of its role, a TestInfo parameter, and the @Test among same-named
        // methods.
        LIFECYCLE.clear();
        runWorkloadMethod(SetUpWorkload.class, "theWorkloadBody");
        assertEquals(Arrays.asList("beforeAll:SetUpWorkload",
                        "beforeEach:theWorkloadBody",
                        "starting:theWorkloadBody", "theWorkloadBody",
                        "afterEach:theWorkloadBody"),
                new ArrayList<>(LIFECYCLE));

        LIFECYCLE.clear();
        try {
            runWorkloadMethod(FailingJupiterWorkload.class,
                    "theWorkloadBody");
            fail("a failing @Test must reach the launcher");
        } catch (AssertionError failed) {
            assertEquals("the workload's own throwable, not a wrapper",
                    "the workload's own assertion", failed.getMessage());
        }
        assertEquals("teardown owes its turn on the failure path",
                Arrays.asList("beforeEach", "theWorkloadBody", "afterEach"),
                new ArrayList<>(LIFECYCLE));

        try {
            runWorkloadMethod(JupiterWorkload.class, "noSuchWorkloadBody");
            fail("a name no workload declares must be refused");
        } catch (NoSuchMethodException refused) {
            assertEquals("no such test method: "
                            + JupiterWorkload.class.getName()
                            + "#noSuchWorkloadBody",
                    refused.getMessage());
        }
    }

    /** Calls the runner's one lifecycle driver, unwrapping reflection. */
    private static void runWorkloadMethod(Class<?> workload, String method)
            throws Throwable {
        // The runner owns main and the session's lifetime; the lifecycle
        // it drives is its own class, and this is that class's one entry.
        assertNotNull(Class.forName(RUNNER_CLASS)
                .getDeclaredMethod("main", String[].class));
        Method run = Class.forName(LIFECYCLE_CLASS)
                .getDeclaredMethod("run", String[].class);
        run.setAccessible(true);
        try {
            run.invoke(null,
                    (Object) new String[] {workload.getName(), method});
        } catch (InvocationTargetException failure) {
            throw failure.getCause();
        }
    }

    /** What each fixture's lifecycle invocation appends, in order. */
    private static final List<String> LIFECYCLE = new ArrayList<>();

    /** A workload class, as five of the six checkouts are. */
    private static class JupiterWorkload {
        @org.junit.jupiter.api.BeforeAll
        static void beforeAll() {
            LIFECYCLE.add("beforeAll");
        }

        @org.junit.jupiter.api.BeforeEach
        void beforeEach() {
            LIFECYCLE.add("beforeEach");
        }

        @org.junit.jupiter.api.Test
        @org.junit.jupiter.api.Timeout(1)
        void theWorkloadBody() {
            // The @Timeout the campaign owns instead: a one-second limit the
            // runner obeyed would kill every replay it exists to record.
            LIFECYCLE.add("theWorkloadBody");
        }

        @org.junit.jupiter.api.AfterEach
        void afterEach() {
            LIFECYCLE.add("afterEach");
        }

        @org.junit.jupiter.api.AfterAll
        static void afterAll() {
            LIFECYCLE.add("afterAll");
        }
    }

    /** A workload class in the other vocabulary, as the sixth is. */
    private static class JUnit4Workload {
        @org.junit.BeforeClass
        public static void beforeAll() {
            LIFECYCLE.add("beforeAll");
        }

        @org.junit.Before
        public void beforeEach() {
            LIFECYCLE.add("beforeEach");
        }

        @org.junit.Test(timeout = 1L)
        public void theWorkloadBody() {
            // The declared timeout the campaign owns instead, here in the
            // form the JUnit 4 checkout writes it.
            LIFECYCLE.add("theWorkloadBody");
        }

        @org.junit.After
        public void afterEach() {
            LIFECYCLE.add("afterEach");
        }

        @org.junit.AfterClass
        public static void afterAll() {
            LIFECYCLE.add("afterAll");
        }
    }

    /** Names what each callback is handed, as Hadoop's TestName does. */
    public static class NamingExtension implements
            org.junit.jupiter.api.extension.BeforeAllCallback,
            org.junit.jupiter.api.extension.BeforeEachCallback,
            org.junit.jupiter.api.extension.AfterEachCallback {
        @Override
        public void beforeAll(
                org.junit.jupiter.api.extension.ExtensionContext context) {
            LIFECYCLE.add("beforeAll:"
                    + context.getRequiredTestClass().getSimpleName());
        }

        @Override
        public void beforeEach(
                org.junit.jupiter.api.extension.ExtensionContext context) {
            LIFECYCLE.add("beforeEach:"
                    + context.getTestMethod().get().getName());
        }

        @Override
        public void afterEach(
                org.junit.jupiter.api.extension.ExtensionContext context) {
            LIFECYCLE.add("afterEach:"
                    + context.getRequiredTestMethod().getName());
        }
    }

    /** A workload stating its own set-up the Jupiter way. */
    private static class SetUpWorkload {
        @org.junit.jupiter.api.extension.RegisterExtension
        static NamingExtension perClass = new NamingExtension();
        @org.junit.jupiter.api.io.TempDir
        static java.io.File shared;
        @org.junit.jupiter.api.io.TempDir
        java.nio.file.Path own;

        /** As ZooKeeper's ZKTestCase#starting names the test it starts. */
        @org.junit.jupiter.api.BeforeEach
        void starting(org.junit.jupiter.api.TestInfo test) {
            LIFECYCLE.add("starting:" + test.getTestMethod().get().getName());
        }

        /** A helper sharing the test's name is not the test. */
        void theWorkloadBody(int ignored) {
            throw new AssertionError("the helper ran");
        }

        @org.junit.jupiter.api.Test
        void theWorkloadBody() {
            assertTrue(shared.isDirectory() && Files.isDirectory(own));
            LIFECYCLE.add("theWorkloadBody");
        }
    }

    /** The same, failing the way a detected bug fails. */
    private static class FailingJupiterWorkload {
        @org.junit.jupiter.api.BeforeEach
        void beforeEach() {
            LIFECYCLE.add("beforeEach");
        }

        @org.junit.jupiter.api.Test
        void theWorkloadBody() {
            LIFECYCLE.add("theWorkloadBody");
            throw new AssertionError("the workload's own assertion");
        }

        @org.junit.jupiter.api.AfterEach
        void afterEach() {
            LIFECYCLE.add("afterEach");
        }
    }

    /** The external half of the ABI: what the workload checkouts call. */
    private static void assertExternalCallersResolve() throws Exception {
        for (String row : Files.readAllLines(Paths.get(EXTERNAL_CALLERS),
                StandardCharsets.UTF_8)) {
            if (row.isEmpty() || row.startsWith("#")) continue;
            String[] called = row.split(" ");
            Class<?>[] parameters = new Class<?>[called.length - 3];
            for (int i = 0; i < parameters.length; i++) {
                parameters[i] = javaType(called[i + 3]);
            }
            Method api;
            try {
                api = Class.forName(PACKAGE + called[0])
                        .getMethod(called[1], parameters);
            } catch (ReflectiveOperationException gone) {
                fail("the workload checkouts call " + row + "; deleting it "
                        + "kills every campaign at SEED: " + gone);
                return;
            }
            assertTrue(row + " must stay static",
                    Modifier.isStatic(api.getModifiers()));
            assertEquals(row + " return type", javaType(called[2]),
                    api.getReturnType());
        }
    }

    /**
     * One {@code String[]} per {@code .add(...)} of the named catalog
     * factory: owner variable, method name, result type, parameter types.
     */
    private static List<String[]> catalogEntries(String factory)
            throws Exception {
        String source = new String(Files.readAllBytes(Paths.get(
                PIPELINE_SOURCE)), StandardCharsets.UTF_8);
        int start = source.indexOf("HookCatalog " + factory + "() {");
        assertTrue("no " + factory + "() catalog in " + PIPELINE_SOURCE,
                start >= 0);
        int end = source.indexOf("\n        }", start);
        String body = source.substring(start, end);
        List<String[]> entries = new ArrayList<>();
        int at = body.indexOf(".add(");
        while (at >= 0) {
            int open = at + ".add(".length();
            int close = matchingParen(body, open);
            List<String> arguments = splitTopLevel(
                    body.substring(open, close));
            List<String> entry = new ArrayList<>();
            entry.add(arguments.get(1));
            entry.add(unquote(arguments.get(2)));
            entry.addAll(arguments.subList(3, arguments.size()));
            entries.add(entry.toArray(new String[0]));
            at = body.indexOf(".add(", close);
        }
        return entries;
    }

    private static int matchingParen(String text, int from) {
        int depth = 1;
        boolean inString = false;
        for (int i = from; i < text.length(); i++) {
            char ch = text.charAt(i);
            if (inString) {
                if (ch == '\\') i++;
                else if (ch == '"') inString = false;
            } else if (ch == '"') inString = true;
            else if (ch == '(') depth++;
            else if (ch == ')' && --depth == 0) return i;
        }
        throw new IllegalStateException("unbalanced .add( at " + from);
    }

    private static List<String> splitTopLevel(String arguments) {
        List<String> parts = new ArrayList<>();
        int depth = 0;
        boolean inString = false;
        StringBuilder part = new StringBuilder();
        for (int i = 0; i < arguments.length(); i++) {
            char ch = arguments.charAt(i);
            if (inString) {
                part.append(ch);
                if (ch == '\\') part.append(arguments.charAt(++i));
                else if (ch == '"') inString = false;
                continue;
            }
            if (ch == '"') inString = true;
            if (ch == '(') depth++;
            if (ch == ')') depth--;
            if (ch == ',' && depth == 0) {
                parts.add(normalize(part.toString()));
                part.setLength(0);
                continue;
            }
            part.append(ch);
        }
        parts.add(normalize(part.toString()));
        return parts;
    }

    private static String normalize(String text) {
        return text.replaceAll("\\s+", " ").trim();
    }

    private static String unquote(String literal) {
        assertTrue("hook name must be a literal: " + literal,
                literal.startsWith("\"") && literal.endsWith("\""));
        return literal.substring(1, literal.length() - 1);
    }

    private static Class<?> javaType(String name) {
        switch (name) {
            case "VoidType.v()": case "void": return void.class;
            case "BooleanType.v()": case "boolean": return boolean.class;
            case "IntType.v()": case "int": return int.class;
            case "LongType.v()": case "long": return long.class;
            case "string": return String.class;
            case "object": return Object.class;
            case "ArrayType.v(object, 1)": case "object[]": return Object[].class;
            case "byte[]": return byte[].class;
            case "doors.Outbound": return MessageDoors.Outbound.class;
            case "doors.Inbound": return MessageDoors.Inbound.class;
            case "RefType.v(\"java.lang.Throwable\")": return Throwable.class;
            default: throw new IllegalStateException(
                    "unmapped type: " + name);
        }
    }
}

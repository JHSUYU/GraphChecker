package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.WorkStartSites;
import edu.uva.liftlab.graphchecker.runtime.MessageDoors;
import org.apache.hadoop.ipc.CausynthMessagePropagation;
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

public class ConcolicHookAbiTest {
    private static final String PIPELINE_SOURCE =
            "src/main/java/edu/uva/liftlab/graphchecker/causynth/"
                    + "CausynthPipeline.java";
    private static final String RUNTIME_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime";
    private static final String RECORDER_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder";
    private static final String RUNNER_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.JUnitMethodRunner";
    private static final String LIFECYCLE_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.JUnitLifecycle";
    private static final String PACKAGE = "edu.uva.liftlab.graphchecker.";
    private static final String SHIM = "org.apache.hadoop.ipc.";
    private static final String EXTERNAL_CALLERS =
            "src/test/resources/external-callers.txt";

    @Test
    public void everyWovenHookAndCalledApiResolves() throws Throwable {
        assertEquals("the custom VM keeps three java.lang.System hooks",
                3, resolveCatalog("concolic", RUNTIME_CLASS));
        assertEquals("no java.lang.System hook is woven by the trace pass",
                0, resolveCatalog("trace", RECORDER_CLASS));
        assertEveryTimedWaitHasItsStandIn();
        assertExternalCallersResolve();
        assertTheRunnerDrivesTheJupiterLifecycle();
    }

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

    private static Class<?> declaredType(String name)
            throws ClassNotFoundException {
        return name.contains(".") ? Class.forName(name) : javaType(name);
    }

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

    private static void runWorkloadMethod(Class<?> workload, String method)
            throws Throwable {
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

    private static final List<String> LIFECYCLE = new ArrayList<>();

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

    private static class SetUpWorkload {
        @org.junit.jupiter.api.extension.RegisterExtension
        static NamingExtension perClass = new NamingExtension();
        @org.junit.jupiter.api.io.TempDir
        static java.io.File shared;
        @org.junit.jupiter.api.io.TempDir
        java.nio.file.Path own;

        @org.junit.jupiter.api.BeforeEach
        void starting(org.junit.jupiter.api.TestInfo test) {
            LIFECYCLE.add("starting:" + test.getTestMethod().get().getName());
        }

        void theWorkloadBody(int ignored) {
            throw new AssertionError("the helper ran");
        }

        @org.junit.jupiter.api.Test
        void theWorkloadBody() {
            assertTrue(shared.isDirectory() && Files.isDirectory(own));
            LIFECYCLE.add("theWorkloadBody");
        }
    }

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
                api = Class.forName(called[0].startsWith(SHIM)
                        ? called[0] : PACKAGE + called[0])
                        .getMethod(called[1], parameters);
            } catch (ReflectiveOperationException gone) {
                fail("the system trees call " + row + "; deleting it "
                        + "kills every campaign at SEED: " + gone);
                return;
            }
            assertTrue(row + " must stay static",
                    Modifier.isStatic(api.getModifiers()));
            assertEquals(row + " return type", javaType(called[2]),
                    api.getReturnType());
        }
    }

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
            case "string[]": return String[].class;
            case "predicate": return java.util.function.Predicate.class;
            case "doors.Outbound": return MessageDoors.Outbound.class;
            case "doors.Inbound": return MessageDoors.Inbound.class;
            case "shim.Outbound":
                return CausynthMessagePropagation.Outbound.class;
            case "shim.Inbound":
                return CausynthMessagePropagation.Inbound.class;
            case "runnable": return Runnable.class;
            case "list": return java.util.List.class;
            case "RefType.v(\"java.lang.Throwable\")": return Throwable.class;
            default: throw new IllegalStateException(
                    "unmapped type: " + name);
        }
    }
}

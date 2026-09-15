package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Test;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
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
 * <p>The other half of the ABI is not woven at all: the workload checkouts
 * and Solr call GraphChecker from their own source, compiled against an
 * older jar, so a {@code git grep} of this repository returns empty for
 * every one of them and the reference resolves only at campaign SEED.
 * {@code external-callers.txt} is that list; MECHANISMS §10 is why.</p>
 */
public class ConcolicHookAbiTest {
    private static final String PIPELINE_SOURCE =
            "src/main/java/edu/uva/liftlab/graphchecker/causynth/"
                    + "CausynthPipeline.java";
    private static final String RUNTIME_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime";
    private static final String RECORDER_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder";
    private static final String PACKAGE = "edu.uva.liftlab.graphchecker.";
    /** APIs called from outside this repository; see the class javadoc. */
    private static final String EXTERNAL_CALLERS =
            "src/test/resources/external-callers.txt";

    @Test
    public void everyWovenHookAndCalledApiResolves() throws Exception {
        assertEquals("the custom VM keeps three java.lang.System hooks",
                3, resolveCatalog("concolic", RUNTIME_CLASS));
        // The recording's own hooks, against the recorder: startWork files
        // the start frame and enterMethod states the occurrence address of
        // a region root, and both are woven into application bytecode.
        assertEquals("no java.lang.System hook is woven by the trace pass",
                0, resolveCatalog("trace", RECORDER_CLASS));
        assertExternalCallersResolve();
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
            case "ArrayType.v(object, 1)": return Object[].class;
            case "RefType.v(\"java.lang.Throwable\")": return Throwable.class;
            default: throw new IllegalStateException(
                    "unmapped type: " + name);
        }
    }
}

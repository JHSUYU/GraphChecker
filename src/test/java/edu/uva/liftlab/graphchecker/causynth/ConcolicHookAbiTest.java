package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Test;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * The instrumentation ABI: every hook {@code HookCatalog.concolic()} weaves
 * into application bytecode must exist as a public static method of
 * {@code ConcolicRegionRuntime} with exactly the woven signature, and the
 * handoff carrier must keep its binary name and its leaf fields.
 *
 * <p>Soot resolves those references lazily against a phantom class, so a
 * rename or a moved method fails only in a full campaign run. This test
 * reads the catalog out of the pipeline source and resolves every entry
 * reflectively instead.</p>
 */
public class ConcolicHookAbiTest {
    private static final String PIPELINE_SOURCE =
            "src/main/java/edu/uva/liftlab/graphchecker/causynth/"
                    + "CausynthPipeline.java";
    private static final String RUNTIME_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime";
    private static final Map<String, Class<?>> SOOT_TYPES = sootTypes();
    private static final Map<String, Class<?>> PINNED_TYPES = pinnedTypes();

    /**
     * Driver entry points: runtime methods no hook weaves, called by a
     * launcher, by a workload checkout or by the trace recorder.  Nothing in
     * this repository's own call graph fails when one is renamed, moved to
     * another class or narrowed, so each row pins visibility, return type,
     * name and parameter types.
     */
    private static final String[][] DRIVER_ENTRY_POINTS = {
            {"public", "String", "openWorkloadSession"},
            {"public", "String", "closeWorkloadSession"},
            {"public", "void", "awaitSelectedResultPublications"},
            {"public", "boolean", "symbolizeConfiguredSourceField",
                    "String", "Object", "String"},
            {"package", "void", "observeCausalSource", "String"},
            {"public", "boolean", "materializeSymbolicBoolean", "String"},
    };

    /** Binary name of every handoff carrier leaf and the type it carries. */
    private static final String[][] CARRIER_LEAVES = {
            {"z", "boolean"}, {"b", "byte"}, {"s", "short"},
            {"c", "char"}, {"i", "int"}, {"j", "long"},
            {"f", "float"}, {"d", "double"}, {"o", "Object"},
    };

    private static Map<String, Class<?>> pinnedTypes() {
        Map<String, Class<?>> types = new HashMap<>();
        types.put("void", void.class);
        types.put("boolean", boolean.class);
        types.put("byte", byte.class);
        types.put("short", short.class);
        types.put("char", char.class);
        types.put("int", int.class);
        types.put("long", long.class);
        types.put("float", float.class);
        types.put("double", double.class);
        types.put("String", String.class);
        types.put("Object", Object.class);
        return types;
    }

    private static Map<String, Class<?>> sootTypes() {
        Map<String, Class<?>> types = new HashMap<>();
        types.put("VoidType.v()", void.class);
        types.put("BooleanType.v()", boolean.class);
        types.put("IntType.v()", int.class);
        types.put("LongType.v()", long.class);
        types.put("string", String.class);
        types.put("object", Object.class);
        types.put("ArrayType.v(object, 1)", Object[].class);
        types.put("RefType.v(\"java.lang.Throwable\")", Throwable.class);
        return types;
    }

    @Test
    public void everyWovenConcolicHookResolvesOnTheRuntime() throws Exception {
        Class<?> runtime = Class.forName(RUNTIME_CLASS);
        List<String[]> entries = catalogEntries("concolic");
        assertFalse("no hook entries parsed out of " + PIPELINE_SOURCE,
                entries.isEmpty());
        int wovenOnRuntime = 0;
        int wovenOnSystem = 0;
        for (String[] entry : entries) {
            if ("system".equals(entry[0])) {
                wovenOnSystem++;
                continue;
            }
            assertEquals("unexpected hook owner", "runtime", entry[0]);
            wovenOnRuntime++;
            String name = entry[1];
            Class<?> result = javaType(entry[2]);
            Class<?>[] parameters = new Class<?>[entry.length - 3];
            for (int i = 0; i < parameters.length; i++) {
                parameters[i] = javaType(entry[i + 3]);
            }
            Method hook;
            try {
                hook = runtime.getMethod(name, parameters);
            } catch (NoSuchMethodException missing) {
                fail("woven concolic hook " + name + " is no longer a public "
                        + "method of " + RUNTIME_CLASS + ": " + missing);
                return;
            }
            assertTrue(name + " must stay static",
                    Modifier.isStatic(hook.getModifiers()));
            assertEquals(name + " return type", result, hook.getReturnType());
        }
        assertEquals("every concolic hook that is not a java.lang.System "
                + "entry point is woven against the runtime",
                entries.size() - wovenOnSystem, wovenOnRuntime);
        assertEquals("the custom VM keeps three java.lang.System hooks",
                3, wovenOnSystem);
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

    private static Class<?> pinnedType(String name) {
        Class<?> type = PINNED_TYPES.get(name);
        if (type == null) {
            throw new IllegalStateException("unmapped pinned type: " + name);
        }
        return type;
    }

    private static Class<?> javaType(String sootType) {
        Class<?> type = SOOT_TYPES.get(sootType);
        if (type == null) {
            throw new IllegalStateException(
                    "unmapped Soot type in the hook catalog: " + sootType);
        }
        return type;
    }
}

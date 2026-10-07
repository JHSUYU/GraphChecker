package edu.uva.liftlab.graphchecker.runtime;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Predicate;

/**
 * The engine's own plumbing, which is never program state (RULES, lead
 * 2026-10-06): the engine's runtime classes, and generated protobuf messages
 * and their builders -- immutable once built, crossing a process only whole
 * through a door ({@link MessageCodec}).  No row states an access at such a
 * site, and a read such code made takes the value of the version it
 * observed when its expression is imported
 * ({@code contract.VmExpressionTable.Store}).
 */
final class EnginePlumbing {
    private EnginePlumbing() {
    }

    private static final String ENGINE = "edu.uva.liftlab.graphchecker.";

    /** The classes generated messages and builders extend, wherever a
     *  build relocates protobuf to (Hadoop's {@code
     *  org.apache.hadoop.thirdparty.protobuf}). */
    private static final String[] GENERATED = {
            ".protobuf.GeneratedMessage", ".protobuf.GeneratedMessageV3",
            ".protobuf.GeneratedMessage$Builder",
            ".protobuf.GeneratedMessageV3$Builder"};

    /** By class name, once per JVM. */
    private static final Map<String, Boolean> SITES =
            new ConcurrentHashMap<String, Boolean>();

    /** {@link #site}, of a class as the VM spells it ({@code a/b/C$D}). */
    static final Predicate<String> VM_CLASSES =
            name -> site(Text.safe(name).replace('/', '.'));

    /** Whether code of {@code className} (source form, {@code a.b.C$D}) is
     *  plumbing. */
    static boolean site(String className) {
        String name = Text.safe(className);
        if (name.startsWith(ENGINE)) return true;
        Boolean known = SITES.get(name);
        if (known == null) {
            known = generated(loaded(name), true);
            SITES.put(name, known);
        }
        return known;
    }

    /** Whether {@code type} is a generated protobuf message (its builders
     *  are not). */
    static boolean generatedMessage(Class<?> type) {
        return generated(type, false);
    }

    private static boolean generated(Class<?> type, boolean builders) {
        for (Class<?> above = type == null ? null : type.getSuperclass();
             above != null; above = above.getSuperclass()) {
            String name = above.getName();
            for (int index = 0; index < (builders ? 4 : 2); index++) {
                if (name.endsWith(GENERATED[index])) return true;
            }
        }
        return false;
    }

    /** The class the program loaded under {@code name}, uninitialized, or
     *  null. */
    private static Class<?> loaded(String name) {
        ClassLoader loader = Thread.currentThread().getContextClassLoader();
        try {
            return Class.forName(name, false, loader != null ? loader
                    : ClassLoader.getSystemClassLoader());
        } catch (ClassNotFoundException | LinkageError absent) {
            return null;
        }
    }
}

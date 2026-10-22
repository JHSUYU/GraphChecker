package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.causynth.LibraryCatalog;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Predicate;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

final class EnginePlumbing {
    private EnginePlumbing() {
    }

    private static final String ENGINE = "edu.uva.liftlab.graphchecker.";

    private static final String[] GENERATED = {
            ".protobuf.GeneratedMessage", ".protobuf.GeneratedMessageV3",
            ".protobuf.GeneratedMessage$Builder",
            ".protobuf.GeneratedMessageV3$Builder"};

    private static final Map<String, Boolean> SITES =
            new ConcurrentHashMap<String, Boolean>();

    static final Predicate<String> VM_CLASSES =
            name -> site(trimmed(name).replace('/', '.'));

    static boolean site(String className) {
        String name = trimmed(className);
        if (name.startsWith(ENGINE)) return true;
        Boolean known = SITES.get(name);
        if (known == null) {
            known = generated(loaded(name), true);
            SITES.put(name, known);
        }
        return known;
    }

    static boolean wireMessage(Class<?> type) {
        return generated(type, false) || type != null
                && LibraryCatalog.messageClasses().contains(type.getName());
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

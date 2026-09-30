package edu.uva.liftlab.graphchecker.contract;

import java.util.Locale;

/**
 * CONTRACT-SPEC §1: the scope kind a lineage hop ran under, as the workload
 * declares it (no deployment vocabulary in engine code).  Only the engine's
 * own kinds are constants.  Never a thread id or name: those are timing
 * facts (IDENTITY §1).
 */
public final class Role extends Value {
    /** A hop this run could not attribute; the address says so. */
    public static final Role UNKNOWN = new Role("UNKNOWN");
    /** The workload's own action: the root a request descends from. */
    public static final Role CLIENT = new Role("CLIENT");
    /** Work a JDK executor ran, as the submission's own hop. */
    public static final Role EXECUTOR_TASK = new Role("EXECUTOR_TASK");

    private final String name;

    private Role(String name) {
        this.name = name;
    }

    /**
     * The role one declared name spells, upper-cased over {@code [A-Z0-9_]}.
     * Total, since it runs inside instrumentation; empty is {@link #UNKNOWN}.
     */
    public static Role of(String declared) {
        String name = normalized(declared);
        if (name.isEmpty() || name.equals(UNKNOWN.name)) return UNKNOWN;
        if (name.equals(CLIENT.name)) return CLIENT;
        if (name.equals(EXECUTOR_TASK.name)) return EXECUTOR_TASK;
        return new Role(name);
    }

    /** The canonical spelling: part of every rendered causal context. */
    public String name() {
        return name;
    }

    private static String normalized(String declared) {
        String value = declared == null ? ""
                : declared.trim().toUpperCase(Locale.ROOT);
        StringBuilder spelled = new StringBuilder(value.length());
        for (int index = 0; index < value.length(); index++) {
            char at = value.charAt(index);
            spelled.append(at >= 'A' && at <= 'Z' || at >= '0' && at <= '9'
                    || at == '_' ? at : '_');
        }
        return spelled.toString();
    }

    @Override
    Object[] parts() {
        return new Object[] {name};
    }

    @Override
    public String toString() {
        return name;
    }
}

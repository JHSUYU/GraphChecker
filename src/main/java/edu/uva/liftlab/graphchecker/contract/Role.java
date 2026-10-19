package edu.uva.liftlab.graphchecker.contract;

import java.util.Locale;

public final class Role extends Value {
    public static final Role UNKNOWN = new Role("UNKNOWN");
    public static final Role CLIENT = new Role("CLIENT");
    public static final Role EXECUTOR_TASK = new Role("EXECUTOR_TASK");
    public static final Role WAKE = new Role("WAKE");

    private final String name;

    private Role(String name) {
        this.name = name;
    }

    public static Role of(String declared) {
        String name = normalized(declared);
        if (name.isEmpty() || name.equals(UNKNOWN.name)) return UNKNOWN;
        if (name.equals(CLIENT.name)) return CLIENT;
        if (name.equals(EXECUTOR_TASK.name)) return EXECUTOR_TASK;
        if (name.equals(WAKE.name)) return WAKE;
        return new Role(name);
    }

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

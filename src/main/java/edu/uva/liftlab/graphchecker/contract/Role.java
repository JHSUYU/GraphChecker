package edu.uva.liftlab.graphchecker.contract;

import java.util.Locale;
import java.util.Objects;

/**
 * CONTRACT-SPEC 1: the scope KIND a lineage hop ran under, as the workload
 * declares it.
 *
 * <p>One string, carried. It used to be a closed enum whose constants were
 * Hadoop concepts -- {@code IPC_HANDLER}, {@code DATA_XCEIVER}, {@code
 * BP_SERVICE_ACTOR}, {@code SPS}, {@code BALANCER}, {@code HEARTBEAT_TICK},
 * {@code KEY_MANAGER_TICK} -- which put a deployment's vocabulary in engine
 * code and forced every new kind through a mapping table. The workload
 * already says which kind a scope is: the transport it names at an exchange,
 * the role it names when it enters a carried scope, the role it names at a
 * daemon tick. That declaration IS the role.</p>
 *
 * <p>Three kinds are the engine's own and are named here because nothing
 * declares them: {@link #CLIENT}, the workload's own action at the root of a
 * request; {@link #EXECUTOR_TASK}, work a JDK executor ran; and {@link
 * #UNKNOWN}, what a hop degrades to when this run could attribute it to
 * nothing, published as {@link CausalContext.Lost} rather than guessed.</p>
 *
 * <p>Roles are never thread ids or thread names: those are timing facts no
 * replay can be held to (IDENTITY-V3 §1).</p>
 */
public final class Role {
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
     * The role one declared name spells.
     *
     * <p>Total by construction, because this runs inside instrumentation: a
     * refusal here would throw out of the engine into the workload. A name
     * nothing declared is {@link #UNKNOWN}, and a declared name is spelled
     * upper-case over {@code [A-Z0-9_]} so that it is one token of a
     * rendered address ({@code Root:<role>#k}) whichever way the workload
     * wrote it. The same normalisation runs in the recording and in every
     * replay, which is what makes the address they compute the same one.</p>
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
    public boolean equals(Object value) {
        return this == value || value instanceof Role
                && name.equals(((Role) value).name);
    }

    @Override
    public int hashCode() {
        return Objects.hash(name);
    }

    @Override
    public String toString() {
        return name;
    }
}

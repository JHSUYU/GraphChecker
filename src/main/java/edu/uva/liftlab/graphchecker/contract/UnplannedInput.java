package edu.uva.liftlab.graphchecker.contract;

/**
 * One invocation of a planned fault marker that its occurrence's task plans
 * no input for (PIPELINE §7.8, GROW): the plan's {@code taskId}, the planned
 * input's {@code symbol} and the invocation {@code k} of the marker's call in
 * that occurrence.  A replay states it as the subject of an {@link
 * GapKind#UNPLANNED_INPUT} row, {@code <taskId> <symbol>#<k>}; GROW plans it
 * as the input {@link #grown()} of the same task, so the k-th call is a root
 * of its own.  Neither a task id nor an input symbol holds a space or a
 * {@code #}.
 */
public final class UnplannedInput extends Value {
    /** The most invocations of one planned marker in one occurrence GROW
     *  plans inputs for: a declared bound, counted in the case's {@code
     *  bounded} ({@code unplanned-input-max}); a replay names one more at
     *  most, so the bound is seen. */
    public static final int MAX = 4;

    private final String taskId;
    private final String symbol;
    private final int k;

    private UnplannedInput(String taskId, String symbol, int k) {
        this.taskId = taskId;
        this.symbol = symbol;
        this.k = k;
    }

    /** The {@code k}-th invocation of the input {@code symbol} plans (its
     *  own symbol, or the one a grown symbol was grown from). */
    public static UnplannedInput of(String taskId, String symbol, int k) {
        String base = Fields.text(symbol, "symbol");
        int grown = base.indexOf('#');
        if (grown >= 0) base = base.substring(0, grown);
        if (k < 1) throw new IllegalArgumentException("k is >= 1: " + k);
        return new UnplannedInput(Fields.text(taskId, "taskId"), base, k);
    }

    /** Reads a row's subject ({@link #subject()}). */
    public static UnplannedInput parse(String subject) {
        String value = subject == null ? "" : subject.trim();
        int space = value.indexOf(' ');
        int mark = value.lastIndexOf('#');
        if (space <= 0 || mark <= space + 1 || mark + 1 >= value.length()) {
            throw new IllegalArgumentException(
                    "not an unplanned input: " + subject);
        }
        try {
            return of(value.substring(0, space),
                    value.substring(space + 1, mark),
                    Integer.parseInt(value.substring(mark + 1)));
        } catch (NumberFormatException notACount) {
            throw new IllegalArgumentException(
                    "not an unplanned input: " + subject);
        }
    }

    public String taskId() {
        return taskId;
    }

    /** The planned input it is an invocation of. */
    public String symbol() {
        return symbol;
    }

    public int k() {
        return k;
    }

    /** The symbol (and port id) of its grown input: {@code <symbol>#<k>}. */
    public String grown() {
        return symbol + "#" + k;
    }

    /** {@code <taskId> <symbol>#<k>}. */
    public String subject() {
        return taskId + " " + grown();
    }

    @Override
    Object[] parts() {
        return new Object[] {taskId, symbol, k};
    }

    @Override
    public String toString() {
        return subject();
    }
}

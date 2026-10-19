package edu.uva.liftlab.graphchecker.contract;

public final class UnplannedInput extends Value {
    public static final int MAX = 4;

    private final String taskId;
    private final String symbol;
    private final int k;

    private UnplannedInput(String taskId, String symbol, int k) {
        this.taskId = taskId;
        this.symbol = symbol;
        this.k = k;
    }

    public static UnplannedInput of(String taskId, String symbol, int k) {
        String base = Fields.text(symbol, "symbol");
        int grown = base.indexOf('#');
        if (grown >= 0) base = base.substring(0, grown);
        if (k < 1) throw new IllegalArgumentException("k is >= 1: " + k);
        return new UnplannedInput(Fields.text(taskId, "taskId"), base, k);
    }

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

    public String symbol() {
        return symbol;
    }

    public int k() {
        return k;
    }

    public String grown() {
        return symbol + "#" + k;
    }

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

/**
 * A StringBuilder's mutators other than append keep its expression true.
 *
 * <p>The builder's content is its append chain, and its bodies' writes to
 * value/count are not followed; setLength, insert and delete used to leave
 * the chain standing for content they had changed.  They are now
 * summarized as a concat of substrings of the content, or, where no summary
 * is exact (reverse), the expression is dropped and the next use states the
 * builder's concrete content.</p>
 */
public final class RegionStringBuilderMutatorSmoke {
    private static final class Input {
        String name = "abc";
    }

    private static final class Sink {
        String text;
    }

    public static void main(String[] args) {
        require(System.startConcolicRegion("REGION.builder",
                "TASK.builder") == 0L, "region start rejected");
        Input in = new Input();
        System.symbolizeExactField(in, Input.class.getName(), "name",
                "Ljava/lang/String;", "SB.NAME");
        Sink sink = new Sink();

        StringBuilder reset = new StringBuilder();
        reset.append(in.name).append("-x");
        reset.setLength(0);
        reset.append("fresh");
        sink.text = reset.toString();
        require(sink.text.equals("fresh") && !text(sink).contains("SB.NAME"),
                "setLength(0) left the old content: " + text(sink));

        StringBuilder inserted = new StringBuilder();
        inserted.append(in.name);
        inserted.insert(0, "pre");
        sink.text = inserted.toString();
        String insert = text(sink);
        require(sink.text.equals("preabc") && insert.contains("SB.NAME")
                        && insert.contains("substring"),
                "insert is not a concat of the content: " + insert);

        StringBuilder deleted = new StringBuilder();
        deleted.append(in.name).append("zz");
        deleted.delete(0, 1);
        sink.text = deleted.toString();
        String delete = text(sink);
        require(sink.text.equals("bczz") && delete.contains("SB.NAME")
                        && delete.contains("substring"),
                "delete is not a substring of the content: " + delete);

        StringBuilder reversed = new StringBuilder();
        reversed.append(in.name);
        reversed.reverse();
        sink.text = reversed.toString();
        require(sink.text.equals("cba") && !text(sink).contains("SB.NAME"),
                "reverse kept a stale expression: " + text(sink));

        System.endConcolic();
        System.out.println("RegionStringBuilderMutatorSmoke OK");
    }

    private static String text(Sink sink) {
        return System.getSymbolicFieldExpression(sink, Sink.class.getName(),
                "text", "Ljava/lang/String;", sink.text);
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}

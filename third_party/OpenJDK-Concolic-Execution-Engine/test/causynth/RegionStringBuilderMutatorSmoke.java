/**
 * A StringBuilder's mutators other than append keep its expression true, and
 * so does an append of a range.
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

        // append(CharSequence, start, end) appends the range [start, end),
        // not the sequence and two renderings of its bounds.
        StringBuilder ranged = new StringBuilder("k=");
        ranged.append(in.name, 1, 3);
        sink.text = ranged.toString();
        String range = text(sink);
        require(sink.text.equals("k=bc") && range.contains("SB.NAME")
                        && range.contains("substring")
                        && !range.contains("toString"),
                "a ranged append is not a substring of its sequence: "
                        + range);
        // A char[]'s or another CharSequence's range no String operation
        // states: with no expression of its own it is the text it appended,
        // a constant after the builder's earlier content, which stays.
        StringBuilder chars = new StringBuilder();
        chars.append(in.name);
        chars.append(new char[]{'x', 'y'}, 0, 1);
        sink.text = chars.toString();
        String charRange = text(sink);
        require(sink.text.equals("abcx") && charRange.contains("SB.NAME")
                        && charRange.contains("Y_L'String'_x")
                        && !charRange.contains("toString"),
                "a char[] range is not its appended text: " + charRange);
        StringBuilder other = new StringBuilder();
        other.append(in.name);
        other.append(java.nio.CharBuffer.wrap("xyz"), 1, 2);
        sink.text = other.toString();
        String otherRange = text(sink);
        require(sink.text.equals("abcy") && otherRange.contains("SB.NAME")
                        && otherRange.contains("Y_L'String'_y"),
                "a CharSequence range is not its appended text: "
                        + otherRange);

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

/**
 * Verifies that String.contains keeps the symbolic receiver and needle and
 * records both the taken and non-taken Java branch predicates.
 */
public final class RegionStringContainsApiSmoke {
    // Volatile peers prevent javac from folding saved == true / != false into
    // a direct unary test.  The VM must still recognize the symbolic operand
    // as Boolean when the bytecode uses the int-shaped comparison family.
    private static volatile boolean EXPECTED_TRUE = true;
    private static volatile boolean EXPECTED_FALSE = false;

    private static final class Input {
        private String text = new String("alpha-needle-omega");
    }

    private static final class InternedInput {
        private String text = "interned-field-ready";
    }

    public static void main(String[] args) {
        Input input = new Input();
        System.startConcolicRegion("REGION.string-contains",
                "ACT.string-contains");
        System.symbolizeField(input, "text", "string_contains_text");

        // Soot lowers the invoke into an assignment and inserts the marker at
        // the subsequent IfStmt.  Keep the smoke in the same shape: the VM
        // predicate is produced first, then claimed by the exact branch event.
        boolean positive = input.text.contains("needle");
        long positiveEvent = System.markConcolicBranch(
                "STRING.CONTAINS.POSITIVE", 1);
        if (positive) {
            // Record the positive contains predicate.
        } else {
            throw new AssertionError("unexpected concrete contains result");
        }
        boolean negative = input.text.contains("absent");
        long negativeEvent = System.markConcolicBranch(
                "STRING.CONTAINS.NEGATIVE", 1);
        if (negative) {
            throw new AssertionError("unexpected concrete contains result");
        }

        // The predicate must remain an unpolarized Boolean shadow after an
        // istore/iload round trip.  In particular, the concrete true result
        // must not have rewritten the saved value into "not contains".
        boolean saved = input.text.contains("needle");
        long savedEqualsEvent = System.markConcolicBranch(
                "STRING.CONTAINS.SAVED.EQ", 1);
        if (saved == EXPECTED_TRUE) {
            // Exact Boolean equality with a concrete true peer.
        } else {
            throw new AssertionError("unexpected saved equality result");
        }
        long savedNotEqualsEvent = System.markConcolicBranch(
                "STRING.CONTAINS.SAVED.NE", 1);
        if (saved != EXPECTED_FALSE) {
            // Exact Boolean inequality with a concrete false peer.
        } else {
            throw new AssertionError("unexpected saved inequality result");
        }

        // Java shares iand/ixor bytecodes between int and boolean.  With two
        // symbolic Boolean operands these must be modeled as logical AND and
        // Boolean inequality, never as integer bit-vector arithmetic.
        boolean left = input.text.contains("needle");
        boolean right = input.text.contains("omega");
        boolean both = left & right;
        long andEvent = System.markConcolicBranch(
                "STRING.CONTAINS.PAIR.AND", 1);
        if (!both) {
            throw new AssertionError("unexpected concrete AND result");
        }
        boolean different = left ^ right;
        long xorEvent = System.markConcolicBranch(
                "STRING.CONTAINS.PAIR.XOR", 1);
        if (different) {
            throw new AssertionError("unexpected concrete XOR result");
        }

        // Computing a symbolic predicate is not itself a path decision.  If
        // the result is ignored, it must neither enter the path condition nor
        // become the condition of an unrelated later concrete branch.
        input.text.contains("ignored");
        long unrelatedEvent = System.markConcolicBranch(
                "STRING.CONTAINS.UNRELATED", 1);
        if (args.length >= 0) {
            // This branch deliberately has no symbolic input.
        }

        require(positiveEvent > 0L && negativeEvent > positiveEvent
                        && savedEqualsEvent > negativeEvent
                        && savedNotEqualsEvent > savedEqualsEvent
                        && andEvent > savedNotEqualsEvent
                        && xorEvent > andEvent
                        && unrelatedEvent > xorEvent,
                "contains branch markers were rejected");

        String events = System.getConcolicBranchEvents();
        require(exactCondition(events, "STRING.CONTAINS.POSITIVE", 1),
                events);
        require(exactCondition(events, "STRING.CONTAINS.NEGATIVE", 1),
                events);
        require(exactCondition(events, "STRING.CONTAINS.SAVED.EQ", 1),
                events);
        require(exactCondition(events, "STRING.CONTAINS.SAVED.NE", 1),
                events);
        require(exactCondition(events, "STRING.CONTAINS.PAIR.AND", 1),
                events);
        require(exactCondition(events, "STRING.CONTAINS.PAIR.XOR", 1),
                events);
        require(noCondition(events, "STRING.CONTAINS.UNRELATED", 1), events);
        require(count(events, "\"conditionCount\":1") == 6, events);
        require(count(events, "\"conditionCount\":0") == 1, events);

        String path = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        String summary = System.finishConcolicRegion();
        require(summary.contains("\"regionId\":\"REGION.string-contains\""),
                summary);
        require(path.contains("string_contains_text"), path);
        // Five immutable contains nodes feed the six recorded predicates: the
        // saved result is compared twice.  The DAG artifact defines that node
        // once instead of expanding it once per downstream use.
        require(count(path, "\"_name\":\"contains\"") == 5, path);
        require(path.contains("\"_is_not\":false"), path);
        require(!path.contains("\"_is_not\":true"), path);
        require(path.contains("\"_op\":\"&&\""), path);
        require(path.contains("\"_java_type\":\"Z\",\"_exp\":\"Y_Z_0\""),
                path);
        require(path.contains("\"_java_type\":\"Z\",\"_exp\":\"Y_Z_1\""),
                path);
        require(path.contains("Y_L'String'_needle"), path);
        require(path.contains("Y_L'String'_absent"), path);
        require(path.contains("Y_L'String'_omega"), path);
        require(!path.contains("Y_L'String'_ignored"), path);
        if (Boolean.getBoolean("causynth.smoke.dump")) {
            System.out.println(summary);
        }
        runInternedFieldSmoke();
        runInternedLocalSmoke();
        runInternReturnIdentitySmoke();
        System.out.println("CAUSYNTH_REGION_STRING_CONTAINS_API_SMOKE_OK");
    }

    private static void runInternedFieldSmoke() {
        InternedInput input = new InternedInput();
        String peerAlias = "interned-field-ready";
        require(input.text == peerAlias,
                "field seed must use the intern-table identity");

        System.startConcolicRegion("REGION.interned-string-field",
                "ACT.interned-string-field");
        System.symbolizeField(input, "text", "interned_field_text");

        // Exercise the real cross-method shape: getfield supplies an
        // alias-specific reference shadow, astore/aload preserves it, and
        // String.contains consumes it in a different Java frame.
        String selectedAlias = input.text;
        boolean selected = selectedAlias.contains("ready");
        long selectedEvent = System.markConcolicBranch(
                "STRING.INTERNED.FIELD.SELECTED", 1);
        if (!selected) {
            throw new AssertionError("unexpected interned field result");
        }

        // The same intern-table oop reached through another alias must remain
        // concrete: symbolizeField binds the owner edge, not the shared oop.
        boolean peer = peerAlias.contains("ready");
        long peerEvent = System.markConcolicBranch(
                "STRING.INTERNED.FIELD.PEER", 1);
        if (!peer) {
            throw new AssertionError("unexpected peer literal result");
        }

        require(selectedEvent > 0L && peerEvent > selectedEvent,
                "interned field markers were rejected");
        String events = System.getConcolicBranchEvents();
        require(exactCondition(events,
                "STRING.INTERNED.FIELD.SELECTED", 1), events);
        require(noCondition(events, "STRING.INTERNED.FIELD.PEER", 1),
                events);

        String path = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        String summary = System.finishConcolicRegion();
        require(path.contains("interned_field_text"), path);
        require(count(path, "\"_name\":\"contains\"") == 1, path);
        require(path.contains("Y_L'String'_ready"), path);
        require(!path.contains("\"_is_not\":true"), path);
        require(input.text == peerAlias,
                "symbolizeField changed interned String identity");
    }

    private static void runInternedLocalSmoke() {
        String local = "interned-local-ready";
        String peerAlias = "interned-local-ready";
        require(local == peerAlias,
                "local seed must use the intern-table identity");

        System.startConcolicRegion("REGION.interned-string-local",
                "ACT.interned-string-local");
        System.symbolize(local, "interned_local_text");

        String expression = System.getSymbolicExpression(local);
        require(expression.contains("\"symbolic\":true"), expression);
        require(expression.contains("interned_local_text"), expression);

        boolean contains = local.contains("ready");
        long event = System.markConcolicBranch(
                "STRING.INTERNED.LOCAL", 1);
        if (!contains) {
            throw new AssertionError("unexpected interned local result");
        }
        require(event > 0L, "interned local marker was rejected");
        String events = System.getConcolicBranchEvents();
        require(exactCondition(events, "STRING.INTERNED.LOCAL", 1),
                events);

        String path = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        String summary = System.finishConcolicRegion();
        require(path.contains("interned_local_text"), path);
        require(count(path, "\"_name\":\"contains\"") == 1, path);
        require(path.contains("Y_L'String'_ready"), path);
        require(!path.contains("\"_is_not\":true"), path);
        require(local == peerAlias,
                "symbolize changed interned String identity");
    }

    private static void runInternReturnIdentitySmoke() {
        String canonicalLiteral = "canonical-intern-return-ready";
        String source = new String(canonicalLiteral);
        require(source != canonicalLiteral,
                "source must begin with a distinct heap identity");

        System.startConcolicRegion("REGION.string-intern-return",
                "ACT.string-intern-return");
        System.symbolize(source, "string_intern_source_text");

        // String.intern() must retain the JVM's canonical reference identity.
        // Symbolic content is propagated only along this returned operand edge.
        String canonical = source.intern();
        require(canonical == canonicalLiteral,
                "intern must return the JVM canonical identity");

        boolean returnedContains = canonical.contains("ready");
        long returnedEvent = System.markConcolicBranch(
                "STRING.INTERN.RETURNED", 1);
        if (!returnedContains) {
            throw new AssertionError("unexpected intern return result");
        }

        // A separate alias to the same canonical oop remains concrete.  The
        // return-edge shadow must not be installed globally on the interned oop.
        boolean literalContains = canonicalLiteral.contains("ready");
        long literalEvent = System.markConcolicBranch(
                "STRING.INTERN.LITERAL", 1);
        if (!literalContains) {
            throw new AssertionError("unexpected literal result");
        }

        require(returnedEvent > 0L && literalEvent > returnedEvent,
                "intern return markers were rejected");
        String events = System.getConcolicBranchEvents();
        require(exactCondition(events, "STRING.INTERN.RETURNED", 1),
                events);
        require(noCondition(events, "STRING.INTERN.LITERAL", 1), events);

        String path = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        String summary = System.finishConcolicRegion();
        require(path.contains("string_intern_source_text"), path);
        require(count(path, "\"_name\":\"contains\"") == 1, path);
        require(path.contains("Y_L'String'_ready"), path);
        require(!path.contains("\"_name\":\"intern\""), path);
        require(canonical == canonicalLiteral,
                "concolic propagation changed intern identity");
    }

    private static boolean exactCondition(String events, String site,
                                          int occurrence) {
        String identity = "\"siteId\":\"" + site
                + "\",\"occurrence\":" + occurrence;
        int identityOffset = events.indexOf(identity);
        if (identityOffset < 0) return false;
        int start = events.lastIndexOf('{', identityOffset);
        int end = events.indexOf('}', identityOffset);
        if (start < 0 || end < start) return false;
        String event = events.substring(start, end + 1);
        return !event.contains("\"conditionIndices\":[]")
                && event.contains("\"conditionCount\":1");
    }

    private static boolean noCondition(String events, String site,
                                       int occurrence) {
        String identity = "\"siteId\":\"" + site
                + "\",\"occurrence\":" + occurrence;
        int identityOffset = events.indexOf(identity);
        if (identityOffset < 0) return false;
        int start = events.lastIndexOf('{', identityOffset);
        int end = events.indexOf('}', identityOffset);
        if (start < 0 || end < start) return false;
        String event = events.substring(start, end + 1);
        return event.contains("\"conditionIndices\":[]")
                && event.contains("\"conditionCount\":0");
    }

    private static int count(String value, String needle) {
        int result = 0;
        int offset = 0;
        while ((offset = value.indexOf(needle, offset)) >= 0) {
            result++;
            offset += needle.length();
        }
        return result;
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}

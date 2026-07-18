public final class RegionBranchEventApiSmoke {
    private static final class Input {
        int value = 1;
        int otherValue = 1;
        long wide = 2L;
        boolean flag = true;
    }

    private static void check(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }

    private static int occurrences(String text, String needle) {
        int count = 0;
        int cursor = 0;
        while ((cursor = text.indexOf(needle, cursor)) >= 0) {
            count++;
            cursor += needle.length();
        }
        return count;
    }

    public static void main(String[] args) throws Exception {
        Input input = new Input();
        long status = System.startConcolicRegion(
                "REGION.BRANCH.SMOKE", "ACT.BRANCH.SMOKE");
        check(status == 0L, "region start rejected");

        String concreteInt = System.getSymbolicExpression(
                Integer.valueOf(10));
        String concreteBoolean = System.getSymbolicExpression(Boolean.FALSE);
        String concreteLong = System.getSymbolicExpression(
                Long.valueOf(1234567890123L));
        String concreteChar = System.getSymbolicExpression(
                Character.valueOf('A'));
        String concreteFloat = System.getSymbolicExpression(
                Float.valueOf(1.25F));
        String concreteDouble = System.getSymbolicExpression(
                Double.valueOf(1.25D));
        check(concreteInt.contains("\"kind\":\"CONCRETE_PRIMITIVE\"")
                        && concreteInt.contains(
                        "\"javaTypeDescriptor\":\"I\"")
                        && concreteInt.contains("\"expressionAuthority\":"
                        + "\"VM_EXACT_CONCRETE_BOXED_PRIMITIVE_V1\"")
                        && concreteInt.contains("\"_type\":\"ConstExpr\"")
                        && concreteInt.contains("\"_java_type\":\"I\"")
                        && concreteInt.contains("Y_I_10"),
                "concrete Integer was not serialized as a typed constant: "
                        + concreteInt);
        check(concreteBoolean.contains(
                        "\"kind\":\"CONCRETE_PRIMITIVE\"")
                        && concreteBoolean.contains(
                        "\"javaTypeDescriptor\":\"Z\"")
                        && concreteBoolean.contains("\"expressionAuthority\":"
                        + "\"VM_EXACT_CONCRETE_BOXED_PRIMITIVE_V1\"")
                        && concreteBoolean.contains(
                        "\"_type\":\"ConstExpr\"")
                        && concreteBoolean.contains(
                        "\"_java_type\":\"Z\"")
                        && concreteBoolean.contains("Y_Z_0"),
                "concrete Boolean was not serialized as a typed constant: "
                        + concreteBoolean);
        check(concreteLong.contains("\"kind\":\"CONCRETE_PRIMITIVE\"")
                        && concreteLong.contains(
                        "\"javaTypeDescriptor\":\"J\"")
                        && concreteLong.contains("\"expressionAuthority\":"
                        + "\"VM_EXACT_CONCRETE_BOXED_PRIMITIVE_V1\"")
                        && concreteLong.contains("\"_type\":\"ConstExpr\"")
                        && concreteLong.contains("\"_java_type\":\"J\"")
                        && concreteLong.contains("Y_J_1234567890123"),
                "concrete Long was not serialized as a typed constant: "
                        + concreteLong);
        check(concreteChar.contains("\"javaTypeDescriptor\":\"C\"")
                        && concreteChar.contains("\"expressionAuthority\":"
                        + "\"VM_EXACT_CONCRETE_BOXED_PRIMITIVE_V1\"")
                        && concreteChar.contains("Y_C_65"),
                "concrete Character did not use a numeric constant: "
                        + concreteChar);
        check(concreteFloat.contains("\"javaTypeDescriptor\":\"F\"")
                        && concreteFloat.contains("Y_F_1.250000000e+00"),
                "concrete Float lost round-trip precision: "
                        + concreteFloat);
        check(concreteDouble.contains("\"javaTypeDescriptor\":\"D\"")
                        && concreteDouble.contains(
                        "Y_D_1.25000000000000000e+00"),
                "concrete Double lost round-trip precision: "
                        + concreteDouble);

        System.symbolizeField(input, "value", "branch_value");
        System.symbolizeField(input, "otherValue", "branch_other_value");
        System.symbolizeField(input, "wide", "branch_wide");
        System.symbolizeField(input, "flag", "branch_flag");

        Integer boxedInt = new Integer(input.value);
        Integer boxedOtherInt = new Integer(input.otherValue);
        Boolean boxedBoolean = new Boolean(input.flag);
        String intExpression = System.getSymbolicExpression(boxedInt);
        String otherIntExpression = System.getSymbolicExpression(
                boxedOtherInt);
        String booleanExpression = System.getSymbolicExpression(boxedBoolean);
        check(intExpression.contains("branch_value")
                        && intExpression.contains(
                        "\"javaTypeDescriptor\":\"I\"")
                        && intExpression.contains("\"expressionAuthority\":"
                        + "\"VM_EXACT_BOXED_PRIMITIVE_SHADOW_V1\""),
                "boxed int lost its primitive shadow: " + intExpression);
        check(otherIntExpression.contains("branch_other_value")
                        && !otherIntExpression.contains("branch_value_"),
                "second fresh int wrapper has the wrong shadow: "
                        + otherIntExpression);
        check(System.getSymbolicExpression(boxedInt).contains(
                        "branch_value"),
                "second same-value wrapper overwrote the first shadow");
        check(booleanExpression.contains("branch_flag")
                        && booleanExpression.contains(
                        "\"javaTypeDescriptor\":\"Z\"")
                        && booleanExpression.contains("\"expressionAuthority\":"
                        + "\"VM_EXACT_BOXED_PRIMITIVE_SHADOW_V1\""),
                "boxed boolean lost its primitive shadow: "
                        + booleanExpression);
        String cachedConcrete = System.getSymbolicExpression(
                Integer.valueOf(1));
        check(cachedConcrete.contains(
                        "\"kind\":\"CONCRETE_PRIMITIVE\"")
                        && cachedConcrete.contains(
                        "\"javaTypeDescriptor\":\"I\"")
                        && cachedConcrete.contains("\"expressionAuthority\":"
                        + "\"VM_EXACT_CONCRETE_BOXED_PRIMITIVE_V1\"")
                        && cachedConcrete.contains("Y_I_1")
                        && !cachedConcrete.contains("branch_value")
                        && !cachedConcrete.contains("branch_other_value"),
                "fresh symbolic boxes polluted IntegerCache: "
                        + cachedConcrete);

        long first = System.markConcolicBranch("SAME_SHAPE.1", 1);
        boolean firstOutcome;
        if (input.value > 0) {
            firstOutcome = true;
        } else {
            firstOutcome = false;
        }
        check(first > 0L && firstOutcome, "first branch marker failed");

        long second = System.markConcolicBranch("SAME_SHAPE.2", 1);
        boolean secondOutcome;
        if (input.value > 0) {
            secondOutcome = true;
        } else {
            secondOutcome = false;
        }
        check(second > first && secondOutcome,
                "second same-shape branch marker failed");

        for (int occurrence = 1; occurrence <= 2; occurrence++) {
            long loopEvent = System.markConcolicBranch(
                    "LOOP.SAME.SITE", occurrence);
            boolean loopOutcome;
            if (input.value >= occurrence) {
                loopOutcome = true;
            } else {
                loopOutcome = false;
            }
            check(loopEvent > second,
                    "loop branch marker failed at " + occurrence);
            check(occurrence == 1 ? loopOutcome : !loopOutcome,
                    "loop branch outcome changed");
        }

        long wideEvent = System.markConcolicBranch("LCMP.BRANCH", 1);
        boolean wideOutcome;
        if (input.wide >= 0L) {
            wideOutcome = true;
        } else {
            wideOutcome = false;
        }
        check(wideEvent > second && wideOutcome,
                "lcmp branch marker failed");

        String beforePause = System.getConcolicBranchEvents();
        System.pauseConcolicPathCondition();
        long pausedEvent = System.markConcolicBranch("PAUSED.BRANCH", 1);
        if (input.value > 0) {
            input.value += 0;
        }
        System.resumeConcolicPathCondition();
        String afterPause = System.getConcolicBranchEvents();
        check(pausedEvent == 0L, "paused marker must be rejected");
        check(beforePause.equals(afterPause),
                "paused bookkeeping changed branch events");

        final String[] foreignEvents = new String[1];
        final long[] foreignMarker = new long[1];
        Thread foreign = new Thread(new Runnable() {
            @Override
            public void run() {
                foreignMarker[0] = System.markConcolicBranch(
                        "FOREIGN.BRANCH", 1);
                foreignEvents[0] = System.getConcolicBranchEvents();
            }
        }, "branch-event-foreign");
        foreign.start();
        foreign.join();
        check(foreignMarker[0] == 0L,
                "foreign thread acquired the owner marker");
        check(foreignEvents[0].contains("\"active\":false")
                        && foreignEvents[0].contains("\"events\":[]"),
                "foreign thread observed owner events: " + foreignEvents[0]);

        String events = System.getConcolicBranchEvents();
        check(events.contains("\"kind\":\"CONCOLIC_THREAD_BRANCH_EVENTS\""),
                "missing branch event envelope: " + events);
        check(events.contains("\"active\":true"),
                "active branch event envelope is not explicit: " + events);
        check(events.contains("\"regionId\":\"REGION.BRANCH.SMOKE\""),
                "missing region ownership: " + events);
        check(events.contains("\"activationId\":\"ACT.BRANCH.SMOKE\""),
                "missing activation ownership: " + events);
        check(events.contains("\"siteId\":\"SAME_SHAPE.1\"")
                        && events.contains("\"siteId\":\"SAME_SHAPE.2\""),
                "same-shape sites were not distinguished: " + events);
        check(events.contains("\"siteId\":\"LOOP.SAME.SITE\","
                        + "\"occurrence\":1")
                        && events.contains("\"siteId\":\"LOOP.SAME.SITE\","
                        + "\"occurrence\":2"),
                "loop occurrences were not distinguished: " + events);
        check(events.contains("\"siteId\":\"LCMP.BRANCH\""),
                "lcmp event is absent: " + events);
        check(!events.contains("PAUSED.BRANCH")
                        && !events.contains("FOREIGN.BRANCH"),
                "non-owner/paused event leaked into owner context: " + events);
        check(occurrences(events,
                "\"authority\":\"VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1\"")
                        == 5,
                "expected five exact branch events: " + events);
        check(occurrences(events, "\"conditionCount\":1") == 5,
                "every symbolic if must own one PC index: " + events);
        check(events.contains("\"conditionIndices\":[0]")
                        && events.contains("\"conditionIndices\":[1]")
                        && events.contains("\"conditionIndices\":[4]"),
                "PC indices are not exact/monotonic: " + events);

        String summary = System.finishConcolicRegion();
        check(summary.contains("\"threadContextId\":")
                        && summary.contains("\"branchEvents\":"),
                "final summary omitted thread branch context: " + summary);
        String afterFinish = System.getConcolicBranchEvents();
        check(afterFinish.contains("\"active\":false")
                        && afterFinish.contains("\"events\":[]"),
                "branch context survived finish: " + afterFinish);
        System.out.println("RegionBranchEventApiSmoke passed");
    }
}

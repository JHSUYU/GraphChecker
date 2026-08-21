public final class RegionFieldApiSmoke {
    private static final class Input {
        private long expiryDate = 100L;
        private int keyId = 42;
        private Entry[] entries = {new Entry(7), null, new Entry(11)};
        private Object unrelated = new Object();
    }

    private static final class Entry {
        private int keyId;

        private Entry(int keyId) {
            this.keyId = keyId;
        }
    }

    public static void main(String[] args) {
        Input input = new Input();
        System.startConcolicRegion("REGION.field", "ACT.field");
        System.symbolizeField(input, "expiryDate", "field_input_expiryDate");
        System.symbolizeField(input, "keyId", "field_input_keyId");
        System.symbolizeField(input, "entries", "field_input_entries");
        if (input.expiryDate > 0L && input.keyId > 0) {
            // Force the selected primitive field into the path condition.
        }
        if (input.entries[0].keyId > 0 && input.entries[2].keyId > 0) {
            // Exercise arbitrary object-array initialization and AALOAD while
            // retaining a concrete loop/index policy outside the VM model.
        }
        String expression = System.getSymbolicExpression(input);
        // Read while the region is still open: the expression API is the
        // authority for what a selected field carries, and the region summary
        // is deliberately sparse - it stopped restating the accumulated
        // expression DAG, so it is asked only for its own identity.
        String entries = System.getSymbolicExpression(input.entries);
        String summary = System.finishConcolicRegion();
        require(expression.contains("\"symbolic\":true"), expression);
        require(entries.contains("ContainerRelation"), entries);
        require(summary.contains("\"regionId\":\"REGION.field\""), summary);
        System.out.println("CAUSYNTH_REGION_FIELD_API_SMOKE_OK");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) {
            throw new AssertionError(detail);
        }
    }
}

/** Isolates the pending-exception shadow invalidation path of arraycopy. */
public final class RegionArrayCopyExceptionApiSmoke {
    public static void main(String[] args) {
        String[] destination = new String[] {"seed"};

        System.startConcolicRegion("REGION.arraycopy-exception",
                "ACT.arraycopy-exception");
        try {
            System.arraycopy(new Object[] {new Object()}, 0,
                    destination, 0, 1);
            throw new AssertionError("expected ArrayStoreException");
        } catch (ArrayStoreException expected) {
            // The VM conservatively invalidates the requested destination
            // interval because an object copy may have committed a prefix.
        }

        System.gc();

        System.pauseConcolicPathCondition();
        String json = System.getSymbolicExpression(destination);
        require(json.contains("\"kind\":\"ARRAY_VALUE\""), json);
        require(json.contains("\"_elements_complete\":false"), json);
        require(json.contains(
                "\"provenance\":\"ARRAY_SHADOW\""), json);
        require(json.contains(
                "\"source_provenance\":\"INVALIDATED_ARRAYCOPY_EXCEPTION\""),
                json);
        require(json.contains(
                "\"_authority\":\"VM_EXACT_FINITE_ARRAY_VALUE_V1\""),
                json);
        String summary = System.finishConcolicRegion();
        require(summary.contains(
                "\"regionId\":\"REGION.arraycopy-exception\""),
                summary);
        System.out.println(
                "CAUSYNTH_REGION_ARRAYCOPY_EXCEPTION_API_SMOKE_OK");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}

/** Direct VM-envelope regression for finite array-value snapshots and shadow
 * propagation through AALOAD, AASTORE, and System.arraycopy. */
public final class RegionArrayValueApiSmoke {
    private static final class Holder {
        long expiry;

        private Holder(long expiry) {
            this.expiry = expiry;
        }
    }

    public static void main(String[] args) {
        Holder holder = new Holder(23L);
        Holder[] holderArray = new Holder[1];
        int[] primitiveArray = new int[] {7, 11};
        Object[] opaqueArray = new Object[] {new Object()};
        Object[] secondConcreteArray = new Object[] {null};
        Object[] copiedArray = new Object[] {null};
        Object[] symbolicArray = new Object[] {holder, null};
        Object[] symbolicNullDestination = new Object[] {null};
        Holder[] symbolicCopySource = new Holder[] {holder};
        Holder[] symbolicCopyDestination = new Holder[] {null};

        System.startConcolicRegion("REGION.array-value",
                "ACT.array-value");
        System.symbolize(holder, "array_value_holder");
        holderArray[0] = holder;
        Object restoredShadow = holderArray[0];
        secondConcreteArray[0] = restoredShadow;
        System.arraycopy(secondConcreteArray, 0, copiedArray, 0, 1);
        System.symbolize(symbolicArray, "array_value_symbolic_array");
        Object symbolicNull = symbolicArray[1];
        symbolicNullDestination[0] = symbolicNull;
        System.symbolize(symbolicCopySource,
                "array_value_symbolic_copy_source");
        System.arraycopy(symbolicCopySource, 0,
                symbolicCopyDestination, 0, 1);
        // Array shadows are keyed by GC-tracked handles; force a moving-GC
        // opportunity before every snapshot lookup.
        System.gc();

        System.pauseConcolicPathCondition();
        String holderJson = snapshot("holder", holderArray);
        String primitiveJson = snapshot("primitive", primitiveArray);
        String opaqueJson = snapshot("opaque", opaqueArray);
        String copiedJson = snapshot("copied", copiedArray);
        String symbolicArrayJson =
                snapshot("symbolic", symbolicArray);
        String symbolicNullJson =
                snapshot("symbolic-null-destination",
                        symbolicNullDestination);
        String symbolicCopyJson = snapshot("symbolic-copy-destination",
                symbolicCopyDestination);

        String summary = System.finishConcolicRegion();

        require(holderJson.contains("\"kind\":\"ARRAY_VALUE\""),
                holderJson);
        require(holderJson.contains(
                "\"_type\":\"ArrayValueExpression\""), holderJson);
        require(holderJson.contains("\"_schema_version\":1"),
                holderJson);
        require(holderJson.contains(
                "\"_java_type\":\"[LRegionArrayValueApiSmoke$Holder;\""),
                holderJson);
        require(holderJson.contains(
                "\"_component_java_type\":\"LRegionArrayValueApiSmoke$Holder;\""),
                holderJson);
        require(holderJson.contains("\"_concrete_length\":1"),
                holderJson);
        require(holderJson.contains(
                "\"_length_exp\":{\"_type\":\"ConstExpr\",\"_java_type\":\"I\",\"_exp\":\"Y_I_1\"}"),
                holderJson);
        require(holderJson.contains("\"_elements_complete\":true"),
                holderJson);
        require(holderJson.contains("\"index\":0,\"expression\":{"),
                holderJson);
        require(holderJson.contains(
                "\"provenance\":\"ARRAY_SHADOW\""), holderJson);
        require(holderJson.contains(
                "\"_authority\":\"VM_EXACT_FINITE_ARRAY_VALUE_V1\""),
                holderJson);
        require(!holderJson.contains("\"_engine_array_id\":"),
                holderJson);

        require(primitiveJson.contains("\"_java_type\":\"[I\""),
                primitiveJson);
        require(primitiveJson.contains(
                "\"_component_java_type\":\"I\""), primitiveJson);
        require(primitiveJson.contains("\"_concrete_length\":2"),
                primitiveJson);
        require(primitiveJson.contains("\"_exp\":\"Y_I_7\""),
                primitiveJson);
        require(primitiveJson.contains("\"_exp\":\"Y_I_11\""),
                primitiveJson);
        require(primitiveJson.contains("\"_elements_complete\":true"),
                primitiveJson);
        require(primitiveJson.contains(
                "\"provenance\":\"CONCRETE_PRIMITIVE\""),
                primitiveJson);

        require(opaqueJson.contains("\"_elements_complete\":false"),
                opaqueJson);
        require(opaqueJson.contains(
                "\"provenance\":\"SYMBOLIC_ELEMENT\""),
                opaqueJson);
        require(opaqueJson.contains(
                "\"source_provenance\":\"OPAQUE_CONCRETE_NON_NULL_REFERENCE\""),
                opaqueJson);

        require(copiedJson.contains("\"_elements_complete\":true"),
                copiedJson);
        require(copiedJson.contains(
                "\"provenance\":\"ARRAY_SHADOW\""),
                copiedJson);
        require(copiedJson.contains("\"_type\":\"SymbolExpression\""),
                copiedJson);
        require(symbolicArrayJson.contains("\"symbolic\":true"),
                symbolicArrayJson);
        require(symbolicArrayJson.contains("\"_elements_complete\":true"),
                symbolicArrayJson);
        require(symbolicArrayJson.contains("\"_type\":\"ArrayValueExpression\""),
                symbolicArrayJson);
        require(symbolicArrayJson.contains(
                "\"_length_exp\":{\"_type\":\"ConstExpr\",\"_java_type\":\"I\",\"_exp\":\"Y_I_2\"}"),
                symbolicArrayJson);
        require(symbolicArrayJson.contains(
                "\"_engine_array_id\":\"AL_"), symbolicArrayJson);
        require(symbolicArrayJson.contains(
                "\"_engine_array_id_authority\":\"VM_ACTIVE_SYM_ARRAY_ID_V1\""),
                symbolicArrayJson);
        require(symbolicNullJson.contains("\"_elements_complete\":true"),
                symbolicNullJson);
        require(symbolicNullJson.contains("\"_exp\":\"EL_"),
                symbolicNullJson);
        require(symbolicNullJson.contains(
                "\"_java_type\":\"Ljava/lang/Object;\""),
                symbolicNullJson);
        require(symbolicCopyJson.contains("\"_elements_complete\":true"),
                symbolicCopyJson);
        require(symbolicCopyJson.contains(
                "\"provenance\":\"ARRAY_SHADOW\""),
                symbolicCopyJson);
        require(symbolicCopyJson.contains(
                "\"_java_type\":\"RegionArrayValueApiSmoke$Holder\""),
                symbolicCopyJson);
        require(!symbolicCopyJson.contains("\"_engine_array_id\":"),
                symbolicCopyJson);

        require(summary.contains("\"regionId\":\"REGION.array-value\""),
                summary);
        System.out.println("CAUSYNTH_REGION_ARRAY_VALUE_API_SMOKE_OK");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }

    private static String snapshot(String phase, Object array) {
        return System.getSymbolicExpression(array);
    }
}

/**
 * Contract smoke for the one explicit mint API over a field that already
 * carries a propagated expression.
 *
 * <p>The HDFS-17899 shape: the region selects {@code serialNo} as a shared
 * carrier, the application then writes it from carrier reads whose every
 * candidate is a recorded constant, and only after that write does the
 * configured-source hook ask for the root.  The exact symbolizer must replace
 * that propagated shadow with the fresh symbol and publish the symbol as a
 * version, so that the read-back names one VM symbol and a later carrier
 * read observes the mint as a writer.  The recursive and by-name forms keep
 * the old invariant and never overwrite.</p>
 */
public final class RegionExactMintOverCarrierWriteSmoke {
    private static final class Holder {
        int serial = 5;
        int plain = 9;
    }

    private static final class Sink {
        int value;
    }

    public static void main(String[] args) {
        require(System.startConcolicRegion(
                "REGION.exact-mint", "TASK.exact-mint") == 0L,
                "region start rejected");

        Holder holder = new Holder();
        require(System.selectSharedFieldCarrier(holder, Holder.class.getName(),
                "serial", "I") > 0L, "carrier selection rejected");

        // An application write computed from a carrier read: the shadow is
        // now a tree over a ReadFrom whose only candidate is the constant
        // INITIAL version.
        holder.serial = holder.serial + 1;
        String propagated = field(holder, "serial");
        require(propagated.contains("\"kind\":\"SYMBOLIC_FIELD\""), propagated);
        require(propagated.contains("ReadFromExpression"), propagated);
        require(!propagated.contains("M_I_field_MINT.SERIAL"), propagated);

        // The exact mint replaces it.
        System.symbolizeExactField(holder, Holder.class.getName(), "serial",
                "I", "MINT.SERIAL");
        String minted = field(holder, "serial");
        require(minted.contains("\"kind\":\"SYMBOLIC_FIELD\""), minted);
        require(minted.contains("\"_type\":\"SymbolExpression\""), minted);
        require(minted.contains("\"_exp\":\"M_I_field_MINT.SERIAL"), minted);
        require(!minted.contains("ReadFromExpression"), minted);

        // The mint is a version too: INITIAL, the application write, the
        // mint.  A read of the carrier resolves over all three and the mint
        // is one of its arms.
        // One writerContextId per version entry; the envelope's expression
        // table also serializes a read's candidate fieldVersionIds, so that
        // key is not a version count.
        String versions = System.getSharedFieldVersions(
                holder, Holder.class.getName(), "serial", "I");
        require(count(versions, "\"writerContextId\"") == 3, versions);
        require(versions.contains("M_I_field_MINT.SERIAL"), versions);
        Sink sink = new Sink();
        sink.value = holder.serial;
        require(sink.value == 6, "concrete value changed by the mint: "
                + sink.value);
        String read = field(sink, "value");
        require(read.contains("ReadFromExpression"), read);
        require(read.contains("\"rf3\""), read);
        require(read.contains("M_I_field_MINT.SERIAL"), read);

        // A second exact mint on the same field replaces again: the caller
        // decides authority, the VM does not second-guess it.
        System.symbolizeExactField(holder, Holder.class.getName(), "serial",
                "I", "MINT.AGAIN");
        String again = field(holder, "serial");
        require(again.contains("\"_exp\":\"M_I_field_MINT.AGAIN"), again);
        require(count(System.getSharedFieldVersions(holder,
                Holder.class.getName(), "serial", "I"),
                "\"writerContextId\"") == 4, "second mint published no version");

        // The by-name form keeps the invariant: an existing expression is
        // never overwritten by it.
        System.symbolizeField(holder, "plain", "NAME.FIRST");
        String first = field(holder, "plain");
        require(first.contains("NAME.FIRST"), first);
        System.symbolizeField(holder, "plain", "NAME.SECOND");
        String second = field(holder, "plain");
        require(second.contains("NAME.FIRST"), second);
        require(!second.contains("NAME.SECOND"), second);

        // An unselected field takes the exact mint without any version.
        System.symbolizeExactField(holder, Holder.class.getName(), "plain",
                "I", "MINT.PLAIN");
        String plain = field(holder, "plain");
        require(plain.contains("\"_exp\":\"M_I_field_MINT.PLAIN"), plain);
        String unselected = System.getSharedFieldVersions(holder,
                Holder.class.getName(), "plain", "I");
        require(unselected.contains("\"selected\":false"), unselected);

        System.endConcolic();
        System.out.println("RegionExactMintOverCarrierWriteSmoke OK");
    }

    private static String field(Object owner, String name) {
        try {
            java.lang.reflect.Field field =
                    owner.getClass().getDeclaredField(name);
            field.setAccessible(true);
            return System.getSymbolicFieldExpression(owner,
                    owner.getClass().getName(), name, "I",
                    Integer.valueOf(field.getInt(owner)));
        } catch (ReflectiveOperationException failure) {
            throw new AssertionError(failure);
        }
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

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}

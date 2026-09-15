/**
 * Contract smoke for the one explicit mint API over a field that already
 * carries a propagated expression.
 *
 * <p>The HDFS-17899 shape: the application writes {@code serialNo} from a
 * read of another symbolic field, and only after that write does the
 * configured-source hook ask for the root.  The exact symbolizer must replace
 * that propagated shadow with the fresh symbol and publish the symbol as a
 * version, so that the read-back names one VM symbol and a later read of the
 * field observes the mint as the writer.  The recursive and by-name forms
 * keep the old invariant and never overwrite.  A mint publishes a version
 * whichever form performed it: a location's log begins at the first symbolic
 * value to reach it, and a mint is a symbolic write.</p>
 */
public final class RegionExactMintOverCarrierWriteSmoke {
    private static final class Holder {
        int serial = 5;
        int plain = 9;
    }

    /** The source the propagated expression comes from. */
    private static final class Source {
        int seed = 5;
    }

    private static final class Sink {
        int value;
    }

    public static void main(String[] args) {
        require(System.startConcolicRegion(
                "REGION.exact-mint", "TASK.exact-mint") == 0L,
                "region start rejected");

        Holder holder = new Holder();
        Source source = new Source();
        System.symbolizeField(source, "seed", "MINT.SEED");

        // An application write computed from a read of another symbolic
        // field: `serial` now carries a propagated tree over that read, and
        // this write is the first symbolic value to reach it, so it also
        // starts the field's version log.
        holder.serial = source.seed + 1;
        String propagated = field(holder, "serial");
        require(propagated.contains("\"kind\":\"SYMBOLIC_FIELD\""), propagated);
        require(propagated.contains("ReadFromExpression"), propagated);
        require(propagated.contains("MINT.SEED"), propagated);
        require(!propagated.contains("M_I_field_MINT.SERIAL"), propagated);

        // The exact mint replaces it.
        System.symbolizeExactField(holder, Holder.class.getName(), "serial",
                "I", "MINT.SERIAL");
        String minted = field(holder, "serial");
        require(minted.contains("\"kind\":\"SYMBOLIC_FIELD\""), minted);
        require(minted.contains("\"_type\":\"SymbolExpression\""), minted);
        require(minted.contains("\"_exp\":\"M_I_field_MINT.SERIAL"), minted);
        require(!minted.contains("ReadFromExpression"), minted);
        require(!minted.contains("MINT.SEED"), minted);

        // The mint is a version too: the application write, then the mint.
        // A later read of the field observes the mint, because the mint is
        // the newest version of it.
        // One writerContextId per version entry; the envelope's expression
        // table also serializes a read node's own fieldVersionId, so that key
        // is not a version count.
        String versions = System.getSharedFieldVersions(
                holder, Holder.class.getName(), "serial", "I");
        require(count(versions, "\"writerContextId\"") == 2, versions);
        require(versions.contains("M_I_field_MINT.SERIAL"), versions);
        Sink sink = new Sink();
        sink.value = holder.serial;
        require(sink.value == 6, "concrete value changed by the mint: "
                + sink.value);
        String read = field(sink, "value");
        require(read.contains("ReadFromExpression"), read);
        // The read observed the mint, so the mint's symbol is the value it
        // carries and the propagated write below it is not in the read.
        require(read.contains("M_I_field_MINT.SERIAL"), read);
        require(!read.contains("MINT.SEED"), read);

        // A second exact mint on the same field replaces again: the caller
        // decides authority, the VM does not second-guess it.
        System.symbolizeExactField(holder, Holder.class.getName(), "serial",
                "I", "MINT.AGAIN");
        String again = field(holder, "serial");
        require(again.contains("\"_exp\":\"M_I_field_MINT.AGAIN"), again);
        require(count(System.getSharedFieldVersions(holder,
                Holder.class.getName(), "serial", "I"),
                "\"writerContextId\"") == 3, "second mint published no version");

        // The by-name form keeps the invariant: an existing expression is
        // never overwritten by it.
        System.symbolizeField(holder, "plain", "NAME.FIRST");
        String first = field(holder, "plain");
        require(first.contains("NAME.FIRST"), first);
        System.symbolizeField(holder, "plain", "NAME.SECOND");
        String second = field(holder, "plain");
        require(second.contains("NAME.FIRST"), second);
        require(!second.contains("NAME.SECOND"), second);

        // Every mint publishes a version, whichever form performed it: the
        // by-name symbol and the exact one that replaced it are both writers
        // a later projection of this field can name.
        System.symbolizeExactField(holder, Holder.class.getName(), "plain",
                "I", "MINT.PLAIN");
        String plain = field(holder, "plain");
        require(plain.contains("\"_exp\":\"M_I_field_MINT.PLAIN"), plain);
        String plainVersions = System.getSharedFieldVersions(holder,
                Holder.class.getName(), "plain", "I");
        require(plainVersions.contains("\"selected\":true"), plainVersions);
        require(count(plainVersions, "\"writerContextId\"") == 2,
                plainVersions);
        require(plainVersions.contains("M_I_field_NAME.FIRST"), plainVersions);
        require(plainVersions.contains("M_I_field_MINT.PLAIN"), plainVersions);

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

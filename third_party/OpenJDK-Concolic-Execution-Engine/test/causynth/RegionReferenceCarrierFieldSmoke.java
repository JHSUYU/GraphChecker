/**
 * Contract smoke for a read through a reference-typed shared carrier.
 *
 * <p>The HDFS-17899 bug3 shape: the region selects an object-valued field
 * ({@code BlockTokenSecretManager#currentKey}) as a carrier, two writers
 * install two different objects in it, and the program then reads a
 * <em>field of whatever object is in there</em> ({@code currentKey.keyId}).
 * The value of that second read is not a property of the object this
 * execution happened to walk: it belongs to whichever writer the solver
 * selects.  The dependent getfield must therefore keep the owner's
 * read-from choice, and carry alongside it the object this run actually read
 * from and what its field then held -- the pair that pins the arm the run
 * took without saying anything about the arms it did not.</p>
 */
public final class RegionReferenceCarrierFieldSmoke {
    private static final class Key {
        final int keyId;

        Key(int keyId) {
            this.keyId = keyId;
        }
    }

    private static final class Holder {
        Key current;
        Key untracked;
    }

    private static final class Sink {
        int value;
    }

    private static final String KEY_DESCRIPTOR =
            "L" + Key.class.getName().replace('.', '/') + ";";

    public static void main(String[] args) {
        require(System.startConcolicRegion(
                "REGION.reference-carrier", "TASK.reference-carrier") == 0L,
                "region start rejected");

        Holder holder = new Holder();
        holder.current = new Key(11);
        holder.untracked = new Key(41);

        // Selecting a reference field publishes the identity it holds now.
        require(System.selectSharedFieldCarrier(holder,
                Holder.class.getName(), "current", KEY_DESCRIPTOR) > 0L,
                "reference carrier selection rejected");

        // A second writer installs a different object, which is a competing
        // identity rather than a competing scalar.
        Key installed = new Key(23);
        holder.current = installed;

        String versions = System.getSharedFieldVersions(holder,
                Holder.class.getName(), "current", KEY_DESCRIPTOR);
        require(versions.contains("\"writerSetComplete\":true"), versions);
        require(count(versions, "\"fieldVersionId\"") == 2, versions);
        require(versions.contains("InstanceSymbolExp"), versions);

        // The dependent read: one getfield of the carrier, then a getfield
        // of the object it produced.
        Sink sink = new Sink();
        sink.value = holder.current.keyId;
        require(sink.value == 23, "concrete dependent read changed: "
                + sink.value);

        String dependent = expression(sink);
        require(dependent.contains("\"_type\":\"FieldAccessExpression\""),
                dependent);
        require(dependent.contains("ReadFromExpression"), dependent);
        require(dependent.contains("\"exactlyOne\":[\"rf1\",\"rf2\"]"),
                dependent);
        // The owner is the choice, not the object this run walked.
        require(dependent.contains("\"concreteOwner\""), dependent);
        require(dependent.contains("\"concreteValue\""), dependent);

        // A read through a reference nobody selected is unchanged: no owner
        // choice exists, so there is no arm to pin and no pair to carry.
        Sink plain = new Sink();
        plain.value = holder.untracked.keyId;
        require(plain.value == 41, "concrete untracked read changed: "
                + plain.value);
        String untracked = expression(plain);
        require(!untracked.contains("\"concreteOwner\""), untracked);

        System.endConcolic();
        System.out.println("RegionReferenceCarrierFieldSmoke OK");
    }

    private static String expression(Sink sink) {
        return System.getSymbolicFieldExpression(sink, Sink.class.getName(),
                "value", "I", Integer.valueOf(sink.value));
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

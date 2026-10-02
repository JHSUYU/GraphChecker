/**
 * Contract smoke: a stored reference is symbolic only by what it carries.
 *
 * <p>An object whose shadow only names it -- here the owner of an observed
 * field -- stored into a field of another object, or into an array, is a
 * concrete store: it starts no log there, and null does not either.  A load
 * of it back out of that array is the plain object, so a field read of it is
 * concrete, not a projection.  Counted symbolic, such a name started a log at
 * every location it reached and made an array load of it demand-symbolic
 * (hdfs-17960: a checkpoint saver's thread, and its context class loader into
 * a whole configuration parse).  A field a log already holds still versions
 * the same store, naming its referent.</p>
 */
public final class RegionNamedReferenceStoreSmoke {
    private static final String OBJECT = "Ljava/lang/Object;";

    private static final class Owner {
        long count = 1L;
        long plain = 7L;
    }

    private static final class Holder {
        Object ref;
        Object observed;
    }

    private static final class Sink {
        long value;
    }

    public static void main(String[] args) {
        require(System.startConcolicRegion("REGION.named-store",
                "TASK.named-store") == 0L, "region start rejected");

        // The observation gives the owner a shadow that only names it.
        Owner owner = new Owner();
        require(System.observeField(owner, Owner.class.getName(), "count",
                "J") == 0, "the observation failed");

        Holder holder = new Holder();
        holder.ref = owner;
        holder.ref = null;
        holder.ref = owner;
        String field = System.getSharedFieldVersions(holder,
                Holder.class.getName(), "ref", OBJECT);

        Object[] array = new Object[1];
        array[0] = owner;
        String element = System.getSharedElementVersions(array, 0);
        Owner loaded = (Owner) array[0];
        Sink sink = new Sink();
        sink.value = loaded.plain;
        String projected = System.getSymbolicFieldExpression(sink,
                Sink.class.getName(), "value", "J",
                Long.valueOf(sink.value));

        // Where a log stands, the same store is a version naming the owner.
        require(System.observeField(holder, Holder.class.getName(),
                "observed", OBJECT) == 0, "the second observation failed");
        holder.observed = owner;
        String observed = System.getSharedFieldVersions(holder,
                Holder.class.getName(), "observed", OBJECT);
        System.endConcolic();

        require(field.contains("\"selected\":false"),
                "a named reference started a field's log: " + field);
        require(element.contains("\"selected\":false"),
                "a named reference started an element's log: " + element);
        require(projected.contains("\"kind\":\"CONCRETE_PRIMITIVE\"")
                        && !projected.contains("FieldAccessExpression"),
                "an array load of a named element made it symbolic: "
                        + projected);
        require(observed.contains("\"versionKind\":\"INITIAL\"")
                        && observed.contains("\"versionKind\":\"WRITE\""),
                "a tracked field did not version the store: " + observed);
        System.out.println("RegionNamedReferenceStoreSmoke OK");
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}

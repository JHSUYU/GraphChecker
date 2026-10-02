/**
 * Contract smoke: a stored reference is symbolic only by what it carries.
 *
 * <p>An object whose shadow only names it -- here the owner of an observed
 * field -- stored into a field of another object, into a static field, or
 * into an array, is a concrete store: it starts no log there, and null does
 * not either.  A load of it back out of that array is the plain object, so a
 * field read of it is concrete, not a projection.  Counted symbolic, such a
 * name started a log at every location it reached and made an array load of
 * it demand-symbolic (hdfs-17960: a checkpoint saver's thread, and its
 * context class loader into a whole configuration parse).  A field a log
 * holds -- an instance one observed on its object, a static one on its
 * class's mirror -- still versions the same stores: the WRITE names the
 * object stored, and a null stored there is a version a read states.</p>
 */
public final class RegionNamedReferenceStoreSmoke {
    private static final String OBJECT = "Ljava/lang/Object;";
    private static final String OWNER =
            "_exp\":\"M_L'RegionNamedReferenceStoreSmoke$Owner'_";

    private static final class Owner {
        long count = 1L;
        long plain = 7L;
    }

    private static final class Holder {
        Object ref;
        Object observed;
    }

    private static final class Registry {
        static Object slot;
        static Object observed;
    }

    private static final class Sink {
        long value;
        Object ref;
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
        Registry.slot = null;
        Registry.slot = owner;
        String unobservedStatic = System.getSharedFieldVersions(
                Registry.class, Registry.class.getName(), "slot", OBJECT);

        Object[] array = new Object[1];
        array[0] = owner;
        String element = System.getSharedElementVersions(array, 0);
        Owner loaded = (Owner) array[0];
        Sink sink = new Sink();
        sink.value = loaded.plain;
        String projected = System.getSymbolicFieldExpression(sink,
                Sink.class.getName(), "value", "J",
                Long.valueOf(sink.value));

        // Where a log stands, the same stores are versions: the WRITE names
        // the owner, and a null stored there is read back as a version.
        require(System.observeField(holder, Holder.class.getName(),
                "observed", OBJECT) == 0, "the second observation failed");
        holder.observed = owner;
        String observed = System.getSharedFieldVersions(holder,
                Holder.class.getName(), "observed", OBJECT);
        holder.observed = null;
        sink.ref = holder.observed;
        String nulled = System.getSymbolicFieldExpression(sink,
                Sink.class.getName(), "ref", OBJECT, sink.ref);
        require(System.observeField(Registry.class, Registry.class.getName(),
                "observed", OBJECT) == 0, "the static observation failed");
        Registry.observed = owner;
        String observedStatic = System.getSharedFieldVersions(
                Registry.class, Registry.class.getName(), "observed", OBJECT);
        System.endConcolic();

        require(field.contains("\"selected\":false"),
                "a named reference started a field's log: " + field);
        require(unobservedStatic.contains("\"selected\":false"),
                "a named reference started a static's log: "
                        + unobservedStatic);
        require(element.contains("\"selected\":false"),
                "a named reference started an element's log: " + element);
        require(projected.contains("\"kind\":\"CONCRETE_PRIMITIVE\"")
                        && !projected.contains("FieldAccessExpression"),
                "an array load of a named element made it symbolic: "
                        + projected);
        require(observed.contains("\"versionKind\":\"INITIAL\"")
                        && observed.contains("\"versionKind\":\"WRITE\"")
                        && observed.contains(OWNER),
                "a tracked field's WRITE does not name the owner: "
                        + observed);
        require(nulled.contains("\"_type\":\"ReadFromExpression\"")
                        && nulled.contains("\"concreteValue\":null"),
                "the null stored into a tracked field is no version its"
                        + " read states: " + nulled);
        require(observedStatic.contains("\"versionKind\":\"INITIAL\"")
                        && observedStatic.contains("\"versionKind\":\"WRITE\"")
                        && observedStatic.contains(OWNER),
                "a static observed on its class's mirror does not version"
                        + " the store: " + observedStatic);
        System.out.println("RegionNamedReferenceStoreSmoke OK");
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}

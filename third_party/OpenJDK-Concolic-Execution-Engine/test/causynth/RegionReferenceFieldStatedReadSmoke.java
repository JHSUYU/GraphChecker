/**
 * Contract smoke for what a reference-typed field read states.
 *
 * <p>The HDFS-17960 shape: a region input is an object container, an object
 * is taken out of it, and the program then reads a <em>reference</em>-typed
 * field of that object -- {@code Snapshot.root}, reached from the snapshot
 * map.  A read like that is a projection the write log does not cover, so
 * the only thing that can value it is the pair the VM states beside it: the
 * object read from, and what the field then held.  A primitive-typed read on
 * the same object has stated that pair since "Every primitive field read
 * states what it read"; a reference-typed one stated neither, and every
 * anchor path through one was refused as {@code UNSTATED_FIELD_PROJECTION}.
 *
 * <p>So both shapes are asserted here side by side, and the reference read's
 * answer is an identity in the same spelling an owner identity has -- which
 * is what lets the composer equate a read reference with the owner of
 * another read -- or the null symbol {@code N} when the field held null.</p>
 */
public final class RegionReferenceFieldStatedReadSmoke {
    private static final class Leaf {
        final int id;

        Leaf(int id) {
            this.id = id;
        }
    }

    private static final class Node {
        final int tag;
        final Leaf leaf;
        final Leaf absent;
        final int[] payload;

        Node(int tag, Leaf leaf, Leaf absent, int[] payload) {
            this.tag = tag;
            this.leaf = leaf;
            this.absent = absent;
            this.payload = payload;
        }
    }

    private static final class Sink {
        int total;
    }

    private static final int PAYLOAD_LENGTH = 4096;

    private static int[] payload() {
        int[] values = new int[PAYLOAD_LENGTH];
        for (int index = 0; index < values.length; index++) {
            values[index] = index;
        }
        return values;
    }

    private static final class Input {
        final Node[] nodes =
                {new Node(5, new Leaf(7), null, payload())};
    }

    private static final String LEAF_DESCRIPTOR =
            "L" + Leaf.class.getName().replace('.', '/') + ";";

    public static void main(String[] args) {
        Input input = new Input();

        require(System.startConcolicRegion("REGION.reference-field-read",
                "TASK.reference-field-read") == 0L, "region start rejected");
        System.symbolizeField(input, "nodes", "reference_field_nodes");

        // Out of the symbolic container, so the element's own fields are
        // materialized on demand at getfield -- the mint that has to state
        // what it read.
        Node node = input.nodes[0];
        int tag = node.tag;
        Leaf leaf = node.leaf;
        Leaf absent = node.absent;

        require(tag == 5, "concrete primitive read changed: " + tag);
        require(leaf != null && leaf.id == 7, "concrete reference read");
        require(absent == null, "concrete null read changed");

        String primitiveRead = System.getSymbolicFieldExpression(node,
                Node.class.getName(), "tag", "I", Integer.valueOf(tag));
        String referenceRead = System.getSymbolicFieldExpression(node,
                Node.class.getName(), "leaf", LEAF_DESCRIPTOR, leaf);
        String nullRead = System.getSymbolicFieldExpression(node,
                Node.class.getName(), "absent", LEAF_DESCRIPTOR, absent);

        System.out.println("PRIMITIVE_READ " + primitiveRead);
        System.out.println("REFERENCE_READ " + referenceRead);
        System.out.println("NULL_READ " + nullRead);

        // The primitive read, unchanged: a projection with the pair beside it.
        require(primitiveRead.contains("\"kind\":\"SYMBOLIC_FIELD\""),
                primitiveRead);
        require(primitiveRead.contains("\"_type\":\"FieldAccessExpression\""),
                primitiveRead);
        require(primitiveRead.contains("\"_java_type\":\"I\""),
                primitiveRead);
        require(primitiveRead.contains("\"concreteOwner\""), primitiveRead);
        require(referenced(primitiveRead, "concreteValue").startsWith(
                "{\"_type\":\"ConstExpr\",\"_java_type\":\"I\","
                + "\"_exp\":\"Y_I_5\"}"), primitiveRead);

        // The reference read now states the same pair.  Its value is the
        // identity of the object it read, spelled as any owner identity is.
        require(referenceRead.contains("\"kind\":\"SYMBOLIC_FIELD\""),
                referenceRead);
        require(referenceRead.contains("\"_type\":\"FieldAccessExpression\""),
                referenceRead);
        require(referenceRead.contains("\"_java_type\":\"L\""),
                referenceRead);
        require(referenceRead.contains("\"concreteOwner\""), referenceRead);
        require(referenced(referenceRead, "concreteValue").startsWith(
                "{\"_type\":\"SymbolExpression\",\"_java_type\":\""
                + Leaf.class.getName() + "\",\"_exp\":\"M_L'"
                + Leaf.class.getName() + "'_"), referenceRead);

        // A field that held null states the null symbol, not an absent
        // member: "it was null" and "nothing was recorded" are different
        // answers and only the first one is true here.
        require(nullRead.contains("\"kind\":\"SYMBOLIC_FIELD\""), nullRead);
        require(nullRead.contains("\"_java_type\":\"L\""), nullRead);
        require(nullRead.contains("\"concreteOwner\""), nullRead);
        require(referenced(nullRead, "concreteValue").startsWith(
                "{\"_type\":\"SymbolExpression\",\"_java_type\":\"\","
                + "\"_exp\":\"N\"}"), nullRead);

        namedReferentStaysConcrete(node);

        require(System.finishConcolicRegion().contains("\"complete\":true"),
                "summary incomplete");
        System.out.println(
                "CAUSYNTH_REGION_REFERENCE_FIELD_STATED_READ_SMOKE_OK");
    }

    /**
     * A named referent is inert.
     *
     * <p>Stating the identity of what a reference read returned is a naming
     * act.  It must not decide that the object is symbolic: its own element
     * and field loads stay concrete, produce no expression, and record no
     * path condition.  Naming used to allocate a shadow, and a shadow is
     * what `CONCOLIC_ALOAD` gates on, so one named array-valued field put
     * every element load of that array on the container path -- a state root,
     * a position constraint and a path condition per load.  On 17960's seed
     * that was 57 MB of expressions and 39 GB of RSS for a recording that had
     * only been asked for a name.</p>
     */
    private static void namedReferentStaysConcrete(Node node) {
        int[] payload = node.payload;
        Leaf leaf = node.leaf;

        // The reference read still states the identity, for an array in the
        // spelling an array owner identity has.
        String arrayRead = System.getSymbolicFieldExpression(node,
                Node.class.getName(), "payload", "[I", payload);
        require(arrayRead.contains("\"_java_type\":\"L\""), arrayRead);
        require(referenced(arrayRead, "concreteValue").startsWith(
                "{\"_type\":\"SymbolExpression\",\"_java_type\":\"L\","
                + "\"_exp\":\"AL_"), arrayRead);

        String before = System.getPathCondition();
        int sum = 0;
        for (int index = 0; index < payload.length; index++) {
            sum += payload[index];
        }
        int identifier = leaf.id;
        String after = System.getPathCondition();

        require(sum == PAYLOAD_LENGTH * (PAYLOAD_LENGTH - 1) / 2,
                "concrete element loads changed: " + sum);
        require(identifier == 7, "concrete field load changed: "
                + identifier);
        // Byte-identical, which is the whole claim: these loads produced no
        // expression, so there was nothing for them to record.
        require(after.equals(before), PAYLOAD_LENGTH
                + " element loads and one field load of named referents"
                + " changed the path condition: " + before.length()
                + " -> " + after.length() + " chars; " + after);

        // Neither referent is symbolic, so neither has a container state or
        // an object shadow to hand back.
        String namedArray = System.getSymbolicExpression(payload);
        require(namedArray.contains("\"symbolic\":false"), namedArray);
        require(namedArray.contains("\"kind\":\"CONCRETE_OBJECT\""),
                namedArray);
        String namedObject = System.getSymbolicExpression(leaf);
        require(namedObject.contains("\"symbolic\":false"), namedObject);
        require(namedObject.contains("\"kind\":\"CONCRETE_OBJECT\""),
                namedObject);

        // And the values those loads produced carry no expression at all.
        Sink sink = new Sink();
        sink.total = sum + identifier;
        String carried = System.getSymbolicFieldExpression(sink,
                Sink.class.getName(), "total", "I",
                Integer.valueOf(sink.total));
        require(carried.contains("\"kind\":\"CONCRETE_PRIMITIVE\""),
                carried);
        require(!carried.contains("ContainerRelation"), carried);
        require(!carried.contains("FieldAccessExpression"), carried);
    }

    /**
     * The definition text that one member of the serialized root node
     * references.
     *
     * <p>A field-expression envelope names its nodes by id and defines each
     * one once in its {@code vmExpressionTable}, so a member's value is a
     * {@code VmExpressionReference} rather than the node itself.  Asserting
     * on the definition the member resolves to -- instead of on any
     * definition the table happens to hold -- is what makes the answer
     * belong to that member.</p>
     */
    private static String referenced(String json, String member) {
        String reference = "\"" + member
                + "\":{\"_type\":\"VmExpressionReference\"";
        int at = json.indexOf(reference);
        require(at >= 0, member + " is not a node reference in " + json);
        String idKey = "\"expressionId\":";
        int idAt = json.indexOf(idKey, at);
        require(idAt >= 0, json);
        int from = idAt + idKey.length();
        int to = from;
        while (to < json.length() && json.charAt(to) >= '0'
                && json.charAt(to) <= '9') {
            to++;
        }
        // The definition entry, not another reference: only a definition is
        // followed by its `expression` member.
        String definitionKey = idKey + json.substring(from, to)
                + ",\"expression\":";
        int definitionAt = json.indexOf(definitionKey);
        require(definitionAt >= 0,
                "no definition for " + member + " in " + json);
        return json.substring(definitionAt + definitionKey.length());
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}

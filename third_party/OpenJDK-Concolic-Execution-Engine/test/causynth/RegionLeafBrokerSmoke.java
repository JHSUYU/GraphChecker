import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

/**
 * System.exportLeaf and System.mintLeaf (concolic/leafBroker.hpp), and the one
 * `toString` op every decimal and boolean rendering is.
 *
 * <p>Each check is one row: the call, the status it must answer, and the text
 * its answer must (and must not) hold.  The rows run outside every region
 * (under the workload session), inside one, and before any session exists.
 */
public final class RegionLeafBrokerSmoke {
    private static final int FIELD = 0;
    private static final int ELEMENT = 1;
    private static final int ENTRY = 2;
    private static final int POSITION = 3;
    private static final int VALUE = 4;

    private static final class Source {
        long n;
        boolean flag;
    }

    private static final class Message {
        long id;
        String name;
        String absent;
    }

    private static final class Flags {
        Boolean on = Boolean.TRUE;
        Boolean fresh = new Boolean(true);
        Thread.State state = Thread.State.NEW;
    }

    public static void main(String[] args) throws Exception {
        refusedWithoutASession();
        require(System.openWorkloadSession() > 0L,
                "workload session not opened");
        exportsConstantsOutsideEveryRegion();
        Built built = buildsSymbolicLeavesInARegion();
        exportsSymbolicLeavesOutsideEveryRegion(built);
        Minted minted = mintsOutsideEveryRegion(built);
        aRegionReadsAnEntryMintThroughParseLong(minted);
        aRegionReadsTheOtherMints(minted);
        onlyAValueOperandOpensTheGate(minted);
        theSymbolizersLeaveJvmWideObjectsClean();
        require(System.closeWorkloadSession() == 0L,
                "workload session not closed");
        System.out.println("RegionLeafBrokerSmoke OK");
    }

    /** No region and no workload session: both natives refuse by name. */
    private static void refusedWithoutASession() throws Exception {
        Source source = new Source();
        expect(System.exportLeaf(source, FIELD, field(Source.class, "n")),
                "NO_SESSION");
        expect(System.mintLeaf(source, FIELD, field(Source.class, "n"),
                num("HOFF.none")), "NO_SESSION");
    }

    /** A slot, then the leaf object, then a typed constant; refusals named. */
    private static void exportsConstantsOutsideEveryRegion() throws Exception {
        Source source = new Source();
        source.n = 1727L;
        long[] longs = new long[]{5L, 6L};
        Map<String, String> map = new HashMap<String, String>();
        map.put("k", new String("v"));
        List<String> list = new ArrayList<String>();
        list.add("a");
        Message message = new Message();
        Map<String, String> sorted = new TreeMap<String, String>();
        sorted.put("k", "v");

        Field n = field(Source.class, "n");
        expect(System.exportLeaf(source, FIELD, n), "CONSTANT",
                "\"source\":\"CONSTANT\"", "Y_J_1727", "\"javaType\":\"J\"",
                "\"exportEvent\":");
        expect(System.exportLeaf(longs, ELEMENT, Integer.valueOf(1)),
                "CONSTANT", "Y_J_6");
        expect(System.exportLeaf(map, ENTRY, "k"), "CONSTANT",
                "Y_L'String'_v", "\"javaType\":\"Ljava/lang/String;\"",
                "\"concrete\":\"v\"");
        expect(System.exportLeaf(list, POSITION, Integer.valueOf(0)),
                "CONSTANT", "Y_L'String'_a");
        expect(System.exportLeaf(new String("w"), VALUE, null), "CONSTANT",
                "Y_L'String'_w");
        expect(System.exportLeaf(new Long(3L), VALUE, null), "CONSTANT",
                "Y_J_3", "\"javaType\":\"J\"");

        expect(System.exportLeaf(message, FIELD,
                field(Message.class, "absent")), "NULL_LEAF");
        expect(System.exportLeaf(map, ENTRY, "missing"), "SLOT_MISSING",
                "KEY_ABSENT");
        expect(System.exportLeaf(longs, ELEMENT, Integer.valueOf(9)),
                "SLOT_MISSING", "INDEX_OUT_OF_RANGE");
        expect(System.exportLeaf(message, FIELD, n), "SLOT_MISSING",
                "FIELD_NOT_OF_PARENT");
        expect(System.exportLeaf(new Object(), VALUE, null), "UNSUPPORTED",
                "LEAF_CLASS:java.lang.Object");
        expect(System.exportLeaf(sorted, ENTRY, "k"), "UNSUPPORTED",
                "NOT_A_MODELED_MAP:java.util.TreeMap");
    }

    private static final class Built {
        Source source;
        long[] longs;
        Map<String, String> map;
        List<String> list;
        String rendered;
    }

    /**
     * A symbolic field, element, entry, position and String built in a
     * region; peeks of them record nothing; every decimal and boolean
     * rendering is one `toString` op.
     */
    private static Built buildsSymbolicLeavesInARegion() throws Exception {
        Built built = new Built();
        Field n = field(Source.class, "n");
        require(System.startConcolicRegion("REGION.leaf-build",
                "TASK.leaf-build") == 0L, "region start rejected");
        built.source = new Source();
        built.source.n = 1727L;
        built.source.flag = true;
        System.symbolizeExactField(built.source, Source.class.getName(), "n",
                "J", "SRC.n");
        System.symbolizeExactField(built.source, Source.class.getName(),
                "flag", "Z", "SRC.flag");
        long value = built.source.n;
        boolean flag = built.source.flag;
        built.longs = new long[2];
        built.longs[1] = value;
        built.map = new HashMap<String, String>();
        built.map.put("plain", "x");
        built.map.put("expireAt", String.valueOf(value));
        built.list = new ArrayList<String>();
        built.list.add("a");
        built.list.add(Long.toString(value));
        built.rendered = Long.toString(value);

        // One op for every decimal and boolean rendering.  A decimal
        // rendering is a fresh String that carries its expression; a boolean
        // one is an interned literal, whose expression rides only the slot,
        // so its decision states it.
        String[] renderings = {
            built.rendered,
            String.valueOf(value),
            new StringBuilder().append(value).toString(),
            String.valueOf(Long.valueOf(value)),
            Short.toString((short) value),
        };
        for (String rendering : renderings) {
            String expression = System.getSymbolicExpression(rendering);
            require(expression.contains("\"_name\":\"toString\""),
                    expression);
            require(expression.contains("M_J_field_SRC.n"), expression);
            require(!expression.contains("\"_name\":\"valueOf\""),
                    expression);
            require(!expression.contains(
                    "unsupportedPrimitiveStringConversion"), expression);
        }
        boolean statically = Boolean.toString(flag).contains("t");
        System.markConcolicBranch("LEAF.BOOLEAN.TOSTRING", 1);
        if (!statically) throw new AssertionError("Boolean.toString");
        boolean viaValueOf = String.valueOf(flag).contains("t");
        System.markConcolicBranch("LEAF.BOOLEAN.VALUEOF", 1);
        if (!viaValueOf) throw new AssertionError("String.valueOf");
        String decided = System.getConcolicPathConditionRange(0,
                Integer.MAX_VALUE);
        require(count(decided, "\"_name\":\"contains\"") >= 2, decided);
        require(decided.contains("\"_name\":\"toString\"")
                && decided.contains("M_Z_field_SRC.flag"), decided);
        require(!decided.contains("\"_name\":\"valueOf\"")
                && !decided.contains("unsupportedPrimitiveStringConversion"),
                decided);
        String radix = System.getSymbolicExpression(
                Long.toString(value, 16));
        require(radix.contains("unsupportedPrimitiveStringConversion:"
                + "java/lang/Long.toString(JI)Ljava/lang/String;"), radix);

        // A peek records nothing: no condition, no read, no version.  The
        // leaves are in locals first, so this code reads no tracked field of
        // its own between the two logs (`built.rendered` is one: a symbolic
        // store started its log).
        Integer one = Integer.valueOf(1);
        Integer zero = Integer.valueOf(0);
        Source source = built.source;
        long[] longs = built.longs;
        Map<String, String> map = built.map;
        List<String> list = built.list;
        String rendered = built.rendered;
        String fresh = new String("12");
        String minted = mint(fresh, VALUE, null, parts(dec("DEC_LONG",
                "HOFF.inside", "12")), "OK");
        require(minted.contains("M_J_field_HOFF.inside"), minted);
        String pathBefore = System.getConcolicPathConditionRange(0,
                Integer.MAX_VALUE);
        String logBefore = System.getTrackedLocationVersions(0L, 0);
        String[] peeks = {
            expect(System.exportLeaf(source, FIELD, n), "OK",
                    "\"source\":\"SLOT\"", "M_J_field_SRC.n"),
            expect(System.exportLeaf(longs, ELEMENT, one), "OK",
                    "\"source\":\"SLOT\"", "M_J_field_SRC.n"),
            expect(System.exportLeaf(longs, ELEMENT, zero),
                    "CONSTANT", "Y_J_0"),
            expect(System.exportLeaf(map, ENTRY, "expireAt"), "OK",
                    "\"source\":\"SLOT\"", "\"_name\":\"toString\"",
                    "M_J_field_SRC.n"),
            expect(System.exportLeaf(map, ENTRY, "plain"), "OK",
                    "\"source\":\"SLOT\"", "Y_L'String'_x"),
            expect(System.exportLeaf(list, POSITION, one), "OK",
                    "\"source\":\"SLOT\"", "\"_name\":\"toString\"",
                    "M_J_field_SRC.n"),
            expect(System.exportLeaf(list, POSITION, zero), "OK",
                    "\"source\":\"SLOT\"", "Y_L'String'_a"),
            expect(System.exportLeaf(rendered, VALUE, null), "OK",
                    "\"source\":\"OBJECT\"", "M_J_field_SRC.n"),
            expect(System.exportLeaf(fresh, VALUE, null), "OK",
                    "\"source\":\"OBJECT\"", "M_J_field_HOFF.inside"),
        };
        String pathAfter = System.getConcolicPathConditionRange(0,
                Integer.MAX_VALUE);
        String logAfter = System.getTrackedLocationVersions(0L, 0);
        require(conditionCount(pathBefore) == conditionCount(pathAfter),
                "a peek recorded a condition: " + pathBefore + " / "
                        + pathAfter);
        require(count(logBefore, "\"readEventId\"")
                        == count(logAfter, "\"readEventId\""),
                "a peek recorded a read: " + logBefore + "\n" + logAfter);
        require(count(logBefore, "\"writerContextId\"")
                        == count(logAfter, "\"writerContextId\""),
                "a peek published a version: " + logAfter);
        require(peeks.length == 9, "peek rows");
        require(System.finishConcolicRegion().contains("\"complete\":true"),
                "region finish failed");
        return built;
    }

    /** The same leaves, peeked by a thread outside every region. */
    private static void exportsSymbolicLeavesOutsideEveryRegion(Built built)
            throws Exception {
        expect(System.exportLeaf(built.source, FIELD,
                field(Source.class, "n")), "OK", "M_J_field_SRC.n");
        expect(System.exportLeaf(built.map, ENTRY, "expireAt"), "OK",
                "\"_name\":\"toString\"", "M_J_field_SRC.n");
        expect(System.exportLeaf(built.list, POSITION, Integer.valueOf(1)),
                "OK", "M_J_field_SRC.n");
        expect(System.exportLeaf(built.rendered, VALUE, null), "OK",
                "\"source\":\"OBJECT\"", "M_J_field_SRC.n");
    }

    private static final class Minted {
        Message message;
        String pair;
        Long box;
        Map<String, String> decoded;
        String[] elements;
        List<String> positional;
    }

    /** Mints through every slot kind by a thread outside every region. */
    private static Minted mintsOutsideEveryRegion(Built built)
            throws Exception {
        Minted minted = new Minted();
        minted.message = new Message();
        minted.message.id = 42L;
        minted.message.name = new String("1727-x");
        mint(minted.message, FIELD, field(Message.class, "id"),
                num("HOFF.id"), "OK", "\"exp\":\"M_J_field_HOFF.id\"",
                "\"kind\":\"NUM\"", "Y_J_42");
        mint(minted.message, FIELD, field(Message.class, "name"),
                parts(dec("DEC_LONG", "HOFF.name", "1727"), literal("-x")),
                "OK", "\"_name\":\"concat\"", "\"_name\":\"toString\"",
                "M_J_field_HOFF.name", "Y_L'String'_-x", "Y_J_1727");

        minted.pair = new String("42:abc");
        mint(minted.pair, VALUE, null, parts(dec("DEC_INT", "HOFF.int",
                "42"), literal(":"), dec("STR", "HOFF.str", "abc")), "OK",
                "M_I_field_HOFF.int", "M_L'String'_field_HOFF.str",
                "\"concreteValue\":\"abc\"",
                "\"javaType\":\"Ljava/lang/String;\"");

        minted.box = new Long(99L);
        mint(minted.box, VALUE, null, num("HOFF.box"), "OK",
                "M_J_field_HOFF.box", "Y_J_99");

        minted.decoded = new HashMap<String, String>();
        minted.decoded.put("expireAt", new String("1727"));
        mint(minted.decoded, ENTRY, "expireAt",
                parts(dec("DEC_LONG", "HOFF.expire", "1727")), "OK",
                "M_J_field_HOFF.expire");

        // An element's expression lands on the slot, so even an interned
        // literal element is minted: nothing JVM-wide is touched.
        minted.elements = new String[]{new String("7"), "lit"};
        mint(minted.elements, ELEMENT, Integer.valueOf(0),
                parts(dec("DEC_INT", "HOFF.elem", "7")), "OK",
                "M_I_field_HOFF.elem");
        mint(minted.elements, ELEMENT, Integer.valueOf(1),
                parts(dec("STR", "HOFF.lit", "lit")), "OK",
                "M_L'String'_field_HOFF.lit");

        minted.positional = new ArrayList<String>();
        minted.positional.add(new String("5"));
        mint(minted.positional, POSITION, Integer.valueOf(0),
                parts(dec("DEC_INT", "HOFF.pos", "5")), "OK",
                "M_I_field_HOFF.pos");

        // JVM-wide objects are refused, so the caller re-homes them.  This
        // JDK's Long.valueOf boxes afresh (it bypasses LongCache), so its
        // result is no JVM-wide object and is minted.
        Map<String, String> literals = new HashMap<String, String>();
        literals.put("k", "true");
        mint(Boolean.TRUE, VALUE, null, num("HOFF.shared"), "SHARED");
        mint("true", VALUE, null, parts(dec("BOOL", "HOFF.shared", "true")),
                "SHARED");
        mint(Character.valueOf('a'), VALUE, null, num("HOFF.shared"),
                "SHARED");
        mint(literals, ENTRY, "k", parts(dec("BOOL", "HOFF.shared", "true")),
                "SHARED");
        mint(Long.valueOf(5L), VALUE, null, num("HOFF.fresh"), "OK");

        // A container whose state already names the member.
        mint(built.map, ENTRY, "expireAt",
                parts(dec("STR", "HOFF.tracked", "1727")),
                "TRACKED_CONTAINER");
        // Templates that do not state the leaf, or are not the grammar.
        mint(new String("1727"), VALUE, null,
                parts(dec("DEC_LONG", "HOFF.bad", "1728")),
                "TEMPLATE_MISMATCH", "TEXT_MISMATCH");
        mint(new String("0017"), VALUE, null,
                parts(dec("DEC_LONG", "HOFF.bad", "0017")),
                "TEMPLATE_MISMATCH", "DECIMAL_NOT_CANONICAL");
        mint(new Long(1L), VALUE, null,
                parts(dec("DEC_LONG", "HOFF.bad", "1")), "TEMPLATE_MISMATCH",
                "NUMERIC_LEAF_TAKES_ONE_NUM_HOLE");
        mint(new String("x"), VALUE, null, num("HOFF.bad"),
                "TEMPLATE_MISMATCH", "NUM_HOLE_IN_STRING");
        mint(new String("x"), VALUE, null, "not json",
                "MALFORMED_TEMPLATE");
        mint(new String("1"), VALUE, null,
                parts(dec("DEC_LONG", "a b", "1")), "MALFORMED_TEMPLATE",
                "HOLE_LABEL");
        mint(minted.message, FIELD, field(Message.class, "absent"),
                parts(dec("STR", "HOFF.null", "")), "NULL_LEAF");

        // A mint never replaces an expression: an object or an element slot
        // that already carries one (a String a cache shares, an element a
        // mint wrote) is SHADOWED, a field whose location is versioned is
        // TRACKED; a JVM-wide holder (a box's own field, a box cache's
        // array) is SHARED.
        mint(minted.pair, VALUE, null, parts(dec("DEC_INT", "HOFF.again",
                "42"), literal(":"), dec("STR", "HOFF.again2", "abc")),
                "SHADOWED", "OBJECT_CARRIES_EXPRESSION",
                "\"landsOn\":\"OBJECT\"");
        mint(minted.elements, ELEMENT, Integer.valueOf(0),
                parts(dec("DEC_INT", "HOFF.again", "7")), "SHADOWED",
                "SLOT_CARRIES_EXPRESSION", "\"landsOn\":\"SLOT\"");
        mint(Thread.State.NEW, FIELD, field(Enum.class, "ordinal"),
                num("HOFF.enum"), "SHARED", "HOLDER_JVM_SHARED");
        mint(minted.message, FIELD, field(Message.class, "id"),
                num("HOFF.again"), "TRACKED_CONTAINER", "FIELD_TRACKED");
        mint(Boolean.TRUE, FIELD, field(Boolean.class, "value"),
                num("HOFF.shared"), "SHARED", "HOLDER_JVM_SHARED");
        Field cache = Class.forName("java.lang.Integer$IntegerCache")
                .getDeclaredField("cache");
        cache.setAccessible(true);
        mint(cache.get(null), ELEMENT, Integer.valueOf(200),
                num("HOFF.cache"), "SHARED", "HOLDER_JVM_SHARED");
        return minted;
    }

    /**
     * Only a value operand that carries its own expression opens a region's
     * gate: an owner a mint marked (a field of it symbolized), passed to a
     * modeled call, reads nothing, and paused bookkeeping opens nothing.
     */
    private static void onlyAValueOperandOpensTheGate(Minted minted) {
        require(System.startConcolicRegion("REGION.leaf-gate",
                "TASK.leaf-gate") == 0L, "region start rejected");
        Map<String, Object> holders = new HashMap<String, Object>();
        holders.put("k", minted.message);
        System.markConcolicBranch("LEAF.GATE.OWNER", 1);
        if (holders == null) throw new AssertionError("owner");
        String closed = System.getConcolicBranchEvents();
        require(closed.contains("\"events\":[]"),
                "an owner passed along opened the gate: " + closed);
        System.pauseConcolicPathCondition();
        boolean pausedRead = minted.pair.startsWith("42");
        System.resumeConcolicPathCondition();
        System.markConcolicBranch("LEAF.GATE.PAUSED", 1);
        if (!pausedRead) throw new AssertionError("paused read");
        String paused = System.getConcolicBranchEvents();
        require(paused.contains("\"events\":[]"),
                "paused code opened the gate: " + paused);
        boolean read = minted.pair.startsWith("42");
        System.markConcolicBranch("LEAF.GATE.VALUE", 1);
        if (!read) throw new AssertionError("value read");
        String opened = System.getConcolicBranchEvents();
        require(opened.contains("LEAF.GATE.VALUE"),
                "a value operand did not open the gate: " + opened);
        require(System.finishConcolicRegion().contains("\"complete\":true"),
                "region finish failed");
    }

    /**
     * The symbolizers never put an expression on a JVM-wide object: a box a
     * field holds, shared or fresh, carries its value on the field as a value
     * of its sort (what the unboxing reads) and stays clean; an enum constant
     * is neither entered nor shadowed; a shared root is refused.
     */
    private static void theSymbolizersLeaveJvmWideObjectsClean() {
        require(System.startConcolicRegion("REGION.leaf-shared",
                "TASK.leaf-shared") == 0L, "region start rejected");
        Flags selected = new Flags();
        Flags walked = new Flags();
        // The boxes as they were: a later read of the minted field carries
        // the field's value onto what it loads, which is no mint.
        Boolean selectedBox = selected.fresh;
        Boolean walkedBox = walked.fresh;
        System.symbolizeField(selected, "on", "FLAG.on");
        System.symbolizeField(selected, "fresh", "FLAG.fresh");
        System.symbolizeField(selected, "state", "FLAG.state");
        System.symbolize(walked, "FLAG.walk");
        System.symbolize(Boolean.TRUE, "FLAG.root");
        System.symbolize("leaf-shared-literal", "FLAG.literal");
        for (Object clean : new Object[]{Boolean.TRUE, "leaf-shared-literal",
                Thread.State.NEW, selectedBox, walkedBox}) {
            String expression = System.getSymbolicExpression(clean);
            require(!expression.contains("FLAG."),
                    "a mint landed on the object itself: " + expression);
        }
        boolean on = selected.on;
        System.markConcolicBranch("LEAF.SHARED.SELECTED", 1);
        if (!on) throw new AssertionError("selected");
        boolean fresh = selected.fresh;
        System.markConcolicBranch("LEAF.FRESH.SELECTED", 1);
        if (!fresh) throw new AssertionError("selected fresh");
        boolean walkedOn = walked.on;
        System.markConcolicBranch("LEAF.SHARED.WALKED", 1);
        if (!walkedOn) throw new AssertionError("walked");
        boolean walkedFresh = walked.fresh;
        System.markConcolicBranch("LEAF.FRESH.WALKED", 1);
        if (!walkedFresh) throw new AssertionError("walked fresh");
        String path = System.getConcolicPathConditionRange(0,
                Integer.MAX_VALUE);
        for (String symbol : new String[]{"M_Z_field_FLAG.on",
                "M_Z_field_FLAG.fresh", "Flags_on", "Flags_fresh"}) {
            require(path.contains(symbol), symbol + " not in " + path);
        }
        require(System.getSymbolicExpression(Boolean.TRUE)
                .contains("\"symbolic\":false"), "Boolean.TRUE has a shadow");
        require(System.getSymbolicExpression(Thread.State.NEW)
                .contains("\"jvmShared\":true"), "an enum is JVM-wide");
        require(System.getSymbolicExpression(selected)
                .contains("\"jvmShared\":false"), "an owner is not");
        require(System.finishConcolicRegion().contains("\"complete\":true"),
                "region finish failed");
    }

    /**
     * A fresh region whose first symbolic read is the decoded entry: the
     * String the mint left reaches Long.parseLong, which opens the region's
     * path-condition gate, so its decision names the hole.
     */
    private static void aRegionReadsAnEntryMintThroughParseLong(
            Minted minted) {
        require(System.startConcolicRegion("REGION.leaf-parse",
                "TASK.leaf-parse") == 0L, "region start rejected");
        long expire = Long.parseLong(minted.decoded.get("expireAt"));
        boolean late = expire > 1000L;
        System.markConcolicBranch("LEAF.ENTRY.PARSE", 1);
        if (!late) throw new AssertionError("expireAt");
        String path = System.getConcolicPathConditionRange(0,
                Integer.MAX_VALUE);
        require(path.contains("M_J_field_HOFF.expire"), path);
        require(path.contains("parseLong"), path);
        require(System.finishConcolicRegion().contains("\"complete\":true"),
                "region finish failed");
    }

    /** Each other mint reaches a decision of a later region. */
    private static void aRegionReadsTheOtherMints(Minted minted) {
        require(System.startConcolicRegion("REGION.leaf-read",
                "TASK.leaf-read") == 0L, "region start rejected");
        boolean idBig = minted.message.id > 40L;
        System.markConcolicBranch("LEAF.FIELD", 1);
        if (!idBig) throw new AssertionError("id");
        boolean named = minted.message.name.startsWith("1727");
        System.markConcolicBranch("LEAF.FIELD.STRING", 1);
        if (!named) throw new AssertionError("name");
        boolean boxBig = minted.box > 50L;
        System.markConcolicBranch("LEAF.VALUE.BOX", 1);
        if (!boxBig) throw new AssertionError("box");
        boolean elementBig = Integer.parseInt(minted.elements[0]) > 3;
        System.markConcolicBranch("LEAF.ELEMENT", 1);
        if (!elementBig) throw new AssertionError("element");
        boolean positioned = minted.positional.get(0).length() == 1;
        System.markConcolicBranch("LEAF.POSITION", 1);
        if (!positioned) throw new AssertionError("position");
        String path = System.getConcolicPathConditionRange(0,
                Integer.MAX_VALUE);
        for (String hole : new String[]{"M_J_field_HOFF.id",
                "M_J_field_HOFF.name", "M_J_field_HOFF.box",
                "M_I_field_HOFF.elem", "M_I_field_HOFF.pos"}) {
            require(path.contains(hole), hole + " not in " + path);
        }
        String pair = System.getSymbolicExpression(minted.pair);
        require(pair.contains("M_I_field_HOFF.int")
                && pair.contains("M_L'String'_field_HOFF.str"), pair);
        require(System.getTrackedLocationVersions(0L, 0)
                .contains("M_J_field_HOFF.id"),
                "a field mint published no version");
        require(System.finishConcolicRegion().contains("\"complete\":true"),
                "region finish failed");
    }

    // ---- rows -------------------------------------------------------------

    private static String mint(Object parent, int kind, Object slot,
                               String template, String status,
                               String... contains) {
        return expect(System.mintLeaf(parent, kind, slot, template), status,
                contains);
    }

    private static String expect(String answer, String status,
                                 String... contains) {
        require(answer.contains("\"status\":\"" + status + "\""),
                "expected " + status + ": " + answer);
        for (String text : contains) {
            require(answer.contains(text), "expected " + text + ": "
                    + answer);
        }
        return answer;
    }

    private static String num(String label) {
        return parts("{\"hole\":\"NUM\",\"label\":\"" + label + "\"}");
    }

    private static String dec(String kind, String label, String text) {
        return "{\"hole\":\"" + kind + "\",\"label\":\"" + label
                + "\",\"text\":\"" + text + "\"}";
    }

    private static String literal(String text) {
        return "{\"literal\":\"" + text + "\"}";
    }

    private static String parts(String... parts) {
        StringBuilder template = new StringBuilder("{\"parts\":[");
        for (int index = 0; index < parts.length; ++index) {
            if (index > 0) template.append(',');
            template.append(parts[index]);
        }
        return template.append("]}").toString();
    }

    private static Field field(Class<?> owner, String name)
            throws Exception {
        return owner.getDeclaredField(name);
    }

    private static int conditionCount(String range) {
        String key = "\"conditionCount\":";
        int at = range.indexOf(key);
        require(at >= 0, range);
        int end = at + key.length();
        while (end < range.length() && Character.isDigit(range.charAt(end))) {
            ++end;
        }
        return Integer.parseInt(range.substring(at + key.length(), end));
    }

    private static int count(String text, String needle) {
        int found = 0;
        for (int at = text.indexOf(needle); at >= 0;
             at = text.indexOf(needle, at + needle.length())) {
            ++found;
        }
        return found;
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}

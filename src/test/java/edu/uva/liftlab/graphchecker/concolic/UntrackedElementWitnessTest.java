package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

/**
 * A reference the VM stored into a container without naming it.
 *
 * <p>{@code P_L'<class>'_} is the placeholder for an operand oop no shadow
 * names.  It is not a root and it is not one object -- two distinct objects
 * render the same text -- so the codec hands the element to the host together
 * with the mutation that stored it, and the host may name it per mutation.</p>
 */
public class UntrackedElementWitnessTest {

    private static final String SNAPSHOT =
            "P_L'org/apache/hadoop/hdfs/server/namenode/snapshot/Snapshot'_";

    @Test
    public void anInsertedElementReachesTheHostWithItsMutation() {
        JsonObject state = relation("INDEXED", "STATE",
                symbol("MAP_STATE.v1." + digest('a')));
        JsonObject element = symbol(SNAPSHOT);
        JsonObject inserted = withArguments(
                relation("INDEXED", "INSERT", state), integer(0), element);

        ElementHost host = new ElementHost();
        ContainerSmtCodec.Term term = ContainerSmtCodec.term(inserted, host);

        assertNotNull(String.join(",", host.unsupported), term);
        assertEquals(1, host.mutations.size());
        assertSame("the mutation handed over is the INSERT node itself",
                inserted, host.mutations.get(0));
        assertSame(element, host.elements.get(0));
        assertTrue(term.text, term.text.contains("(indexed_insert "));
        assertTrue(term.text, term.text.contains("element__0"));
    }

    // --- fixture -----------------------------------------------------------

    private static String digest(char fill) {
        StringBuilder text = new StringBuilder();
        for (int index = 0; index < 64; index++) text.append(fill);
        return text.toString();
    }

    private static JsonObject relation(String shape, String operation,
                                       JsonObject receiver) {
        JsonObject relation = new JsonObject();
        relation.addProperty("_type", "ContainerRelation");
        relation.addProperty("shape", shape);
        relation.addProperty("operation", operation);
        relation.addProperty("_java_type", "L");
        if (receiver != null) relation.add("receiver", receiver);
        return relation;
    }

    private static JsonObject withArguments(JsonObject relation,
                                            JsonObject... arguments) {
        JsonArray rows = new JsonArray();
        for (JsonObject argument : arguments) rows.add(argument);
        relation.add("arguments", rows);
        return relation;
    }

    private static JsonObject symbol(String raw) {
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_exp", raw);
        symbol.addProperty("_java_type", raw.startsWith("P_L'")
                ? raw.substring(4, raw.indexOf('\'', 4)) : "L");
        return symbol;
    }

    private static JsonObject integer(int value) {
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_exp", "Y_I_" + value);
        symbol.addProperty("_java_type", "I");
        return symbol;
    }

    /** Names each unnamed element after the mutation that stored it. */
    private static final class ElementHost implements ContainerSmtCodec.Host {
        final List<String> unsupported = new ArrayList<>();
        final List<JsonObject> mutations = new ArrayList<>();
        final List<JsonElement> elements = new ArrayList<>();
        final IdentityHashMap<JsonObject, String> names =
                new IdentityHashMap<>();
        boolean nameElements = true;

        @Override
        public ContainerSmtCodec.Term state(JsonElement identity,
                                            ContainerSmtCodec.Sort shape) {
            return new ContainerSmtCodec.Term("container__state", shape);
        }

        @Override
        public ContainerSmtCodec.Term operand(
                JsonElement expression, ContainerSmtCodec.Sort expected) {
            if (ContainerSmtCodec.handles(expression)) {
                return ContainerSmtCodec.term(
                        expression.getAsJsonObject(), this);
            }
            if (expected == ContainerSmtCodec.Sort.INT) {
                String raw = expression.getAsJsonObject().get("_exp")
                        .getAsString();
                return new ContainerSmtCodec.Term(raw.substring(4),
                        ContainerSmtCodec.Sort.INT);
            }
            return new ContainerSmtCodec.Term("container__state", expected);
        }

        @Override
        public ContainerSmtCodec.Term box(JsonElement expression) {
            if (ContainerSmtCodec.handles(expression)) {
                ContainerSmtCodec.Term inner = ContainerSmtCodec.term(
                        expression.getAsJsonObject(), this);
                if (inner != null) return inner;
            }
            String raw = expression.getAsJsonObject().get("_exp")
                    .getAsString();
            return new ContainerSmtCodec.Term("(VRef " + raw + ")",
                    ContainerSmtCodec.Sort.VALUE);
        }

        @Override
        public ContainerSmtCodec.Term element(JsonElement expression,
                                              JsonObject mutation) {
            String raw = expression.getAsJsonObject().get("_exp")
                    .getAsString();
            if (!nameElements
                    || !VmExpressionIr.isUntrackedReferencePlaceholder(raw)) {
                return box(expression);
            }
            mutations.add(mutation);
            elements.add(expression);
            String name = names.get(mutation);
            if (name == null) {
                name = "element__" + names.size();
                names.put(mutation, name);
            }
            return new ContainerSmtCodec.Term("(VRef " + name + ")",
                    ContainerSmtCodec.Sort.VALUE);
        }

        @Override
        public ContainerSmtCodec.Term unbox(ContainerSmtCodec.Term value,
                                            String javaType) {
            return value;
        }

        @Override
        public void require(String predicate) {
        }

        @Override
        public ContainerSmtCodec.Term field(ContainerSmtCodec.Term owner,
                                            String ownerClass,
                                            int fieldOffset,
                                            String javaType) {
            unsupported.add("field:" + ownerClass);
            return null;
        }

        @Override
        public void unsupported(String reason) {
            unsupported.add(reason);
        }
    }
}

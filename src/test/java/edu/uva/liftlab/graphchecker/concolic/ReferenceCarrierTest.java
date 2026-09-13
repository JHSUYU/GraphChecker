package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Assume;
import org.junit.Test;

import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/**
 * A reference-typed shared location, end to end through the stages that had
 * no representation for one.
 *
 * <p>The motivating location is {@code BlockTokenSecretManager#currentKey}:
 * its writers install {@code BlockKey} objects that a root decides between,
 * and the HDFS-17899 bug3 wire key id is {@code currentKey.keyId} -- a field
 * of whichever object was installed, not of whichever object this execution
 * happened to walk.</p>
 */
public class ReferenceCarrierTest {

    private static final String BLOCK_KEY = "org.apache.hadoop.hdfs"
            + ".security.token.block.BlockKey";

    // ------------------------------------------------------- type contract

    @Test
    public void aPlainObjectReferenceIsAnIdentityCarrier() {
        assertTrue(JavaPrimitiveSmtSemantics.referenceIdentityCarrier(
                BLOCK_KEY));
        assertTrue(JavaPrimitiveSmtSemantics.referenceIdentityCarrier(
                "L" + BLOCK_KEY.replace('.', '/') + ";"));
    }

    /**
     * Everything the other representations already own stays theirs.
     *
     * <p>Two representations of one location is not a widening, it is an
     * ambiguity: the bounded container model answers reads of a collection,
     * the scalar contract answers a String or a boxed primitive, and an
     * array is state with its own element locations.  {@code Object} names
     * no class a dependent read could resolve a field of, and is the type a
     * container most often hides behind.</p>
     */
    @Test
    public void everyOtherShapeKeepsItsOwnRepresentation() {
        assertFalse(JavaPrimitiveSmtSemantics.referenceIdentityCarrier("int"));
        assertFalse(JavaPrimitiveSmtSemantics.referenceIdentityCarrier("J"));
        assertFalse(JavaPrimitiveSmtSemantics.referenceIdentityCarrier(
                "java.lang.String"));
        assertFalse(JavaPrimitiveSmtSemantics.referenceIdentityCarrier(
                "java.lang.Integer"));
        assertFalse(JavaPrimitiveSmtSemantics.referenceIdentityCarrier(
                "java.lang.Object"));
        assertFalse(JavaPrimitiveSmtSemantics.referenceIdentityCarrier(
                "java.util.List"));
        assertFalse(JavaPrimitiveSmtSemantics.referenceIdentityCarrier(
                "java.util.Map"));
        assertFalse(JavaPrimitiveSmtSemantics.referenceIdentityCarrier(
                BLOCK_KEY + "[]"));
        assertFalse(JavaPrimitiveSmtSemantics.referenceIdentityCarrier(""));
        assertFalse(JavaPrimitiveSmtSemantics.referenceIdentityCarrier(null));
    }

    // ------------------------------------------------- the VM payload path

    /**
     * The observed pair reaches the host that can use it.
     *
     * <p>A host with no representation for an owner choice keeps the plain
     * projection, so the extra facts are carried on a second entry point
     * rather than by changing the one every lowering shares.</p>
     */
    @Test
    public void theObservedPairReachesTheHost() {
        RecordingHost host = new RecordingHost();
        ContainerSmtCodec.field(fieldAccess(true), host);

        assertEquals("owner", host.owner);
        assertEquals("witness", host.concreteOwner);
        assertEquals("23", host.concreteValue);
        assertEquals(BLOCK_KEY.replace('.', '/'), host.ownerClass);
        assertEquals(16, host.fieldOffset);
    }

    /**
     * A read with no owner choice is exactly the read it always was.
     *
     * <p>The VM writes both members together or neither, so a half-present
     * pair is a payload this codec does not recognise; guessing the missing
     * half would invent an observation.</p>
     */
    @Test
    public void aReadWithoutAnOwnerChoiceIsUnchanged() {
        RecordingHost plain = new RecordingHost();
        ContainerSmtCodec.field(fieldAccess(false), plain);
        assertNull(plain.concreteOwner);
        assertNull(plain.concreteValue);

        JsonObject half = fieldAccess(true);
        half.remove("concreteValue");
        RecordingHost partial = new RecordingHost();
        ContainerSmtCodec.field(half, partial);
        assertNull(partial.concreteOwner);
    }

    // ---------------------------------------------------- the bound value

    /**
     * The shape of the value a dependent reference read lowers to.
     *
     * <p>Outermost is the object this execution read from; then every
     * identity whose own field is versioned; innermost the uninterpreted
     * projection, which is what an identity with neither is worth.</p>
     */
    @Test
    public void theBoundValueIsIndexedByTheOwnerIdentity() {
        List<String[]> routes = new ArrayList<>();
        routes.add(new String[]{"installed_ref", "rf_value__installed"});

        assertEquals("(ite (= owner observed_ref) 23"
                        + " (ite (= owner installed_ref) rf_value__installed"
                        + " (container_field__x owner)))",
                ConcolicSmtComposer.referenceFieldBinding("owner",
                        "observed_ref", "23", "(container_field__x owner)",
                        routes));
    }

    /** With nothing else known, the read is the free projection. */
    @Test
    public void anUnknownOwnerIsANamedFreedomAndNotAZero() {
        String binding = ConcolicSmtComposer.referenceFieldBinding("owner",
                "observed_ref", "23", "(container_field__x owner)",
                Collections.<String[]>emptyList());

        assertEquals("(ite (= owner observed_ref) 23"
                + " (container_field__x owner))", binding);
        assertFalse(binding, binding.contains(" 0 "));
    }

    /**
     * What the binding is worth once the identities are separate, and what
     * it is worth when nothing says they are.
     *
     * <p>Given that the owner is one of the two identities the writers
     * installed, that those two are different objects, and that this
     * execution read 23 out of the one it walked, selecting the
     * <em>other</em> writer's arm cannot also yield 23 for free -- it yields
     * that object's own versioned key id, which is precisely the inference
     * an uninterpreted projection of an unconstrained owner could not
     * make.</p>
     *
     * <p>The separation is a <em>premise</em> here, never an axiom the
     * composer asserts.  It briefly did assert one, over every {@code REF}
     * witness of a replay <em>group</em> -- dozens of executions -- and
     * HDFS-17899 bug3 then had no model at all, in any polarity, with those
     * rows as its entire unsat core.  Without the premise the arms are
     * merely ordered, so the inner one may collapse onto the observed value:
     * an over-approximation, which admits a model rather than refuting one.
     * The last case pins that, so a future sharpening has to state which
     * direction it moves in.</p>
     */
    @Test
    public void theBindingSeparatesTheWritersItArmsOver() throws Exception {
        Assume.assumeTrue(z3Available());
        String model = "(set-logic ALL)\n"
                + "(declare-sort Ref 0)\n"
                + "(declare-const owner Ref)\n"
                + "(declare-const observed_ref Ref)\n"
                + "(declare-const installed_ref Ref)\n"
                + "(declare-const installed_key_id Int)\n"
                + "(declare-const read Int)\n"
                + "(declare-fun container_field__x (Ref) Int)\n"
                + "(assert (distinct observed_ref installed_ref))\n"
                + "(assert (or (= owner observed_ref)"
                + " (= owner installed_ref)))\n"
                + "(assert (= read "
                + ConcolicSmtComposer.referenceFieldBinding("owner",
                        "observed_ref", "23", "(container_field__x owner)",
                        Collections.singletonList(new String[]{
                                "installed_ref", "installed_key_id"}))
                + "))\n";

        // Taking the installed writer's arm reads that object's key id.
        assertEquals("unsat", solve(model
                + "(assert (= owner installed_ref))\n"
                + "(assert (not (= read installed_key_id)))\n"));
        // And the arm the run did take is pinned to what it observed.
        assertEquals("unsat", solve(model
                + "(assert (= owner observed_ref))\n"
                + "(assert (not (= read 23)))\n"));
        // With nothing separating the two arms they may be one object, and
        // the installed writer's key id collapses onto the observed value.
        assertEquals("sat", solve(model.replace(
                        "(assert (distinct observed_ref installed_ref))\n", "")
                + "(assert (= owner installed_ref))\n"
                + "(assert (not (= installed_key_id 23)))\n"
                + "(assert (= read 23))\n"));
    }

    /**
     * The composed formula states no object-identity axiom of its own.
     *
     * <p>A structural witness is scoped by the replay group, so a
     * {@code distinct} over the witnesses of one scope says that dozens of
     * executions allocated dozens of different objects -- which no recording
     * claims, and which refuted HDFS-17899 bug3 outright.  The binding
     * therefore carries the arms and nothing else, and the composer emits no
     * identity row anywhere.</p>
     */
    @Test
    public void theComposerAssertsNoObjectIdentityAxiom() throws Exception {
        String binding = ConcolicSmtComposer.referenceFieldBinding("owner",
                "observed_ref", "23", "(container_field__x owner)",
                Collections.singletonList(new String[]{
                        "installed_ref", "installed_key_id"}));

        assertFalse(binding, binding.contains("distinct"));

        String source = new String(Files.readAllBytes(Paths.get(
                        "src/main/java/edu/uva/liftlab/graphchecker"
                                + "/concolic/ConcolicSmtComposer.java")),
                StandardCharsets.UTF_8);
        assertFalse("reference_identity_distinct is unsound over a replay"
                        + " group and must not come back unexamined",
                source.contains("reference_identity_distinct"));
    }

    // ------------------------------------------------------------- helpers

    @Test
    public void aLocationKeyNamesItsSlot() {
        assertEquals(24, SharedStateEvidence.locationSlotOf(
                "INSTANCE_FIELD/7#24"));
        assertEquals(7L, SharedStateEvidence.locationOwnerOf(
                "INSTANCE_FIELD/7#24"));
        assertEquals(-1, SharedStateEvidence.locationSlotOf("nonsense"));
        assertEquals(-1, SharedStateEvidence.locationSlotOf(
                "INSTANCE_FIELD/7#x"));
    }

    private static JsonObject fieldAccess(boolean observed) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "FieldAccessExpression");
        node.addProperty("_java_type", "I");
        node.addProperty("ownerClass", BLOCK_KEY.replace('.', '/'));
        node.addProperty("fieldOffset", 16);
        node.add("owner", named("owner"));
        if (observed) {
            node.add("concreteOwner", named("witness"));
            node.add("concreteValue", named("23"));
        }
        return node;
    }

    private static JsonObject named(String text) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "SymbolExpression");
        node.addProperty("_exp", text);
        return node;
    }

    /** A host that answers every operand by its recorded name. */
    private static final class RecordingHost
            implements ContainerSmtCodec.Host {
        private String owner;
        private String ownerClass;
        private int fieldOffset = -1;
        private String concreteOwner;
        private String concreteValue;

        @Override
        public ContainerSmtCodec.Term state(JsonElement identity,
                                            ContainerSmtCodec.Sort shape) {
            return null;
        }

        @Override
        public ContainerSmtCodec.Term operand(JsonElement expression,
                                              ContainerSmtCodec.Sort expected) {
            String text = expression.getAsJsonObject().get("_exp")
                    .getAsString();
            return new ContainerSmtCodec.Term(text,
                    "23".equals(text) ? ContainerSmtCodec.Sort.INT
                            : ContainerSmtCodec.Sort.REF);
        }

        @Override
        public ContainerSmtCodec.Term box(JsonElement expression) {
            return null;
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
            this.owner = owner == null ? null : owner.text;
            this.ownerClass = ownerClass;
            this.fieldOffset = fieldOffset;
            return new ContainerSmtCodec.Term("(field " + this.owner + ")",
                    ContainerSmtCodec.Sort.INT);
        }

        @Override
        public ContainerSmtCodec.Term field(ContainerSmtCodec.Term owner,
                                            String ownerClass,
                                            int fieldOffset,
                                            String javaType,
                                            ContainerSmtCodec.Term concrete,
                                            ContainerSmtCodec.Term value) {
            this.concreteOwner = concrete == null ? null : concrete.text;
            this.concreteValue = value == null ? null : value.text;
            return field(owner, ownerClass, fieldOffset, javaType);
        }

        @Override
        public void unsupported(String reason) {
            throw new AssertionError(reason);
        }
    }

    private static String solve(String input) throws Exception {
        Process process = new ProcessBuilder("z3", "-in", "-smt2").start();
        try (OutputStream stream = process.getOutputStream()) {
            stream.write((input + "(check-sat)\n")
                    .getBytes(StandardCharsets.UTF_8));
        }
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        try (InputStream stream = process.getInputStream()) {
            byte[] chunk = new byte[256];
            for (int count; (count = stream.read(chunk)) >= 0; ) {
                output.write(chunk, 0, count);
            }
        }
        assertEquals(0, process.waitFor());
        return new String(output.toByteArray(), StandardCharsets.UTF_8)
                .trim();
    }

    private static boolean z3Available() {
        try {
            Process process = new ProcessBuilder("z3", "--version")
                    .redirectErrorStream(true).start();
            process.getInputStream().close();
            return process.waitFor() == 0;
        } catch (Exception unavailable) {
            return false;
        }
    }
}

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

    // ---------------------------------------------------- the bound value

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

    // ------------------------------------------------------------- helpers

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

    /**
     * Whether z3 can be run at all.
     *
     * <p>This used to close z3's stdout before waiting on it, so z3 died on
     * EPIPE, the probe read a non-zero exit as "no z3", and the one test that
     * proves the reference binding really separates its writers skipped on
     * every host that had z3 installed.  Let the process write and exit.</p>
     */
    private static boolean z3Available() {
        try {
            Process process = new ProcessBuilder("z3", "-version").start();
            return process.waitFor() == 0;
        } catch (Exception unavailable) {
            return false;
        }
    }
}

package edu.uva.liftlab.graphchecker.runtime;

import org.junit.Test;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * The plant-run agent's rewrite: after every invoke of a named callee, the
 * plant's call for the invoke's return type (a reference through Object and
 * a cast back), nothing after an unnamed or void one; the rewritten class
 * verifies and, with no plant, returns what it returned.  And the JVM
 * spelling of a Soot signature the agent matches invokes by.
 */
public class PlantAgentTest {
    private static final String FIXTURE =
            "edu.uva.liftlab.graphchecker.runtime.PlantAgentFixture";

    @Test
    public void namedInvokesHandTheirReturnsToThePlant() throws Exception {
        Set<String> callees = new LinkedHashSet<String>(Arrays.asList(
                "java/lang/System.currentTimeMillis ()J",
                "java/lang/Integer.parseInt (Ljava/lang/String;)I",
                "java/lang/String.split (Ljava/lang/String;)[Ljava/lang/String;",
                "java/lang/String.valueOf (Ljava/lang/Object;)Ljava/lang/String;",
                "java/lang/System.gc ()V"));
        byte[] rewritten = PlantAgent.rewrite(bytes(), callees);
        final List<String> after = new ArrayList<String>();
        new ClassReader(rewritten).accept(new ClassVisitor(Opcodes.ASM5) {
            @Override
            public MethodVisitor visitMethod(int access, String name,
                                             String descriptor,
                                             String signature,
                                             String[] exceptions) {
                return new MethodVisitor(Opcodes.ASM5) {
                    @Override
                    public void visitMethodInsn(int opcode, String owner,
                                                String called, String desc,
                                                boolean onInterface) {
                        if (owner.endsWith("RecordingPlant")) {
                            after.add(called + desc);
                        }
                    }

                    @Override
                    public void visitTypeInsn(int opcode, String type) {
                        if (opcode == Opcodes.CHECKCAST) after.add(type);
                    }
                };
            }
        }, 0);
        assertEquals(Arrays.asList("returned(J)J", "returned(I)I",
                "returned(Ljava/lang/Object;)Ljava/lang/Object;",
                "[Ljava/lang/String;",
                "returned(Ljava/lang/Object;)Ljava/lang/Object;",
                "java/lang/String"), after);
        Class<?> loaded = new ClassLoader(getClass().getClassLoader()) {
            @Override
            protected Class<?> loadClass(String name, boolean resolve)
                    throws ClassNotFoundException {
                if (!FIXTURE.equals(name)) {
                    return super.loadClass(name, resolve);
                }
                synchronized (getClassLoadingLock(name)) {
                    Class<?> defined = findLoadedClass(name);
                    return defined != null ? defined : defineClass(name,
                            rewritten, 0, rewritten.length);
                }
            }
        }.loadClass(FIXTURE);
        long before = System.currentTimeMillis();
        long clock = (Long) method(loaded, "clock", boolean.class)
                .invoke(null, true);
        assertTrue(clock > before);
        assertEquals(12, method(loaded, "parsed", String.class)
                .invoke(null, "12"));
        assertArrayEquals(new String[]{"a", "b"}, (String[]) method(loaded,
                "split", String.class).invoke(null, "a,b"));
        assertEquals("5", method(loaded, "named", Object.class)
                .invoke(null, 5));
        method(loaded, "collected").invoke(null);
    }

    @Test
    public void aSootSignatureInTheJvmsSpelling() {
        Object[][] signatures = {
                {"<java.lang.System: long nanoTime()>",
                        "java/lang/System nanoTime ()J"},
                {"<a.B$C: java.lang.String[] f(int,java.util.List)>",
                        "a/B$C f (ILjava/util/List;)[Ljava/lang/String;"},
                {"<org.apache.hadoop.util.Timer: long now()>",
                        "org/apache/hadoop/util/Timer now ()J"},
                {"a.B#f", null},
                {"", null},
        };
        for (Object[] signature : signatures) {
            String[] parsed = JvmSignature.parse((String) signature[0]);
            assertEquals(Arrays.toString(signature), signature[1],
                    parsed == null ? null : String.join(" ", parsed));
        }
    }

    private static Method method(Class<?> owner, String name,
                                 Class<?>... parameters) throws Exception {
        return owner.getMethod(name, parameters);
    }

    private static byte[] bytes() throws IOException {
        try (InputStream in = PlantAgentTest.class.getResourceAsStream(
                "PlantAgentFixture.class")) {
            ByteArrayOutputStream out = new ByteArrayOutputStream();
            byte[] buffer = new byte[8192];
            for (int read; (read = in.read(buffer)) > 0; ) {
                out.write(buffer, 0, read);
            }
            return out.toByteArray();
        }
    }
}

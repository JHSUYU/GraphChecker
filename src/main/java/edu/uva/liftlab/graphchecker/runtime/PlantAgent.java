package edu.uva.liftlab.graphchecker.runtime;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;

import java.lang.instrument.ClassFileTransformer;
import java.lang.instrument.Instrumentation;
import java.nio.file.Paths;
import java.security.ProtectionDomain;
import java.util.Map;
import java.util.Set;

/**
 * The plant-run agent (PIPELINE §10b): loaded only by a native
 * reproduction's JVM ({@code -javaagent}, {@code execute.sh} with {@code
 * CAUSYNTH_PLANT}), it hands {@link RecordingPlant} the value every call the
 * plant reads returns -- a clock's reading, a configuration getter's or an
 * accessor's value, a port's call-return capture -- so the planted world's
 * value takes its place.
 *
 * <p>In each caller class the plant names, as it loads, every invoke of a
 * callee the plant names there is followed by one call, {@code
 * RecordingPlant.returned(T)T} for the call's JVM return type T (a reference
 * through {@code Object} and back by a cast).  Which call it is the
 * recording weave's own call-site context states at run time, by site and
 * callee, so no unit index is mapped to a bytecode offset; an invoke the weave
 * wraps in no context matches no row.  Nothing else changes: the woven classes
 * on disk, SEED's artifacts and the recording are the same, and a JVM without
 * a plant loads no agent.  The rewrite keeps the operand stack's types (one
 * value in, the same type out), so no frame is recomputed and no class is
 * loaded to do it; it speaks the oldest ASM API that reads Java 8 classes, as
 * a tree may put an older ASM ahead of the engine's on the class path.</p>
 */
public final class PlantAgent {
    private static final String PLANT =
            "edu/uva/liftlab/graphchecker/runtime/RecordingPlant";

    private PlantAgent() {
    }

    public static void premain(String arguments, Instrumentation instrumentation)
            throws Exception {
        String file = RecordingPlant.file();
        if (file.isEmpty()) return;
        Map<String, Set<String>> intercepted = RecordingPlant.interceptions(
                RecordingPlant.read(Paths.get(file)));
        if (intercepted.isEmpty()) return;
        instrumentation.addTransformer(new Rewriter(intercepted));
    }

    /** Rewrites the caller classes the plant names as they load. */
    static final class Rewriter implements ClassFileTransformer {
        private final Map<String, Set<String>> intercepted;

        Rewriter(Map<String, Set<String>> intercepted) {
            this.intercepted = intercepted;
        }

        @Override
        public byte[] transform(ClassLoader loader, String className,
                                Class<?> redefined, ProtectionDomain domain,
                                byte[] bytes) {
            Set<String> callees = className == null ? null
                    : intercepted.get(className);
            if (callees == null) return null;
            try {
                return rewrite(bytes, callees);
            } catch (RuntimeException unwritable) {
                // The class loads as woven: its calls answer the host, and
                // every row it would have planted says it was not reached.
                EngineConsole.println("Causynth plant agent: " + className
                        + " was not rewritten: " + unwritable);
                return null;
            }
        }
    }

    /** One class with every invoke of {@code callees} handed to the plant. */
    static byte[] rewrite(byte[] bytes, final Set<String> callees) {
        ClassReader reader = new ClassReader(bytes);
        ClassWriter writer = new ClassWriter(reader, ClassWriter.COMPUTE_MAXS);
        reader.accept(new ClassVisitor(Opcodes.ASM5, writer) {
            @Override
            public MethodVisitor visitMethod(int access, String name,
                                             String descriptor,
                                             String signature,
                                             String[] exceptions) {
                MethodVisitor method = super.visitMethod(access, name,
                        descriptor, signature, exceptions);
                return new MethodVisitor(Opcodes.ASM5, method) {
                    @Override
                    public void visitMethodInsn(int opcode, String owner,
                                                String called, String desc,
                                                boolean onInterface) {
                        super.visitMethodInsn(opcode, owner, called, desc,
                                onInterface);
                        if (callees.contains(owner + "." + called + " "
                                + desc)) {
                            handOff(mv, Type.getReturnType(desc));
                        }
                    }
                };
            }
        }, 0);
        return writer.toByteArray();
    }

    /** The plant's call after one invoke returning {@code type}. */
    static void handOff(MethodVisitor method, Type type) {
        switch (type.getSort()) {
            case Type.VOID:
                return;
            case Type.LONG:
                method.visitMethodInsn(Opcodes.INVOKESTATIC, PLANT,
                        "returned", "(J)J", false);
                return;
            case Type.BOOLEAN:
                method.visitMethodInsn(Opcodes.INVOKESTATIC, PLANT,
                        "returned", "(Z)Z", false);
                return;
            case Type.INT:
            case Type.SHORT:
            case Type.BYTE:
            case Type.CHAR:
                method.visitMethodInsn(Opcodes.INVOKESTATIC, PLANT,
                        "returned", "(I)I", false);
                return;
            case Type.FLOAT:
                method.visitMethodInsn(Opcodes.INVOKESTATIC, PLANT,
                        "returned", "(F)F", false);
                return;
            case Type.DOUBLE:
                method.visitMethodInsn(Opcodes.INVOKESTATIC, PLANT,
                        "returned", "(D)D", false);
                return;
            default:
                method.visitMethodInsn(Opcodes.INVOKESTATIC, PLANT,
                        "returned", "(Ljava/lang/Object;)Ljava/lang/Object;",
                        false);
                method.visitTypeInsn(Opcodes.CHECKCAST,
                        type.getSort() == Type.ARRAY ? type.getDescriptor()
                                : type.getInternalName());
        }
    }
}

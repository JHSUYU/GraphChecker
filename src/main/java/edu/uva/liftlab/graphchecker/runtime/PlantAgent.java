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
                EngineConsole.println("Causynth plant agent: " + className
                        + " was not rewritten: " + unwritable);
                return null;
            }
        }
    }

    static byte[] rewrite(byte[] bytes, final Set<String> callees) {
        ClassReader reader = new ClassReader(bytes);
        ClassWriter writer = new ClassWriter(reader, ClassWriter.COMPUTE_MAXS);
        reader.accept(new ClassVisitor(Opcodes.ASM5, writer) {
            @Override
            public MethodVisitor visitMethod(int access, final String name,
                                             final String descriptor,
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

                    @Override
                    public void visitFieldInsn(int opcode, String owner,
                                               String field, String desc) {
                        String read = "<" + owner.replace('/', '.') + ": "
                                + Type.getType(desc).getClassName() + " "
                                + field + ">";
                        if (opcode == Opcodes.GETFIELD && callees.contains(
                                name + descriptor + " " + read)) {
                            super.visitInsn(Opcodes.DUP);
                            super.visitLdcInsn(read);
                            super.visitMethodInsn(Opcodes.INVOKESTATIC, PLANT,
                                    "fieldRead", "(Ljava/lang/Object;"
                                            + "Ljava/lang/String;)V", false);
                        }
                        super.visitFieldInsn(opcode, owner, field, desc);
                    }
                };
            }
        }, 0);
        return writer.toByteArray();
    }

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

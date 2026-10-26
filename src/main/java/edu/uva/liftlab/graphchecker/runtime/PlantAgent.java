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
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
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
        final Map<String, List<String>> reads =
                new HashMap<String, List<String>>();
        reader.accept(new ClassVisitor(Opcodes.ASM5) {
            @Override
            public MethodVisitor visitMethod(int access, String name,
                                             String descriptor,
                                             String signature,
                                             String[] exceptions) {
                final List<String> fields = new ArrayList<String>();
                reads.put(name + descriptor, fields);
                return new MethodVisitor(Opcodes.ASM5) {
                    @Override
                    public void visitFieldInsn(int opcode, String owner,
                                               String field, String desc) {
                        if (opcode == Opcodes.GETFIELD) {
                            fields.add(field(owner, field, desc));
                        }
                    }
                };
            }
        }, 0);
        ClassWriter writer = new ClassWriter(reader, ClassWriter.COMPUTE_MAXS);
        reader.accept(new ClassVisitor(Opcodes.ASM5, writer) {
            @Override
            public MethodVisitor visitMethod(int access, String name,
                                             String descriptor,
                                             String signature,
                                             String[] exceptions) {
                MethodVisitor method = super.visitMethod(access, name,
                        descriptor, signature, exceptions);
                final Map<String, Boolean> planned = planned(
                        name + descriptor, reads.get(name + descriptor),
                        callees);
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
                        String read = field(owner, field, desc);
                        for (Map.Entry<String, Boolean> planted
                                : planned.entrySet()) {
                            if (opcode != Opcodes.GETFIELD
                                    || !sameField(planted.getKey(), read)) {
                                continue;
                            }
                            if (planted.getValue()) {
                                super.visitInsn(Opcodes.DUP);
                            }
                            super.visitLdcInsn(planted.getKey());
                            super.visitMethodInsn(Opcodes.INVOKESTATIC, PLANT,
                                    planted.getValue() ? "fieldRead"
                                            : "fieldUnwritten",
                                    planted.getValue() ? "(Ljava/lang/Object;"
                                            + "Ljava/lang/String;)V"
                                            : "(Ljava/lang/String;)V", false);
                        }
                        super.visitFieldInsn(opcode, owner, field, desc);
                    }
                };
            }
        }, 0);
        return writer.toByteArray();
    }

    static Map<String, Boolean> planned(String method, List<String> reads,
                                        Set<String> callees) {
        Map<String, Integer> sites = new LinkedHashMap<String, Integer>();
        for (String key : callees) {
            if (key.startsWith(method + " <")) {
                sites.merge(key.substring(method.length() + 1,
                        key.indexOf("> ", method.length()) + 1), 1,
                        Integer::sum);
            }
        }
        Map<String, Boolean> planned = new LinkedHashMap<String, Boolean>();
        for (Map.Entry<String, Integer> field : sites.entrySet()) {
            int found = 0;
            int exact = 0;
            for (String read : reads) {
                if (sameField(field.getKey(), read)) found++;
                if (field.getKey().equals(read)) exact++;
            }
            planned.put(field.getKey(), found == field.getValue()
                    && exact == found);
        }
        return planned;
    }

    private static String field(String owner, String name, String desc) {
        return "<" + owner.replace('/', '.') + ": "
                + Type.getType(desc).getClassName() + " " + name + ">";
    }

    private static boolean sameField(String planned, String read) {
        return planned.substring(planned.indexOf(": ")).equals(
                read.substring(read.indexOf(": ")));
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

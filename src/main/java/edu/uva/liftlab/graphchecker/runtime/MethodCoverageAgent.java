package edu.uva.liftlab.graphchecker.runtime;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.commons.AdviceAdapter;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.instrument.ClassFileTransformer;
import java.lang.instrument.IllegalClassFormatException;
import java.lang.instrument.Instrumentation;
import java.security.ProtectionDomain;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

public final class MethodCoverageAgent {
    private static final Set<String> SEEN = Collections.newSetFromMap(new ConcurrentHashMap<String, Boolean>());
    private static final Object LOCK = new Object();
    private static volatile File outputFile;
    private static volatile List<String> includePrefixes = Collections.singletonList("org/apache/hadoop/");

    private MethodCoverageAgent() {
    }

    public static void premain(String agentArgs, Instrumentation instrumentation) {
        configure(agentArgs);
        instrumentation.addTransformer(new Transformer(), false);
    }

    public static void record(String className, String methodName, String descriptor) {
        File file = outputFile;
        if (file == null) {
            return;
        }
        String key = className + "#" + methodName + descriptor;
        if (!SEEN.add(key)) {
            return;
        }
        synchronized (LOCK) {
            FileWriter writer = null;
            try {
                File parent = file.getParentFile();
                if (parent != null && !parent.exists()) {
                    parent.mkdirs();
                }
                writer = new FileWriter(file, true);
                writer.write("{\"event\":\"METHOD_COVERED\",\"className\":\"");
                writer.write(escape(className));
                writer.write("\",\"methodName\":\"");
                writer.write(escape(methodName));
                writer.write("\",\"descriptor\":\"");
                writer.write(escape(descriptor));
                writer.write("\",\"method\":\"");
                writer.write(escape(className + "." + methodName));
                writer.write("\"}\n");
            } catch (IOException ignored) {
            } finally {
                if (writer != null) {
                    try {
                        writer.close();
                    } catch (IOException ignored) {
                    }
                }
            }
        }
    }

    private static void configure(String agentArgs) {
        if (agentArgs == null) {
            return;
        }
        for (String part : agentArgs.split(";")) {
            int index = part.indexOf('=');
            if (index <= 0) {
                continue;
            }
            String key = part.substring(0, index).trim();
            String value = part.substring(index + 1).trim();
            if ("output".equals(key)) {
                outputFile = new File(value);
            } else if ("include".equals(key)) {
                List<String> prefixes = new ArrayList<>();
                for (String prefix : value.split(",")) {
                    String trimmed = prefix.trim();
                    if (!trimmed.isEmpty()) {
                        prefixes.add(trimmed.replace('.', '/'));
                    }
                }
                if (!prefixes.isEmpty()) {
                    includePrefixes = prefixes;
                }
            }
        }
    }

    private static boolean shouldInstrument(String internalName) {
        if (internalName == null
                || internalName.startsWith("edu/uva/liftlab/graphchecker/")
                || internalName.startsWith("org/objectweb/asm/")) {
            return false;
        }
        for (String prefix : includePrefixes) {
            if (internalName.startsWith(prefix)) {
                return true;
            }
        }
        return false;
    }

    private static String escape(String value) {
        if (value == null) {
            return "";
        }
        return value.replace("\\", "\\\\").replace("\"", "\\\"");
    }

    private static final class Transformer implements ClassFileTransformer {
        @Override
        public byte[] transform(ClassLoader loader, String className, Class<?> classBeingRedefined,
                                ProtectionDomain protectionDomain, byte[] classfileBuffer)
                throws IllegalClassFormatException {
            if (!shouldInstrument(className)) {
                return null;
            }
            try {
                ClassReader reader = new ClassReader(classfileBuffer);
                ClassWriter writer = new ClassWriter(reader, ClassWriter.COMPUTE_MAXS);
                reader.accept(new CoverageClassVisitor(writer, className), ClassReader.EXPAND_FRAMES);
                return writer.toByteArray();
            } catch (Throwable ignored) {
                return null;
            }
        }
    }

    private static final class CoverageClassVisitor extends ClassVisitor {
        private final String className;

        private CoverageClassVisitor(ClassVisitor visitor, String className) {
            super(Opcodes.ASM9, visitor);
            this.className = className;
        }

        @Override
        public MethodVisitor visitMethod(int access, String name, String descriptor,
                                         String signature, String[] exceptions) {
            MethodVisitor visitor = super.visitMethod(access, name, descriptor, signature, exceptions);
            if (visitor == null
                    || (access & (Opcodes.ACC_ABSTRACT | Opcodes.ACC_NATIVE)) != 0
                    || "<clinit>".equals(name)) {
                return visitor;
            }
            return new AdviceAdapter(Opcodes.ASM9, visitor, access, name, descriptor) {
                @Override
                protected void onMethodEnter() {
                    visitLdcInsn(className.replace('/', '.'));
                    visitLdcInsn(name);
                    visitLdcInsn(descriptor);
                    visitMethodInsn(Opcodes.INVOKESTATIC,
                            "edu/uva/liftlab/graphchecker/runtime/MethodCoverageAgent",
                            "record",
                            "(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)V",
                            false);
                }
            };
        }
    }
}

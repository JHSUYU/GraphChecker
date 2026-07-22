package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.TypeReference;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.AnnotationNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.LineNumberNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeAnnotationNode;
import org.objectweb.asm.tree.TypeInsnNode;
import soot.ArrayType;
import soot.BooleanType;
import soot.ByteType;
import soot.CharType;
import soot.DoubleType;
import soot.FloatType;
import soot.IntType;
import soot.LongType;
import soot.RefType;
import soot.Scene;
import soot.ShortType;
import soot.SootClass;
import soot.SootMethod;
import soot.VoidType;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Enumeration;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/** Finds exact {@link CausynthExceptionTarget} NEW instructions in inputs. */
final class ExceptionTargetAnnotationScanner {
    private static final String ANNOTATION_DESCRIPTOR =
            Type.getDescriptor(CausynthExceptionTarget.class);

    private ExceptionTargetAnnotationScanner() {
    }

    static ExceptionTargetSite select(List<String> inputs,
                                      String requestedId)
            throws IOException {
        List<ExceptionTargetSite> scanned = scan(inputs);
        List<ExceptionTargetSite> matches = new ArrayList<>();
        String wanted = requestedId == null ? "" : requestedId.trim();
        for (ExceptionTargetSite site : scanned) {
            if (wanted.isEmpty() || wanted.equals(site.id)) {
                matches.add(site);
            }
        }
        if (matches.isEmpty()) {
            throw new IOException(wanted.isEmpty()
                    ? "No @CausynthExceptionTarget exists in the analyzed "
                    + "class inputs"
                    : "No @CausynthExceptionTarget(\"" + wanted
                    + "\") exists in the analyzed class inputs");
        }
        if (matches.size() != 1) {
            List<String> identities = matches.stream()
                    .map(site -> (site.id.isEmpty() ? "<unnamed>" : site.id)
                            + "=" + site.stableIdentity())
                    .sorted()
                    .collect(Collectors.toList());
            throw new IOException("Expected exactly one annotated exception "
                    + "target"
                    + (wanted.isEmpty() ? "" : " named " + wanted)
                    + ", found " + matches.size() + ": " + identities);
        }
        ExceptionTargetSite unresolved = matches.get(0);
        String signature = resolveMethodSignature(unresolved);
        return new ExceptionTargetSite(unresolved.id,
                unresolved.className, unresolved.methodName,
                unresolved.methodDescriptor, signature,
                unresolved.exceptionClass,
                unresolved.exceptionConstructionOrdinal,
                unresolved.bytecodeInstructionIndex,
                unresolved.sourceLine);
    }

    static List<ExceptionTargetSite> scan(List<String> inputs)
            throws IOException {
        Map<String, ExceptionTargetSite> unique = new LinkedHashMap<>();
        if (inputs != null) {
            for (String input : inputs) {
                if (input == null || input.trim().isEmpty()) {
                    continue;
                }
                scanInput(Paths.get(input).toAbsolutePath().normalize(),
                        unique);
            }
        }
        List<ExceptionTargetSite> sites = new ArrayList<>(unique.values());
        sites.sort(Comparator.comparing(ExceptionTargetSite::stableIdentity));
        return sites;
    }

    private static void scanInput(Path input,
                                  Map<String, ExceptionTargetSite> sites)
            throws IOException {
        if (Files.isDirectory(input)) {
            try (Stream<Path> stream = Files.walk(input)) {
                List<Path> classes = stream
                        .filter(Files::isRegularFile)
                        .filter(path -> path.toString().endsWith(".class"))
                        .sorted()
                        .collect(Collectors.toList());
                for (Path classFile : classes) {
                    try (InputStream bytes = Files.newInputStream(classFile)) {
                        scanClass(bytes, sites);
                    }
                }
            }
            return;
        }
        if (Files.isRegularFile(input)
                && (input.toString().endsWith(".jar")
                || input.toString().endsWith(".zip"))) {
            try (JarFile jar = new JarFile(input.toFile())) {
                List<JarEntry> entries = new ArrayList<>();
                Enumeration<JarEntry> enumeration = jar.entries();
                while (enumeration.hasMoreElements()) {
                    JarEntry entry = enumeration.nextElement();
                    if (!entry.isDirectory()
                            && entry.getName().endsWith(".class")) {
                        entries.add(entry);
                    }
                }
                entries.sort(Comparator.comparing(JarEntry::getName));
                for (JarEntry entry : entries) {
                    try (InputStream bytes = jar.getInputStream(entry)) {
                        scanClass(bytes, sites);
                    }
                }
            }
        }
    }

    private static void scanClass(InputStream bytes,
                                  Map<String, ExceptionTargetSite> sites)
            throws IOException {
        ClassNode classNode = new ClassNode(Opcodes.ASM9);
        try {
            new ClassReader(bytes).accept(classNode,
                    ClassReader.SKIP_FRAMES);
        } catch (RuntimeException exception) {
            throw new IOException("Could not inspect class-file annotations",
                    exception);
        }
        String className = classNode.name.replace('/', '.');
        for (MethodNode method : classNode.methods) {
            scanMethod(className, method, sites);
        }
    }

    private static void scanMethod(String className, MethodNode method,
                                   Map<String, ExceptionTargetSite> sites)
            throws IOException {
        Map<String, Integer> newOrdinals = new LinkedHashMap<>();
        int instructionIndex = -1;
        int line = -1;
        for (AbstractInsnNode instruction = method.instructions.getFirst();
             instruction != null; instruction = instruction.getNext()) {
            if (instruction instanceof LineNumberNode) {
                line = ((LineNumberNode) instruction).line;
            }
            if (instruction.getOpcode() >= 0) {
                instructionIndex++;
            }
            if (!(instruction instanceof TypeInsnNode)
                    || instruction.getOpcode() != Opcodes.NEW) {
                continue;
            }
            TypeInsnNode creation = (TypeInsnNode) instruction;
            int ordinal = newOrdinals.getOrDefault(creation.desc, 0);
            newOrdinals.put(creation.desc, ordinal + 1);
            List<TypeAnnotationNode> annotations = new ArrayList<>();
            if (instruction.visibleTypeAnnotations != null) {
                annotations.addAll(instruction.visibleTypeAnnotations);
            }
            if (instruction.invisibleTypeAnnotations != null) {
                annotations.addAll(instruction.invisibleTypeAnnotations);
            }
            for (TypeAnnotationNode annotation : annotations) {
                if (!ANNOTATION_DESCRIPTOR.equals(annotation.desc)) {
                    continue;
                }
                if (new TypeReference(annotation.typeRef).getSort()
                        != TypeReference.NEW) {
                    throw new IOException("@CausynthExceptionTarget on "
                            + className + "#" + method.name
                            + " is not attached to a NEW instruction");
                }
                String id = annotationString(annotation, "value");
                ExceptionTargetSite site = new ExceptionTargetSite(id,
                        className, method.name, method.desc, "",
                        creation.desc.replace('/', '.'), ordinal,
                        instructionIndex, line);
                ExceptionTargetSite previous = sites.putIfAbsent(
                        site.stableIdentity(), site);
                if (previous != null && !previous.id.equals(site.id)) {
                    throw new IOException("Conflicting exception target ids "
                            + "for " + site.stableIdentity());
                }
            }
        }
    }

    private static String annotationString(AnnotationNode annotation,
                                           String key) {
        if (annotation.values == null) {
            return "";
        }
        for (int index = 0; index + 1 < annotation.values.size(); index += 2) {
            if (key.equals(annotation.values.get(index))) {
                Object value = annotation.values.get(index + 1);
                return value == null ? "" : value.toString();
            }
        }
        return "";
    }

    private static String resolveMethodSignature(ExceptionTargetSite site)
            throws IOException {
        SootClass owner = Scene.v().getSootClassUnsafe(site.className, false);
        if (owner == null || !owner.isApplicationClass()) {
            throw new IOException("Annotated target class is not an "
                    + "application class: " + site.className);
        }
        List<SootMethod> matches = new ArrayList<>();
        for (SootMethod method : owner.getMethods()) {
            if (site.methodName.equals(method.getName())
                    && site.methodDescriptor.equals(descriptor(method))) {
                matches.add(method);
            }
        }
        if (matches.size() != 1) {
            throw new IOException("Could not resolve annotated bytecode method "
                    + site.className + "#" + site.methodName
                    + site.methodDescriptor + " in Soot; matches="
                    + matches.size());
        }
        return matches.get(0).getSignature();
    }

    private static String descriptor(SootMethod method) throws IOException {
        StringBuilder descriptor = new StringBuilder("(");
        for (soot.Type parameter : method.getParameterTypes()) {
            descriptor.append(descriptor(parameter));
        }
        return descriptor.append(')')
                .append(descriptor(method.getReturnType())).toString();
    }

    private static String descriptor(soot.Type type) throws IOException {
        if (type instanceof VoidType) return "V";
        if (type instanceof BooleanType) return "Z";
        if (type instanceof ByteType) return "B";
        if (type instanceof CharType) return "C";
        if (type instanceof ShortType) return "S";
        if (type instanceof IntType) return "I";
        if (type instanceof LongType) return "J";
        if (type instanceof FloatType) return "F";
        if (type instanceof DoubleType) return "D";
        if (type instanceof RefType) {
            return "L" + ((RefType) type).getClassName()
                    .replace('.', '/') + ";";
        }
        if (type instanceof ArrayType) {
            ArrayType array = (ArrayType) type;
            return String.join("", Collections.nCopies(array.numDimensions,
                    "[")) + descriptor(array.baseType);
        }
        throw new IOException("Unsupported Soot type in annotated target "
                + "method descriptor: " + type);
    }
}

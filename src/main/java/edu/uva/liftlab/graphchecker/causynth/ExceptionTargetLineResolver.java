package edu.uva.liftlab.graphchecker.causynth;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.LineNumberNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
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
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.stream.Collectors;

final class ExceptionTargetLineResolver {
    private ExceptionTargetLineResolver() {
    }

    static final class TargetLine {
        final String name;
        final String className;
        final int line;
        final String thrownType;

        TargetLine(String name, String className, int line,
                   String thrownType) {
            this.name = name;
            this.className = className;
            this.line = line;
            this.thrownType = thrownType;
        }

        static TargetLine parse(String value) throws IOException {
            String[] fields = value.trim().split("\\s+");
            if (fields.length < 3 || fields.length > 4
                    || !fields[2].matches("[1-9][0-9]*")) {
                throw new IOException("exception_target is <name> <binary "
                        + "class name> <source line> [<thrown type>], not: "
                        + value.trim());
            }
            return new TargetLine(fields[0], fields[1],
                    Integer.parseInt(fields[2]),
                    fields.length == 4 ? fields[3] : "");
        }

        boolean throwsType(String internalName) {
            if (thrownType.isEmpty()) {
                return true;
            }
            String[] actual = internalName.split("[/$]");
            String[] stated = thrownType.split("[.$]");
            if (stated.length > actual.length) {
                return false;
            }
            for (int i = 1; i <= stated.length; i++) {
                if (!stated[stated.length - i]
                        .equals(actual[actual.length - i])) {
                    return false;
                }
            }
            return true;
        }

        String render() {
            return className + ":" + line
                    + (thrownType.isEmpty() ? "" : " (" + thrownType + ")");
        }
    }

    static ExceptionTargetSite resolve(List<String> inputs, TargetLine target)
            throws IOException {
        ExceptionTargetSite site = locate(inputs, target);
        return new ExceptionTargetSite(site.id, site.className,
                site.methodName, site.methodDescriptor,
                methodSignature(site), site.exceptionClass,
                site.exceptionConstructionOrdinal);
    }

    static ExceptionTargetSite locate(List<String> inputs, TargetLine target)
            throws IOException {
        List<ClassNode> family = classFamily(inputs, target.className);
        if (family.isEmpty()) {
            throw new IOException("TARGET_LINE_UNRESOLVED: "
                    + target.className + " is not among the analysis inputs "
                    + inputs + " (" + target.name + ")");
        }
        List<ExceptionTargetSite> found = new ArrayList<>();
        for (ClassNode owner : family) {
            for (MethodNode method : owner.methods) {
                collect(owner, method, target, found);
            }
        }
        if (found.isEmpty()) {
            throw new IOException("TARGET_LINE_UNRESOLVED: no throw new at "
                    + target.render() + " in " + target.className
                    + " or its nested classes (" + target.name + ")");
        }
        if (found.size() > 1) {
            throw new IOException("TARGET_LINE_AMBIGUOUS: " + found.size()
                    + " throw new at " + target.render() + " ("
                    + target.name + ")"
                    + (target.thrownType.isEmpty()
                    ? "; state the thrown type" : "") + ": "
                    + found.stream().map(ExceptionTargetSite::stableIdentity)
                    .sorted().collect(Collectors.toList()));
        }
        return found.get(0);
    }

    private static void collect(ClassNode owner, MethodNode method,
                                TargetLine target,
                                List<ExceptionTargetSite> found) {
        Map<String, Integer> ordinals = new HashMap<>();
        int line = -1;
        for (AbstractInsnNode instruction = method.instructions.getFirst();
             instruction != null; instruction = instruction.getNext()) {
            if (instruction instanceof LineNumberNode) {
                line = ((LineNumberNode) instruction).line;
                continue;
            }
            if (instruction.getOpcode() != Opcodes.NEW) {
                continue;
            }
            TypeInsnNode creation = (TypeInsnNode) instruction;
            int ordinal = ordinals.merge(creation.desc, 1, Integer::sum) - 1;
            if (line == target.line && target.throwsType(creation.desc)
                    && thrownOnConstruction(creation)) {
                found.add(new ExceptionTargetSite(target.name,
                        owner.name.replace('/', '.'), method.name,
                        method.desc, "", creation.desc.replace('/', '.'),
                        ordinal));
            }
        }
    }

    private static boolean thrownOnConstruction(TypeInsnNode creation) {
        int nested = 0;
        for (AbstractInsnNode instruction = creation.getNext();
             instruction != null; instruction = instruction.getNext()) {
            if (instruction.getOpcode() == Opcodes.NEW
                    && creation.desc.equals(
                    ((TypeInsnNode) instruction).desc)) {
                nested++;
            } else if (instruction.getOpcode() == Opcodes.INVOKESPECIAL
                    && creation.desc.equals(
                    ((MethodInsnNode) instruction).owner)
                    && "<init>".equals(((MethodInsnNode) instruction).name)) {
                if (nested-- == 0) {
                    AbstractInsnNode next = instruction.getNext();
                    while (next != null && next.getOpcode() < 0) {
                        next = next.getNext();
                    }
                    return next != null && next.getOpcode() == Opcodes.ATHROW;
                }
            }
        }
        return false;
    }

    private static List<ClassNode> classFamily(List<String> inputs,
                                               String className)
            throws IOException {
        String internal = className.replace('.', '/');
        String simple = internal.substring(internal.lastIndexOf('/') + 1);
        List<ClassNode> family = new ArrayList<>();
        for (String input : inputs == null
                ? Collections.<String>emptyList() : inputs) {
            if (input == null || input.trim().isEmpty()) {
                continue;
            }
            Path root = Paths.get(input.trim()).toAbsolutePath().normalize();
            if (Files.isDirectory(root)) {
                Path directory = root.resolve(internal).getParent();
                if (!Files.isDirectory(directory)) {
                    continue;
                }
                List<Path> files = new ArrayList<>();
                try (DirectoryStream<Path> members = Files.newDirectoryStream(
                        directory, simple + "{.class,$*.class}")) {
                    members.forEach(files::add);
                }
                Collections.sort(files);
                for (Path file : files) {
                    try (InputStream bytes = Files.newInputStream(file)) {
                        family.add(read(bytes));
                    }
                }
            } else if (Files.isRegularFile(root)) {
                try (JarFile jar = new JarFile(root.toFile())) {
                    List<JarEntry> entries = jar.stream()
                            .filter(entry -> entry.getName()
                                    .equals(internal + ".class")
                                    || entry.getName().startsWith(internal + "$")
                                    && entry.getName().endsWith(".class"))
                            .sorted((a, b) -> a.getName()
                                    .compareTo(b.getName()))
                            .collect(Collectors.toList());
                    for (JarEntry entry : entries) {
                        try (InputStream bytes = jar.getInputStream(entry)) {
                            family.add(read(bytes));
                        }
                    }
                }
            }
        }
        return family;
    }

    private static ClassNode read(InputStream bytes) throws IOException {
        ClassNode node = new ClassNode(Opcodes.ASM9);
        try {
            new ClassReader(bytes).accept(node, ClassReader.SKIP_FRAMES);
        } catch (RuntimeException exception) {
            throw new IOException("Could not read a target class file",
                    exception);
        }
        return node;
    }

    private static String methodSignature(ExceptionTargetSite site)
            throws IOException {
        SootClass owner = Scene.v().getSootClassUnsafe(site.className, false);
        if (owner == null || !owner.isApplicationClass()) {
            throw new IOException("The target class is not an application "
                    + "class: " + site.className);
        }
        List<SootMethod> matches = new ArrayList<>();
        for (SootMethod method : owner.getMethods()) {
            if (site.methodName.equals(method.getName())
                    && site.methodDescriptor.equals(descriptor(method))) {
                matches.add(method);
            }
        }
        if (matches.size() != 1) {
            throw new IOException("Could not resolve the target's bytecode "
                    + "method " + site.className + "#" + site.methodName
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
        throw new IOException("Unsupported Soot type in the target method's "
                + "descriptor: " + type);
    }
}

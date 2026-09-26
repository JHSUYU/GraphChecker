package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.FieldVisitor;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

/**
 * Grows the analysis scope toward the slice's frontier (SYMBOL-SCOPE §2):
 * for a {@link ScopeFrontier#CALLEE}, the class whose concrete body it is --
 * or, for an abstract one, every class of the roots implementing it; for a
 * {@link ScopeFrontier#FIELD}, its owner and, unless it is private, every
 * class storing it (a reference field: every class loading it too, since the
 * object it holds is written through it).  A protobuf message is a wire
 * payload (F3), never scope.  Rows are taken nearest first until the budget of
 * grown classes is spent; each class taken is copied into the grown directory
 * and listed in its {@value #MANIFEST} with the row that took it.
 *
 * <p>Usage: {@code ScopeGrowth <grown-dir> <frontier.jsonl> <budget>
 * <scope-dir> <class-root>...}.  Prints the number of classes it added.</p>
 */
public final class ScopeGrowth {
    /** The grown classes and why, one {@code class<TAB>kind<TAB>signature}
     *  line each, in the order they were taken. */
    public static final String MANIFEST = "GROWN";
    private static final Pattern METHOD = Pattern.compile(
            "<([^:]+): \\S+ ([^(\\s]+)\\(([^)]*)\\)>");
    private static final Pattern FIELD = Pattern.compile(
            "<([^:]+): (\\S+) ([^\\s>]+)>");

    private final Map<String, ClassFacts> classes = new LinkedHashMap<>();

    ScopeGrowth() {
    }

    public static void main(String[] args) throws IOException {
        if (args.length < 5) {
            throw new IllegalArgumentException("usage: ScopeGrowth "
                    + "<grown-dir> <frontier.jsonl> <budget> <scope-dir> "
                    + "<class-root>...");
        }
        Path grown = Paths.get(args[0]);
        int budget = Integer.parseInt(args[2]);
        ScopeGrowth index = new ScopeGrowth();
        for (int at = 4; at < args.length; at++) {
            index.scan(Paths.get(args[at]));
        }
        Set<String> present = new LinkedHashSet<>();
        present.addAll(classNames(Paths.get(args[3])));
        present.addAll(classNames(grown));
        Path manifest = grown.resolve(MANIFEST);
        int taken = Files.exists(manifest)
                ? Files.readAllLines(manifest, StandardCharsets.UTF_8).size()
                : 0;
        int added = 0;
        for (String line : Files.readAllLines(Paths.get(args[1]),
                StandardCharsets.UTF_8)) {
            if (line.trim().isEmpty()) continue;
            JsonObject row = JsonParser.parseString(line).getAsJsonObject();
            String kind = row.get("kind").getAsString();
            String signature = row.get("signature").getAsString();
            for (String name : index.resolve(kind, signature)) {
                if (taken + added >= budget) break;
                ClassFacts facts = index.classes.get(name);
                if (present.contains(name) || index.protobuf(name)) continue;
                Path target = grown.resolve(facts.relative);
                Files.createDirectories(target.getParent());
                Files.copy(facts.file, target,
                        StandardCopyOption.REPLACE_EXISTING);
                Files.write(manifest, Collections.singletonList(name + "\t"
                                + kind + "\t" + signature),
                        StandardCharsets.UTF_8, StandardOpenOption.CREATE,
                        StandardOpenOption.APPEND);
                present.add(name);
                added++;
            }
        }
        System.out.println(added);
    }

    /** The classes of the roots one frontier row reaches, in name order. */
    Set<String> resolve(String kind, String signature) {
        Set<String> found = new TreeSet<>();
        if (ScopeFrontier.CALLEE.equals(kind)) {
            Matcher method = METHOD.matcher(signature);
            if (!method.matches()) return found;
            String key = method.group(2) + "(" + method.group(3) + ")";
            ClassFacts owner = classes.get(method.group(1));
            if (owner != null && owner.concrete.contains(key)) {
                found.add(owner.name);
                return found;
            }
            for (ClassFacts candidate : classes.values()) {
                if (candidate.concrete.contains(key)
                        && subtype(candidate.name, method.group(1))) {
                    found.add(candidate.name);
                }
            }
        } else if (ScopeFrontier.FIELD.equals(kind)) {
            Matcher field = FIELD.matcher(signature);
            if (!field.matches()) return found;
            ClassFacts owner = classes.get(field.group(1));
            if (owner == null) return found;
            found.add(owner.name);
            if (owner.privateFields.contains(field.group(3))) return found;
            boolean reference = !primitive(field.group(2));
            for (ClassFacts candidate : classes.values()) {
                for (String access : candidate.fieldAccesses) {
                    String[] parts = access.split("\\|", 3);
                    if (parts[2].equals(field.group(3))
                            && ("W".equals(parts[0]) || reference)
                            && subtype(parts[1], owner.name)) {
                        found.add(candidate.name);
                    }
                }
            }
        }
        return found;
    }

    /** Whether {@code name} is {@code ancestor} or below it in the roots. */
    private boolean subtype(String name, String ancestor) {
        Set<String> seen = new LinkedHashSet<>();
        List<String> pending = new ArrayList<>(Collections.singleton(name));
        while (!pending.isEmpty()) {
            String next = pending.remove(pending.size() - 1);
            if (next.equals(ancestor)) return true;
            ClassFacts facts = classes.get(next);
            if (facts == null || !seen.add(next)) continue;
            pending.addAll(facts.supertypes);
        }
        return false;
    }

    /** A generated protobuf class: some supertype is protobuf's. */
    private boolean protobuf(String name) {
        Set<String> seen = new LinkedHashSet<>();
        List<String> pending = new ArrayList<>(Collections.singleton(name));
        while (!pending.isEmpty()) {
            String next = pending.remove(pending.size() - 1);
            if (next.contains(".protobuf.")) return true;
            ClassFacts facts = classes.get(next);
            if (facts == null || !seen.add(next)) continue;
            pending.addAll(facts.supertypes);
        }
        return false;
    }

    private static boolean primitive(String type) {
        switch (type) {
            case "boolean": case "byte": case "char": case "short":
            case "int": case "long": case "float": case "double":
            case "java.lang.String":
                return true;
            default:
                return false;
        }
    }

    void scan(Path root) throws IOException {
        if (!Files.isDirectory(root)) {
            throw new IllegalStateException(
                    "scope growth class root not found: " + root);
        }
        for (Path file : classFiles(root)) {
            ClassFacts facts = new ClassFacts(file, root.relativize(file));
            try (InputStream in = Files.newInputStream(file)) {
                new ClassReader(in).accept(facts,
                        ClassReader.SKIP_DEBUG | ClassReader.SKIP_FRAMES);
            }
            classes.putIfAbsent(facts.name, facts);
        }
    }

    private static Set<String> classNames(Path root) throws IOException {
        Set<String> names = new LinkedHashSet<>();
        if (!Files.isDirectory(root)) return names;
        for (Path file : classFiles(root)) {
            String relative = root.relativize(file).toString();
            names.add(relative.substring(0, relative.length() - 6)
                    .replace('/', '.'));
        }
        return names;
    }

    private static List<Path> classFiles(Path root) throws IOException {
        List<Path> files = new ArrayList<>();
        try (Stream<Path> walk = Files.walk(root)) {
            walk.filter(path -> path.toString().endsWith(".class"))
                    .sorted().forEach(files::add);
        }
        return files;
    }

    /** What one class file states: its supertypes, the methods it has a
     *  body for, its private fields, and the fields it loads and stores. */
    private static final class ClassFacts extends ClassVisitor {
        final Path file;
        final Path relative;
        String name = "";
        final List<String> supertypes = new ArrayList<>();
        /** {@code name(paramType,...)} of every concrete method. */
        final Set<String> concrete = new LinkedHashSet<>();
        final Set<String> privateFields = new LinkedHashSet<>();
        /** {@code R|owner|field} or {@code W|owner|field}. */
        final Set<String> fieldAccesses = new LinkedHashSet<>();

        ClassFacts(Path file, Path relative) {
            super(Opcodes.ASM9);
            this.file = file;
            this.relative = relative;
        }

        @Override
        public void visit(int version, int access, String internal,
                          String signature, String superName,
                          String[] interfaces) {
            name = internal.replace('/', '.');
            if (superName != null) supertypes.add(superName.replace('/', '.'));
            for (String type : interfaces) {
                supertypes.add(type.replace('/', '.'));
            }
        }

        @Override
        public FieldVisitor visitField(int access, String field,
                                       String descriptor, String signature,
                                       Object value) {
            if ((access & Opcodes.ACC_PRIVATE) != 0) privateFields.add(field);
            return null;
        }

        @Override
        public MethodVisitor visitMethod(int access, String method,
                                         String descriptor, String signature,
                                         String[] exceptions) {
            if ((access & Opcodes.ACC_ABSTRACT) == 0) {
                List<String> params = new ArrayList<>();
                for (Type type : Type.getArgumentTypes(descriptor)) {
                    params.add(type.getClassName());
                }
                concrete.add(method + "(" + String.join(",", params) + ")");
            }
            return new MethodVisitor(Opcodes.ASM9) {
                @Override
                public void visitFieldInsn(int opcode, String owner,
                                           String field, String type) {
                    boolean store = opcode == Opcodes.PUTFIELD
                            || opcode == Opcodes.PUTSTATIC;
                    fieldAccesses.add((store ? "W|" : "R|")
                            + owner.replace('/', '.') + "|" + field);
                }
            };
        }
    }
}

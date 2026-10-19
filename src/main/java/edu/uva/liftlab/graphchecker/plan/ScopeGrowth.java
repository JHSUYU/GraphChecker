package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.causynth.LibraryCatalog;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
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
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

public final class ScopeGrowth {
    public static final String MANIFEST = "GROWN";
    static final String DOORS = "--doors";
    private static final String DOOR = "DOOR";
    private static final String IO = "IO";
    private static final Pattern METHOD = Pattern.compile(
            "<([^:]+): \\S+ ([^(\\s]+)\\(([^)]*)\\)>");
    private static final Pattern FIELD = Pattern.compile(
            "<([^:]+): (\\S+) ([^\\s>]+)>");

    private final Map<String, ClassFacts> classes = new LinkedHashMap<>();

    ScopeGrowth() {
    }

    public static void main(String[] args) throws IOException {
        if (args.length > 0 && DOORS.equals(args[0])) {
            doors(args);
            return;
        }
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
        List<JsonObject> rows = new ArrayList<>();
        for (String line : Files.readAllLines(Paths.get(args[1]),
                StandardCharsets.UTF_8)) {
            if (!line.trim().isEmpty()) {
                rows.add(JsonParser.parseString(line).getAsJsonObject());
            }
        }
        Set<String> present = new LinkedHashSet<>(
                classNames(Paths.get(args[3])));
        present.addAll(classNames(grown));
        int taken = 0;
        for (String line : lines(grown.resolve(MANIFEST))) {
            if (!line.contains("\t" + DOOR + "\t")) taken++;
        }
        int added = 0;
        int byIo = 0;
        Set<String> noFileOperation = new TreeSet<>();
        for (JsonObject row : rows) {
            String kind = row.get("kind").getAsString();
            String signature = row.get("signature").getAsString();
            boolean io = row.has("demand")
                    && IO.equals(row.get("demand").getAsString());
            for (String name : index.resolve(kind, signature)) {
                if (taken + added >= budget) break;
                ClassFacts facts = index.classes.get(name);
                if (present.contains(name) || index.codec(name)) continue;
                if (io && !index.callsFileOperation(name, signature)) {
                    noFileOperation.add(name);
                    continue;
                }
                Path target = grown.resolve(facts.relative);
                Files.createDirectories(target.getParent());
                Files.copy(facts.file, target,
                        StandardCopyOption.REPLACE_EXISTING);
                append(grown.resolve(MANIFEST), name + "\t"
                        + (io ? IO : kind) + "\t" + signature + "\t"
                        + row.get("distance").getAsInt());
                present.add(name);
                added++;
                if (io) byIo++;
            }
        }
        System.out.println(added + " added " + added + " class(es), "
                + (taken + added) + " of " + budget + " grown, " + byIo
                + " by IO rows"
                + (noFileOperation.isEmpty() ? "" : "; IO rows skipped, no "
                + "file operation of their own: " + noFileOperation));
    }

    boolean callsFileOperation(String name, String signature) {
        ClassFacts facts = classes.get(name);
        Matcher member = METHOD.matcher(signature);
        if (facts == null || !member.matches()) return false;
        for (String call : facts.callsBy.getOrDefault(member.group(2) + "("
                + member.group(3) + ")", Collections.<String>emptySet())) {
            String[] at = call.split("\\|", 2);
            for (LibraryCatalog.Door door : LibraryCatalog.doors()) {
                Matcher anchor = METHOD.matcher(door.anchor);
                if (door.demanded && anchor.matches()
                        && anchor.group(1).equals(at[0])
                        && at[1].equals(anchor.group(2) + "("
                        + anchor.group(3) + ")")) {
                    return true;
                }
            }
        }
        return false;
    }

    private static void doors(String[] args) throws IOException {
        if (args.length < 5) {
            throw new IllegalArgumentException("usage: ScopeGrowth " + DOORS
                    + " <grown-dir> <scope-dir> <classpath> <class-root>...");
        }
        Path grown = Paths.get(args[1]);
        ScopeGrowth index = new ScopeGrowth();
        index.scan(Paths.get(args[2]));
        index.scan(grown);
        List<Path> search = new ArrayList<>();
        for (int at = 4; at < args.length; at++) {
            search.add(Paths.get(args[at]));
        }
        search.addAll(classpath(args[3]));
        Set<String> present = new LinkedHashSet<>(
                classNames(Paths.get(args[2])));
        present.addAll(classNames(grown));
        Set<String> placed = new LinkedHashSet<>();
        for (LibraryCatalog.Door door : LibraryCatalog.doors()) {
            if (!door.atCalls() && door.relocated != null) {
                placed.add(door.family());
            }
        }
        Set<String> decided = new LinkedHashSet<>();
        List<String> taken = new ArrayList<>();
        for (LibraryCatalog.Door door : LibraryCatalog.doors()) {
            if (door.atCalls()) continue;
            String family = door.family();
            if (!decided.add(family) || present.contains(family)
                    || !placed.contains(family) && !index.called(family)) {
                continue;
            }
            List<String> copied = copyFamily(family, search, grown);
            for (String name : copied) {
                append(grown.resolve(MANIFEST), name + "\t" + DOOR + "\t"
                        + door.method + "\t0");
            }
            if (!copied.isEmpty()) taken.add(family);
        }
        System.out.println(taken.size() + " door famil"
                + (taken.size() == 1 ? "y" : "ies") + " added: " + taken);
    }

    boolean called(String family) {
        String nested = family + "$";
        for (ClassFacts caller : classes.values()) {
            if (caller.name.equals(family)
                    || caller.name.startsWith(nested)) {
                continue;
            }
            for (String call : caller.calls) {
                String owner = call.substring(0, call.indexOf('|'));
                if (owner.equals(family) || owner.startsWith(nested)) {
                    return true;
                }
            }
        }
        return false;
    }

    static List<String> copyFamily(String family, List<Path> search,
                                   Path grown) throws IOException {
        String outer = family.replace('.', '/') + ".class";
        String nested = family.replace('.', '/') + "$";
        List<String> names = new ArrayList<>();
        for (Path entry : search) {
            if (Files.isDirectory(entry)) {
                if (!Files.isRegularFile(entry.resolve(outer))) continue;
                for (Path file : ArtifactIO.classFiles(entry.resolve(outer)
                        .getParent())) {
                    String relative = entry.relativize(file).toString();
                    if (!relative.equals(outer)
                            && !relative.startsWith(nested)) {
                        continue;
                    }
                    Path target = grown.resolve(relative);
                    Files.createDirectories(target.getParent());
                    Files.copy(file, target,
                            StandardCopyOption.REPLACE_EXISTING);
                    names.add(binaryName(relative));
                }
                return names;
            }
            if (!Files.isRegularFile(entry)
                    || !entry.toString().endsWith(".jar")) {
                continue;
            }
            try (ZipFile jar = new ZipFile(entry.toFile())) {
                if (jar.getEntry(outer) == null) continue;
                List<String> relatives = new ArrayList<>();
                for (ZipEntry file : Collections.list(jar.entries())) {
                    String relative = file.getName();
                    if (relative.equals(outer) || (relative.startsWith(nested)
                            && relative.endsWith(".class"))) {
                        relatives.add(relative);
                    }
                }
                Collections.sort(relatives);
                for (String relative : relatives) {
                    Path target = grown.resolve(relative);
                    Files.createDirectories(target.getParent());
                    try (InputStream in = jar.getInputStream(
                            jar.getEntry(relative))) {
                        Files.copy(in, target,
                                StandardCopyOption.REPLACE_EXISTING);
                    }
                    names.add(binaryName(relative));
                }
                return names;
            }
        }
        return names;
    }

    private static List<Path> classpath(String classpath) throws IOException {
        List<Path> entries = new ArrayList<>();
        for (String entry : classpath.split(Pattern.quote(
                java.io.File.pathSeparator))) {
            if (entry.trim().isEmpty()) continue;
            if (!entry.endsWith("/*")) {
                entries.add(Paths.get(entry));
                continue;
            }
            Path dir = Paths.get(entry.substring(0, entry.length() - 2));
            if (!Files.isDirectory(dir)) continue;
            try (Stream<Path> jars = Files.list(dir)) {
                jars.filter(path -> path.toString().endsWith(".jar"))
                        .sorted().forEach(entries::add);
            }
        }
        return entries;
    }

    private static String binaryName(String relative) {
        return relative.substring(0, relative.length() - 6).replace('/', '.');
    }

    private static List<String> lines(Path file) throws IOException {
        return Files.exists(file)
                ? Files.readAllLines(file, StandardCharsets.UTF_8)
                : Collections.<String>emptyList();
    }

    private static void append(Path file, String line) throws IOException {
        Files.write(file, Collections.singletonList(line),
                StandardCharsets.UTF_8, StandardOpenOption.CREATE,
                StandardOpenOption.APPEND);
    }

    Set<String> resolve(String kind, String signature) {
        Set<String> found = new TreeSet<>();
        Matcher member = (ScopeFrontier.FIELD.equals(kind) ? FIELD : METHOD)
                .matcher(signature);
        if (!member.matches()) return found;
        String owner = member.group(1);
        if (ScopeFrontier.FIELD.equals(kind)) {
            ClassFacts facts = classes.get(owner);
            Integer access = facts == null ? null
                    : facts.fields.get(member.group(3));
            if (access == null || constant(access)) return found;
            found.add(owner);
            if ((access & (Opcodes.ACC_PRIVATE | Opcodes.ACC_FINAL)) != 0) {
                return found;
            }
            for (ClassFacts candidate : classes.values()) {
                for (String store : candidate.stores) {
                    String[] at = store.split("\\|", 2);
                    if (at[1].equals(member.group(3))
                            && subtype(at[0], owner)) {
                        found.add(candidate.name);
                    }
                }
            }
            return found;
        }
        String key = member.group(2) + "(" + member.group(3) + ")";
        if (ScopeFrontier.FORMAL.equals(kind)) {
            for (ClassFacts candidate : classes.values()) {
                for (String call : candidate.calls) {
                    String[] at = call.split("\\|", 2);
                    if (at[1].equals(key) && (subtype(at[0], owner)
                            || subtype(owner, at[0]))) {
                        found.add(candidate.name);
                    }
                }
            }
            return found;
        }
        ClassFacts declared = classes.get(owner);
        if (declared == null) return found;
        if (declared.bodies.containsKey(key)) {
            if (!constantBody(declared.bodies.get(key))) found.add(owner);
            return found;
        }
        for (ClassFacts candidate : classes.values()) {
            if (!subtype(candidate.name, owner)) continue;
            for (ClassFacts at = candidate; at != null;
                 at = classes.get(at.superclass)) {
                if (!at.bodies.containsKey(key)) continue;
                if (!constantBody(at.bodies.get(key))) found.add(at.name);
                break;
            }
        }
        return found;
    }

    private static boolean constant(int access) {
        int flags = Opcodes.ACC_STATIC | Opcodes.ACC_FINAL;
        return (access & flags) == flags;
    }

    private boolean constantBody(Set<String> statics) {
        if (statics == null) return false;
        for (String field : statics) {
            String[] at = field.split("\\|", 2);
            ClassFacts owner = classes.get(at[0]);
            Integer access = owner == null ? null : owner.fields.get(at[1]);
            if (access == null || !constant(access)) return false;
        }
        return true;
    }

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

    boolean codec(String name) {
        Set<String> seen = new LinkedHashSet<>();
        List<String> pending = new ArrayList<>(Collections.singleton(name));
        while (!pending.isEmpty()) {
            String next = pending.remove(pending.size() - 1);
            for (java.util.regex.Pattern codec
                    : LibraryCatalog.codecClasses()) {
                if (codec.matcher(next).matches()) return true;
            }
            ClassFacts facts = classes.get(next);
            if (facts == null || !seen.add(next)) continue;
            pending.addAll(facts.supertypes);
        }
        return false;
    }

    void scan(Path root) throws IOException {
        if (!Files.isDirectory(root)) {
            throw new IllegalStateException(
                    "scope growth class root not found: " + root);
        }
        for (Path file : ArtifactIO.classFiles(root)) {
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
        for (Path file : ArtifactIO.classFiles(root)) {
            String relative = root.relativize(file).toString();
            names.add(relative.substring(0, relative.length() - 6)
                    .replace('/', '.'));
        }
        return names;
    }

    private static final class ClassFacts extends ClassVisitor {
        final Path file;
        final Path relative;
        String name = "";
        String superclass = "";
        final List<String> supertypes = new ArrayList<>();
        final Map<String, Set<String>> bodies = new LinkedHashMap<>();
        final Map<String, Integer> fields = new LinkedHashMap<>();
        final Set<String> stores = new LinkedHashSet<>();
        final Set<String> calls = new LinkedHashSet<>();
        final Map<String, Set<String>> callsBy = new LinkedHashMap<>();

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
            if (superName != null) {
                superclass = superName.replace('/', '.');
                supertypes.add(superclass);
            }
            for (String type : interfaces) {
                supertypes.add(type.replace('/', '.'));
            }
        }

        @Override
        public FieldVisitor visitField(int access, String field,
                                       String descriptor, String signature,
                                       Object value) {
            fields.put(field, access);
            return null;
        }

        @Override
        public MethodVisitor visitMethod(int access, String method,
                                         String descriptor, String signature,
                                         String[] exceptions) {
            String body = key(method, descriptor);
            if ((access & Opcodes.ACC_ABSTRACT) == 0) {
                bodies.put(body, new LinkedHashSet<String>());
            }
            return new MethodVisitor(Opcodes.ASM9) {
                @Override
                public void visitFieldInsn(int opcode, String owner,
                                           String field, String type) {
                    String at = owner.replace('/', '.') + "|" + field;
                    if (opcode == Opcodes.PUTFIELD
                            || opcode == Opcodes.PUTSTATIC) {
                        stores.add(at);
                    }
                    Set<String> statics = bodies.get(body);
                    if (statics == null) return;
                    if (opcode == Opcodes.GETSTATIC) {
                        statics.add(at);
                    } else {
                        bodies.put(body, null);
                    }
                }

                @Override
                public void visitMethodInsn(int opcode, String owner,
                                            String callee, String type,
                                            boolean isInterface) {
                    String call = owner.replace('/', '.') + "|"
                            + key(callee, type);
                    calls.add(call);
                    callsBy.computeIfAbsent(body,
                            ignored -> new LinkedHashSet<>()).add(call);
                    if (bodies.containsKey(body)) bodies.put(body, null);
                }

                @Override
                public void visitInvokeDynamicInsn(String callee,
                                                   String type,
                                                   org.objectweb.asm.Handle
                                                           bootstrap,
                                                   Object... arguments) {
                    if (bodies.containsKey(body)) bodies.put(body, null);
                }
            };
        }

        private static String key(String method, String descriptor) {
            List<String> params = new ArrayList<>();
            for (Type type : Type.getArgumentTypes(descriptor)) {
                params.add(type.getClassName());
            }
            return method + "(" + String.join(",", params) + ")";
        }
    }
}

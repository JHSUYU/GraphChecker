package edu.uva.liftlab.graphchecker.plan;

import edu.uva.liftlab.graphchecker.contract.WireDeclarations;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

/**
 * The lineage scope: every application class that hands work to another thread,
 * runs it, waits/signals, or makes an unseeded draw ({@link
 * WorkStartSites#UNSEEDED_DRAWS}: the weave seeds it, so a replay draws what
 * its recording drew wherever the class sits; HDFS's NetworkTopology, which
 * places a pipeline's DataNodes by ThreadLocalRandom, neither hands off work
 * nor is analysed).
 * A lineage hole puts everything after it under
 * {@code Lost:UNKNOWN}, so the weave's work-start, claim and timed-wait hooks
 * cover this scope ({@code CausynthPipeline.instrumentApplicationScope}).
 * Bytecode only, no hierarchy: wide {@link WorkStartSites} predicates; classes
 * already analysed are skipped.  A class that declares a codec's encoder or
 * decoder, or an exchange bracket ({@link WireDeclarations#configured}), is
 * kept whatever it does: the codec weave hooks it
 * ({@code causynth.CodecWeave}).
 *
 * <p>Usage: {@code LineageScan <out-dir> <analysed-dirs> <class-root>...},
 * {@code <analysed-dirs>} path-separated: the case's scope and what SEED grew
 * it by ({@link ScopeGrowth}).</p>
 */
public final class LineageScan {
    private LineageScan() {
    }

    public static void main(String[] args) throws IOException {
        if (args.length < 3) {
            throw new IllegalArgumentException("usage: LineageScan <out-dir> "
                    + "<analysed-dirs> <class-root>...");
        }
        Path out = Paths.get(args[0]);
        List<Path> analysed = new ArrayList<>();
        for (String dir : args[1].split(java.util.regex.Pattern.quote(
                java.io.File.pathSeparator))) {
            if (!dir.isEmpty()) analysed.add(Paths.get(dir));
        }
        Set<String> declared = declaredClassFiles(
                WireDeclarations.configured());
        int scanned = 0;
        int kept = 0;
        for (int index = 2; index < args.length; index++) {
            Path root = Paths.get(args[index]);
            if (!Files.isDirectory(root)) {
                throw new IllegalStateException(
                        "lineage class root not found: " + root);
            }
            for (Path file : classFiles(root)) {
                scanned++;
                Path relative = root.relativize(file);
                if (analysed.stream().anyMatch(dir
                        -> Files.exists(dir.resolve(relative)))) {
                    continue;
                }
                if (!declared.contains(relative.toString().replace(
                        java.io.File.separatorChar, '/'))
                        && !handsOffWork(file)) {
                    continue;
                }
                Path target = out.resolve(relative);
                Files.createDirectories(target.getParent());
                Files.copy(file, target, StandardCopyOption.REPLACE_EXISTING);
                kept++;
            }
        }
        System.out.println("lineage scope: " + kept + " of " + scanned
                + " class(es) start, hand off, run, wait, signal, draw or hold"
                + " a declared codec method outside the analysis scope");
    }

    /**
     * The class files that declare a hooked method: every codec method
     * hook's and every exchange's ({@code a/b/C.class}); a call pattern
     * names no class of its own.
     */
    static Set<String> declaredClassFiles(WireDeclarations declared) {
        Set<String> files = new LinkedHashSet<>();
        List<String> methods = new ArrayList<>();
        for (WireDeclarations.Codec codec : declared.codecs()) {
            for (WireDeclarations.Hook hook : codec.encoders()) {
                if (!hook.call()) methods.add(hook.target());
            }
            for (WireDeclarations.Hook hook : codec.decoders()) {
                if (!hook.call()) methods.add(hook.target());
            }
        }
        for (WireDeclarations.Exchange exchange : declared.exchanges()) {
            methods.add(exchange.method());
        }
        for (String method : methods) {
            files.add(method.substring(1, method.indexOf(':')).replace('.',
                    '/') + ".class");
        }
        return files;
    }

    private static List<Path> classFiles(Path root) throws IOException {
        List<Path> files = new ArrayList<>();
        try (Stream<Path> walk = Files.walk(root)) {
            walk.filter(path -> path.toString().endsWith(".class"))
                    .sorted()
                    .forEach(files::add);
        }
        return files;
    }

    static boolean handsOffWork(Path file) throws IOException {
        try (InputStream in = Files.newInputStream(file)) {
            return handsOffWork(new ClassReader(in));
        }
    }

    static boolean handsOffWork(ClassReader reader) {
        boolean[] found = {false};
        reader.accept(new ClassVisitor(Opcodes.ASM9) {
            @Override
            public MethodVisitor visitMethod(int access, String name,
                                             String descriptor,
                                             String signature,
                                             String[] exceptions) {
                if (found[0] || (access & Opcodes.ACC_ABSTRACT) != 0) {
                    return null;
                }
                if ((access & Opcodes.ACC_STATIC) == 0
                        && WorkStartSites.mayEnterWork(name,
                        Type.getArgumentTypes(descriptor).length)) {
                    found[0] = true;
                    return null;
                }
                return new MethodVisitor(Opcodes.ASM9) {
                    @Override
                    public void visitMethodInsn(int opcode, String owner,
                                                String callee,
                                                String calleeDescriptor,
                                                boolean isInterface) {
                        if (WorkStartSites.mayHandOffWork(owner, callee,
                                Type.getArgumentTypes(calleeDescriptor)
                                        .length)
                                || WorkStartSites.mayWait(callee)
                                || WorkStartSites.UNSEEDED_DRAWS.contains(
                                        owner + "." + callee
                                                + calleeDescriptor)) {
                            found[0] = true;
                        }
                    }
                };
            }
        }, ClassReader.SKIP_DEBUG | ClassReader.SKIP_FRAMES);
        return found[0];
    }
}

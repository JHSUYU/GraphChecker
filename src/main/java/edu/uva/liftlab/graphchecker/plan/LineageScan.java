package edu.uva.liftlab.graphchecker.plan;

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
import java.util.List;
import java.util.stream.Stream;

/**
 * THE LINEAGE SCOPE: every class of the application that hands work to
 * another thread, runs work handed to it, or waits or signals, whatever the
 * case analyses.
 *
 * <p>The analysis scope says which regions a case executes symbolically.
 * Lineage is a different question -- which thread's execution is whose, and
 * which message caused it -- and a hole anywhere in it is a hole everywhere
 * after it: on hdfs-17967 path B the DataNode actor put a heartbeat answer's
 * KeyUpdateCommand on its command queue and the command processor ran
 * {@code addKeys} under {@code Lost:UNKNOWN}, because {@code BPServiceActor}
 * was outside the case's twelve analysed classes and neither its thread
 * start nor its queue handoff was woven.  And a daemon's turn is paced by
 * its waits: v27's seed replay met the DataNode actors' own heartbeats where
 * the recording had the workload's, because the actor's
 * {@code waitTillNextIBR} read the wall clock of a replay many times slower.
 * So the weave's work-start, work-claim, queue-claim and timed-wait hooks
 * cover this scope too, and nothing else of the weave does
 * ({@code CausynthPipeline.instrumentApplicationScope}).</p>
 *
 * <p>The scan reads bytecode with no class hierarchy, so it keeps a class on
 * the wide predicates of {@link WorkStartSites} and lets the weave decide the
 * exact shapes.  A class the analysis scope already holds is not copied: it
 * is woven whole.</p>
 *
 * <p>Usage: {@code LineageScan <out-dir> <analysis-dir> <class-root>...}</p>
 */
public final class LineageScan {
    private LineageScan() {
    }

    public static void main(String[] args) throws IOException {
        if (args.length < 3) {
            throw new IllegalArgumentException("usage: LineageScan <out-dir> "
                    + "<analysis-dir> <class-root>...");
        }
        Path out = Paths.get(args[0]);
        Path analysis = Paths.get(args[1]);
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
                if (Files.exists(analysis.resolve(relative))) continue;
                if (!handsOffWork(file)) continue;
                Path target = out.resolve(relative);
                Files.createDirectories(target.getParent());
                Files.copy(file, target, StandardCopyOption.REPLACE_EXISTING);
                kept++;
            }
        }
        System.out.println("lineage scope: " + kept + " of " + scanned
                + " class(es) start, hand off, run, wait or signal outside the "
                + "analysis scope");
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

    /** Whether one class file starts, hands off, runs, waits or signals. */
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
                                || WorkStartSites.mayWait(callee)) {
                            found[0] = true;
                        }
                    }
                };
            }
        }, ClassReader.SKIP_DEBUG | ClassReader.SKIP_FRAMES);
        return found[0];
    }
}

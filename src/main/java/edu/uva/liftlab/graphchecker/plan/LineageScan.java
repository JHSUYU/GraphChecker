package edu.uva.liftlab.graphchecker.plan;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.List;

public final class LineageScan {
    private LineageScan() {
    }

    public static void main(String[] args) throws IOException {
        if (args.length < 3) {
            throw new IllegalArgumentException("usage: LineageScan <out-dir> "
                    + "<analysed-dirs> <class-root>[#<class>]...");
        }
        Path out = Paths.get(args[0]);
        List<Path> analysed = new ArrayList<>();
        for (String dir : args[1].split(java.util.regex.Pattern.quote(
                java.io.File.pathSeparator))) {
            if (!dir.isEmpty()) analysed.add(Paths.get(dir));
        }
        int scanned = 0;
        int kept = 0;
        for (int index = 2; index < args.length; index++) {
            String[] named = args[index].split("#", 2);
            Path root = Paths.get(named[0]);
            String family = named.length < 2 ? null
                    : named[1].replace('.', '/');
            if (!Files.isDirectory(root)) {
                throw new IllegalStateException(
                        "lineage class root not found: " + root);
            }
            Path walked = family == null || family.indexOf('/') < 0 ? root
                    : root.resolve(family.substring(0,
                    family.lastIndexOf('/')));
            if (!Files.isDirectory(walked)) continue;
            for (Path file : ArtifactIO.classFiles(walked)) {
                Path relative = root.relativize(file);
                if (family != null && !ofFamily(relative, family)) continue;
                scanned++;
                if (analysed.stream().anyMatch(dir
                        -> Files.exists(dir.resolve(relative)))) {
                    continue;
                }
                if (!handsOffWork(file)) continue;
                Path target = out.resolve(relative);
                Files.createDirectories(target.getParent());
                Files.copy(file, target, StandardCopyOption.REPLACE_EXISTING);
                kept++;
            }
        }
        System.out.println("lineage scope: " + kept + " of " + scanned
                + " class(es) start, hand off, run, wait, signal or draw"
                + " outside the analysis scope");
    }

    static boolean ofFamily(Path relative, String family) {
        String name = relative.toString().replace(
                java.io.File.separatorChar, '/');
        return name.equals(family + ".class")
                || name.startsWith(family + "$") && name.endsWith(".class");
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
                                || WorkStartSites.draws(owner, callee,
                                        calleeDescriptor)
                                || WorkStartSites.lists(owner, callee,
                                        calleeDescriptor)) {
                            found[0] = true;
                        }
                    }
                };
            }
        }, ClassReader.SKIP_DEBUG | ClassReader.SKIP_FRAMES);
        return found[0];
    }
}

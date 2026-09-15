package edu.uva.liftlab.graphchecker.causynth;

import java.io.File;
import java.io.IOException;
import java.lang.management.ManagementFactory;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * The INSTRUMENT stage's verifier gate: every class the weave wrote links and
 * verifies, here, before a replay JVM is asked to run it.
 *
 * <p>The JVM verifier is the authority on whether woven bytecode is
 * executable, and it used to be consulted for the first time inside a replay
 * -- hdfs-17960's woven {@code FSNamesystem} was refused with {@code
 * VerifyError: get long/double overflows locals} at {@code
 * allowSnapshot(Ljava/lang/String;)V @142: lload_2}, which ended the seed
 * replay before any region ran and was reported as a failed JUnit method.
 * This main asks the same verifier the same question in the stage that wrote
 * the classes, so the answer names the class, the method and the reason.</p>
 *
 * <p>The class loader is the replay's own layout: the woven tree first, the
 * engine jar (this process's own classpath, the loader's parent) next, and
 * the case classpath last, which is how {@code execute.sh} composes {@code
 * ${classes}:${jar}:${cp}}.  A woven class therefore resolves its hooks and
 * its unwoven neighbours exactly as it will at replay.  Loading is enough to
 * verify: {@code Class.forName(name, false, loader)} leaves the class
 * uninitialized -- no workload static initializer runs -- and the reflective
 * read that follows links it, which is what runs the verifier.</p>
 *
 * <p>Usage: {@code VerifyWovenClasses <instrumented-classes-dir>
 * [<classpath>]}.  Exit 0 when every class verified, 1 when one did not, 2
 * when the gate could not ask the question.</p>
 */
public final class VerifyWovenClasses {
    private VerifyWovenClasses() {
    }

    public static void main(String[] args) {
        if (args.length < 1 || args.length > 2) {
            refuse("usage: VerifyWovenClasses <instrumented-classes-dir> "
                    + "[<classpath>]");
        }
        // A verifier the JVM was told to skip answers every question with
        // "fine", which is the one answer this gate must never report.
        for (String argument : ManagementFactory.getRuntimeMXBean()
                .getInputArguments()) {
            if ("-Xverify:none".equals(argument)
                    || "-noverify".equals(argument)) {
                refuse("bytecode verification is disabled by " + argument
                        + ": this gate cannot verify anything");
            }
        }
        Path classes = Paths.get(args[0]);
        if (!Files.isDirectory(classes)) {
            refuse("instrumented classes directory not found: " + classes);
        }
        List<Path> files;
        try {
            files = classFiles(classes);
        } catch (IOException failure) {
            refuse("could not read the instrumented classes directory "
                    + classes + ": " + failure);
            return;
        }
        if (files.isEmpty()) {
            refuse("no class file under " + classes);
        }
        ClassLoader loader;
        try {
            loader = replayLoader(classes, args.length > 1 ? args[1] : "");
        } catch (MalformedURLException failure) {
            refuse("could not compose the replay classpath: " + failure);
            return;
        }
        int verified = 0;
        List<String> failures = new ArrayList<>();
        String firstDetail = null;
        for (Path file : files) {
            String name = binaryName(classes, file);
            try {
                Class.forName(name, false, loader).getDeclaredMethods();
                verified++;
            } catch (LinkageError | ClassNotFoundException | RuntimeException
                    error) {
                String message = String.valueOf(error.getMessage());
                failures.add(name + ": " + error.getClass().getName()
                        + " at " + location(message) + ": "
                        + reason(message));
                if (firstDetail == null) {
                    firstDetail = name + "\n" + message;
                }
            }
        }
        if (!failures.isEmpty()) {
            System.out.println("verified " + verified + " of " + files.size()
                    + " woven class(es) under " + classes);
            for (String failure : failures) {
                System.out.println("UNVERIFIABLE " + failure);
            }
            System.out.println("first failure in full:\n" + firstDetail);
            System.exit(1);
        }
        System.out.println("verified " + verified + " woven class(es) under "
                + classes + "; the JVM verifier rejected none");
    }

    private static void refuse(String reason) {
        System.out.println("VERIFY_WOVEN_CLASSES_REFUSED: " + reason);
        System.exit(2);
    }

    /** Every class file under {@code root}, in a stable order. */
    private static List<Path> classFiles(Path root) throws IOException {
        List<Path> files = new ArrayList<>();
        Files.walkFileTree(root, new SimpleFileVisitor<Path>() {
            @Override
            public FileVisitResult visitFile(Path file,
                                             BasicFileAttributes attributes) {
                if (file.getFileName().toString().endsWith(".class")) {
                    files.add(file);
                }
                return FileVisitResult.CONTINUE;
            }
        });
        Collections.sort(files);
        return files;
    }

    /** The replay's class loading layout, woven tree first. */
    private static ClassLoader replayLoader(Path classes, String classpath)
            throws MalformedURLException {
        List<URL> urls = new ArrayList<>();
        urls.add(classes.toUri().toURL());
        for (String entry : classpath.split(File.pathSeparator)) {
            if (entry.trim().isEmpty()) continue;
            urls.add(new File(entry).toURI().toURL());
        }
        return new URLClassLoader(urls.toArray(new URL[0]),
                VerifyWovenClasses.class.getClassLoader());
    }

    private static String binaryName(Path root, Path file) {
        String relative = root.relativize(file).toString();
        return relative.substring(0, relative.length() - ".class".length())
                .replace(File.separatorChar, '.');
    }

    /** The method and offset a {@code VerifyError} names, or "-". */
    private static String location(String message) {
        return lineAfter(message, "Location:");
    }

    /** The reason a {@code VerifyError} names, or its own first line. */
    private static String reason(String message) {
        String reason = lineAfter(message, "Reason:");
        return "-".equals(reason) ? message.split("\n")[0].trim() : reason;
    }

    private static String lineAfter(String message, String header) {
        String[] lines = message.split("\n");
        for (int index = 0; index < lines.length - 1; index++) {
            if (lines[index].trim().equals(header)) {
                return lines[index + 1].trim();
            }
        }
        return "-";
    }
}

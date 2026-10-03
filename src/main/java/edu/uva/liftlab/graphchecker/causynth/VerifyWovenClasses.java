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
 * The INSTRUMENT stage's verifier gate: every woven class links and verifies
 * here, not first inside a replay.
 *
 * <p>The loader mirrors {@code execute.sh}'s {@code ${classes}:${jar}:${cp}}.
 * {@code Class.forName(name, false, loader)} runs no static initializer; the
 * reflective read after it links the class, which runs the verifier.  A
 * class that cannot link because a class it names is on no classpath (and
 * is none of the engine's) cannot load in the workload either, woven or not
 * -- the lineage scope is a system's whole class roots, and a ZooKeeper
 * recipe's test lacks the server's Jetty console, which it falls back
 * from -- so it is counted UNLOADABLE by name, not refused.</p>
 *
 * <p>Usage: {@code VerifyWovenClasses <instrumented-classes-dir>
 * [<classpath>]}.  Exit 0 all verified, 1 one did not, 2 could not ask.</p>
 */
public final class VerifyWovenClasses {
    private VerifyWovenClasses() {
    }

    public static void main(String[] args) {
        if (args.length < 1 || args.length > 2) {
            refuse("usage: VerifyWovenClasses <instrumented-classes-dir> "
                    + "[<classpath>]");
        }
        // A disabled verifier answers "fine" to everything.
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
        List<String> unloadable = new ArrayList<>();
        String firstDetail = null;
        for (Path file : files) {
            String name = binaryName(classes, file);
            try {
                Class.forName(name, false, loader).getDeclaredMethods();
                verified++;
            } catch (LinkageError | ClassNotFoundException | RuntimeException
                    error) {
                String message = String.valueOf(error.getMessage());
                if (unloadable(loader, error)) {
                    unloadable.add(name + ": " + message.trim()
                            + " is on no classpath");
                    continue;
                }
                failures.add(name + ": " + error.getClass().getName()
                        + " at " + location(message) + ": "
                        + reason(message));
                if (firstDetail == null) {
                    firstDetail = name + "\n" + message;
                }
            }
        }
        System.out.println("verified " + verified + " of " + files.size()
                + " woven class(es) under " + classes + "; "
                + unloadable.size() + " cannot load in this workload");
        for (String each : unloadable) {
            System.out.println("UNLOADABLE " + each);
        }
        if (!failures.isEmpty()) {
            for (String failure : failures) {
                System.out.println("UNVERIFIABLE " + failure);
            }
            System.out.println("first failure in full:\n" + firstDetail);
            System.exit(1);
        }
    }

    /** The engine's own classes: one a woven hook names is never missing. */
    private static final String ENGINE = "edu/uva/liftlab/graphchecker/";

    /**
     * Whether {@code error} is a link failure on a class neither the woven
     * tree nor the classpath holds, other than the engine's: the workload
     * cannot load the failing class either, so its weave is not in question.
     */
    static boolean unloadable(ClassLoader loader, Throwable error) {
        if (!(error instanceof NoClassDefFoundError)) return false;
        String missing = String.valueOf(error.getMessage()).trim()
                .replace('.', '/');
        return !missing.isEmpty() && !missing.contains(" ")
                && !missing.startsWith(ENGINE)
                && loader.getResource(missing + ".class") == null;
    }

    private static void refuse(String reason) {
        System.out.println("VERIFY_WOVEN_CLASSES_REFUSED: " + reason);
        System.exit(2);
    }

    /** Every class file under {@code root}, in a stable order. */
    static List<Path> classFiles(Path root) throws IOException {
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

    static String binaryName(Path root, Path file) {
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

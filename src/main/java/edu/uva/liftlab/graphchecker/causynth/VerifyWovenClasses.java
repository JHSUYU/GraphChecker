package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.File;
import java.io.IOException;
import java.lang.management.ManagementFactory;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

/**
 * The INSTRUMENT stage's verifier gate: every woven class links and verifies
 * here, not first inside a replay.
 *
 * <p>The loader mirrors {@code execute.sh}'s {@code ${classes}:${jar}:${cp}}.
 * {@code Class.forName(name, false, loader)} runs no static initializer; the
 * reflective read after it links the class, which runs the verifier.</p>
 *
 * <p>The gate judges the weave.  A woven class that fails as the class the
 * classpath holds fails unwoven -- the same throwable with the same message,
 * or both a {@code NoClassDefFoundError} for types no entry of the layout
 * holds (Jetty, for ZooKeeper's admin server under a recipe's workload; which
 * missing type linking meets first depends on the method order, which the
 * weave rewrites) -- is a class the workload cannot link either way: it is
 * listed {@code UNLINKED}, and does not fail the gate.</p>
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
            files = ArtifactIO.classFiles(classes);
        } catch (IOException failure) {
            refuse("could not read the instrumented classes directory "
                    + classes + ": " + failure);
            return;
        }
        if (files.isEmpty()) {
            refuse("no class file under " + classes);
        }
        ClassLoader loader;
        ClassLoader built;
        try {
            String classpath = args.length > 1 ? args[1] : "";
            loader = replayLoader(classes, classpath);
            built = replayLoader(null, classpath);
        } catch (MalformedURLException failure) {
            refuse("could not compose the replay classpath: " + failure);
            return;
        }
        int verified = 0;
        List<String> failures = new ArrayList<>();
        List<String> unlinked = new ArrayList<>();
        String firstDetail = null;
        for (Path file : files) {
            String name = binaryName(classes, file);
            Throwable error = linkError(name, loader);
            if (error == null) {
                verified++;
                continue;
            }
            String message = String.valueOf(error.getMessage());
            String failure = name + ": " + error.getClass().getName()
                    + " at " + location(message) + ": " + reason(message);
            if (failsAlike(error, name, built, loader)) {
                unlinked.add(failure);
                continue;
            }
            failures.add(failure);
            if (firstDetail == null) {
                firstDetail = name + "\n" + message;
            }
        }
        for (String failure : unlinked) {
            System.out.println("UNLINKED " + failure
                    + " (the class the classpath holds fails alike)");
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
                + classes + "; the JVM verifier rejected none"
                + (unlinked.isEmpty() ? "" : "; " + unlinked.size()
                + " class(es) link on this classpath neither woven nor as built"));
    }

    /** Why {@code name} does not load and link from {@code loader}, or null. */
    private static Throwable linkError(String name, ClassLoader loader) {
        try {
            Class.forName(name, false, loader).getDeclaredMethods();
            return null;
        } catch (LinkageError | ClassNotFoundException | RuntimeException
                error) {
            return error;
        }
    }

    /**
     * Whether the class the classpath itself holds under {@code name} fails
     * to link as its woven copy did: the same throwable class, and the same
     * message or, both missing a class, types that no entry of the woven
     * layout ({@code loader}) holds.  A class the classpath does not hold is
     * the weave's alone.
     */
    private static boolean failsAlike(Throwable woven, String name,
                                      ClassLoader built, ClassLoader loader) {
        if (built.getResource(resource(name)) == null) return false;
        Throwable original = linkError(name, built);
        if (original == null || !original.getClass().equals(woven.getClass())) {
            return false;
        }
        String wovenMessage = String.valueOf(woven.getMessage());
        String originalMessage = String.valueOf(original.getMessage());
        return wovenMessage.equals(originalMessage)
                || woven instanceof NoClassDefFoundError
                && loader.getResource(resource(wovenMessage)) == null
                && loader.getResource(resource(originalMessage)) == null;
    }

    /** The class file of a binary or internal class name. */
    private static String resource(String name) {
        return name.replace('.', '/') + ".class";
    }

    private static void refuse(String reason) {
        System.out.println("VERIFY_WOVEN_CLASSES_REFUSED: " + reason);
        System.exit(2);
    }

    /** The replay's class loading layout, the woven tree (if any) first. */
    private static ClassLoader replayLoader(Path classes, String classpath)
            throws MalformedURLException {
        List<URL> urls = new ArrayList<>();
        if (classes != null) urls.add(classes.toUri().toURL());
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

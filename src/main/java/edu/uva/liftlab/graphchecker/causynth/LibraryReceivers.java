package edu.uva.liftlab.graphchecker.causynth;

import soot.Local;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.FieldRef;
import soot.jimple.IdentityStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.ThisRef;

import java.io.File;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Predicate;
import java.util.regex.Pattern;
import java.util.zip.ZipFile;

final class LibraryReceivers {
    static final String ROOTS = "causynth.lineage.roots";
    private static final String[] STATELESS = {
        "org.slf4j.", "org.apache.log4j.", "org.apache.logging.",
        "org.apache.commons.logging.", "java.util.logging.",
    };

    private LibraryReceivers() {
    }

    static boolean stateful(String owner, String name) {
        if ("java.lang.Object".equals(owner)
                || "java.lang.Class".equals(owner)
                || "getClass".equals(name) || "hashCode".equals(name)
                || "toString".equals(name)) {
            return false;
        }
        for (String prefix : STATELESS) {
            if (owner.startsWith(prefix)) return false;
        }
        for (String segment : owner.split("\\.")) {
            if ("metrics".equals(segment) || "metrics2".equals(segment)) {
                return false;
            }
        }
        return true;
    }

    static Predicate<String> systemClasses(String roots) {
        if (roots == null || roots.trim().isEmpty()) {
            throw new IllegalStateException("-D" + ROOTS + " names no class"
                    + " root of the system, so a class outside the scope"
                    + " cannot be told from a library and no library"
                    + " call's receiver may be read (SYMBOL-SCOPE §2.2)");
        }
        List<Predicate<String>> holders = new ArrayList<>();
        for (String root : roots.split(Pattern.quote(File.pathSeparator))) {
            if (!root.trim().isEmpty()) {
                holders.add(holder(Paths.get(root.trim())));
            }
        }
        Map<String, Boolean> asked = new ConcurrentHashMap<>();
        return owner -> asked.computeIfAbsent(owner, name -> {
            String file = name.replace('.', '/') + ".class";
            for (Predicate<String> holder : holders) {
                if (holder.test(file)) return true;
            }
            return false;
        });
    }

    private static Predicate<String> holder(Path root) {
        if (Files.isDirectory(root)) {
            return file -> Files.isRegularFile(root.resolve(file));
        }
        if (!Files.isRegularFile(root)) {
            throw new IllegalStateException("system class root not found: "
                    + root);
        }
        Set<String> entries = ConcurrentHashMap.newKeySet();
        try (ZipFile jar = new ZipFile(root.toFile())) {
            jar.stream().forEach(entry -> entries.add(entry.getName()));
        } catch (IOException unreadable) {
            throw new UncheckedIOException(unreadable);
        }
        return Collections.unmodifiableSet(entries)::contains;
    }

    static boolean shared(List<Unit> units, int index, Local local,
                          Predicate<InvokeExpr> accessor) {
        Local wanted = local;
        for (int at = index - 1; at >= 0; at--) {
            Unit unit = units.get(at);
            if (unit instanceof IdentityStmt
                    && ((IdentityStmt) unit).getLeftOp() == wanted) {
                return ((IdentityStmt) unit).getRightOp() instanceof ThisRef;
            }
            if (!(unit instanceof AssignStmt)
                    || ((AssignStmt) unit).getLeftOp() != wanted) {
                continue;
            }
            Value right = ((AssignStmt) unit).getRightOp();
            if (right instanceof CastExpr) right = ((CastExpr) right).getOp();
            if (right instanceof Local) {
                wanted = (Local) right;
                continue;
            }
            return right instanceof FieldRef
                    || right instanceof InvokeExpr
                    && accessor.test((InvokeExpr) right);
        }
        return false;
    }
}

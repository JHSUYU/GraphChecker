package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.explore.Corpus;
import edu.uva.liftlab.graphchecker.explore.SlotTable;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.InvalidPathException;
import java.nio.file.NoSuchFileException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

final class CompositionInputs {
    static final String FILE = "compose_inputs.sha256";

    private CompositionInputs() {
    }

    static String of(ComposeMain.Arguments arguments) throws IOException {
        return ArtifactIO.sha256(String.join("\n", lines(arguments)));
    }

    static String of(Path dir) throws IOException {
        Path file = dir.resolve(FILE);
        if (!Files.isRegularFile(file)) return "";
        return new String(Files.readAllBytes(file), StandardCharsets.UTF_8)
                .trim();
    }

    static List<String> lines(ComposeMain.Arguments arguments)
            throws IOException {
        List<String> lines = new ArrayList<String>();
        text(lines, "anchor", arguments.anchor);
        file(lines, "root-domains", arguments.rootDomains);
        file(lines, "static-scope-map", arguments.scopeMap);
        text(lines, "max-valuations",
                Integer.toString(arguments.maxValuations));
        text(lines, "solver-timeout-ms",
                Long.toString(arguments.timeoutMillis));
        text(lines, "z3", arguments.z3 == null ? ""
                : arguments.z3.toString());
        for (String name : new TreeSet<String>(
                System.getProperties().stringPropertyNames())) {
            if (!name.startsWith("causynth.")) continue;
            String value = System.getProperty(name);
            text(lines, "property " + name, value);
            Path named = path(value);
            if (named != null && Files.isRegularFile(named)) {
                file(lines, "property-file " + name, named);
            }
        }
        Path iteration = arguments.iteration;
        file(lines, Corpus.RECORDED_SCHEDULE,
                iteration.resolve(Corpus.RECORDED_SCHEDULE));
        file(lines, Refutations.FILE, iteration.resolve(Refutations.FILE));
        file(lines, SessionDir.UNCAPTURED,
                iteration.resolve(SessionDir.UNCAPTURED));
        for (Path slots : SlotTable.files(iteration)) {
            file(lines, "slots " + iteration.relativize(slots), slots);
        }
        Set<String> sessions = new TreeSet<String>();
        for (SessionDir session : SessionDir.sessionsIn(iteration)) {
            String id = session.sessionId();
            sessions.add(id);
            text(lines, "session", id);
            List<Path> files = new ArrayList<Path>();
            try (Stream<Path> listed = Files.list(session.dir())) {
                listed.sorted().forEach(files::add);
            } catch (NoSuchFileException gone) {
                lines.add("session-gone " + id);
                continue;
            }
            for (Path entry : files) {
                lines.add("session-file " + id + "/" + entry.getFileName()
                        + "\t" + (Files.isDirectory(entry) ? "directory"
                        : Long.toString(Files.size(entry))));
            }
            file(lines, "session-manifest " + id,
                    session.dir().resolve(SessionDir.MANIFEST));
        }
        for (ObligationDir worker : ObligationDir.workersIn(iteration)) {
            if (!sessions.contains(worker.sessionId())) continue;
            String name = worker.dir().getParent().getFileName() + "/"
                    + worker.dir().getFileName();
            text(lines, "worker " + name, worker.sessionId());
            file(lines, "worker-result " + name,
                    worker.dir().resolve(ObligationDir.RESULT));
            file(lines, "worker-focus " + name,
                    worker.dir().resolve(ObligationDir.FOCUSED_TASK));
        }
        return lines;
    }

    private static void text(List<String> lines, String name, String value) {
        lines.add(name + "\t" + ArtifactIO.sha256(value));
    }

    private static void file(List<String> lines, String name, Path file)
            throws IOException {
        String digest = "absent";
        if (file != null && Files.isRegularFile(file)) {
            try {
                digest = ArtifactIO.sha256(file);
            } catch (NoSuchFileException gone) {
            }
        }
        lines.add(name + "\t" + digest);
    }

    private static Path path(String value) {
        try {
            return value == null || value.isEmpty() ? null : Paths.get(value);
        } catch (InvalidPathException none) {
            return null;
        }
    }
}

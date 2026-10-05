package edu.uva.liftlab.graphchecker.smt;


import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.stream.Stream;
import java.util.zip.GZIPInputStream;

/**
 * Schema-free file operations shared by concolic command boundaries.
 */
public final class ArtifactIO {
    private static final char[] HEX = "0123456789abcdef".toCharArray();

    private ArtifactIO() {
    }

    public static List<JsonObject> readJsonl(Path path) throws IOException {
        if (path == null || !Files.isRegularFile(path)) {
            throw new IOException("JSONL input not found: " + path);
        }
        return readJsonl(path, "Malformed JSONL %1$s:%2$d",
                "Non-object JSONL row %1$s:%2$d");
    }

    public static List<JsonObject> readJsonl(Path path,
                                             String malformedFormat,
                                             String nonObjectFormat)
            throws IOException {
        List<JsonObject> result = new ArrayList<>();
        try (BufferedReader reader = jsonlReader(path)) {
            String line;
            int number = 0;
            while ((line = reader.readLine()) != null) {
                number++;
                if (line.trim().isEmpty()) continue;
                JsonElement parsed;
                try {
                    parsed = JsonParser.parseString(line);
                } catch (RuntimeException malformed) {
                    throw new IOException(format(malformedFormat, path,
                            number), malformed);
                }
                if (!parsed.isJsonObject()) {
                    throw new IOException(format(nonObjectFormat, path,
                            number));
                }
                result.add(parsed.getAsJsonObject());
            }
        }
        return result;
    }

    private static BufferedReader jsonlReader(Path path) throws IOException {
        InputStream input = Files.newInputStream(path);
        try {
            if (path.getFileName().toString().endsWith(".gz")) {
                input = new GZIPInputStream(input);
            }
            return new BufferedReader(new InputStreamReader(input,
                    StandardCharsets.UTF_8));
        } catch (IOException failure) {
            input.close();
            throw failure;
        }
    }

    /**
     * One artifact write: a temporary sibling, then one atomic move, so no
     * reader sees a partial write and a failure keeps the old artifact.  The
     * one staging envelope in the repository.
     */
    public static void atomicReplace(Path path, Body body)
            throws IOException {
        Path absolute = path.toAbsolutePath().normalize();
        Path parent = absolute.getParent();
        if (parent != null) Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent,
                "artifact-" + absolute.getFileName(), ".tmp");
        try {
            try (BufferedWriter output = Files.newBufferedWriter(temporary,
                    StandardCharsets.UTF_8)) {
                body.writeTo(output);
            }
            try {
                Files.move(temporary, path,
                        StandardCopyOption.ATOMIC_MOVE,
                        StandardCopyOption.REPLACE_EXISTING);
            } catch (AtomicMoveNotSupportedException unsupported) {
                Files.move(temporary, path,
                        StandardCopyOption.REPLACE_EXISTING);
            }
        } catch (IOException | RuntimeException | Error failure) {
            // Failure path only: cleanup must not mask the real error.
            try {
                Files.deleteIfExists(temporary);
            } catch (IOException cleanup) {
                failure.addSuppressed(cleanup);
            }
            throw failure;
        }
    }

    /** What one artifact's bytes are, given the staged file to write them to. */
    public interface Body {
        void writeTo(BufferedWriter output) throws IOException;
    }

    public static void replace(Path path, String value) throws IOException {
        atomicReplace(path, output -> output.write(value));
    }

    public static void replaceJsonl(Path path, Iterable<JsonObject> rows)
            throws IOException {
        atomicReplace(path, output -> {
            if (rows != null) {
                for (JsonObject row : rows) {
                    output.write(row.toString());
                    output.newLine();
                }
            }
        });
    }

    public static String sha256(Path path) throws IOException {
        MessageDigest digest = digest();
        byte[] buffer = new byte[8192];
        try (InputStream input = Files.newInputStream(path)) {
            int read;
            while ((read = input.read(buffer)) >= 0) {
                if (read > 0) digest.update(buffer, 0, read);
            }
        }
        return hex(digest.digest());
    }

    public static String sha256(String value) {
        return hex(digest().digest((value == null ? "" : value)
                .getBytes(StandardCharsets.UTF_8)));
    }

    /**
     * The one id spelling (CONTRACT-SPEC): lowercase hex sha256, truncated
     * to {@code length} characters ({@code <= 0} or past the end means
     * untruncated).  Every stage mints ids here.
     */
    public static String digest(String value, int length) {
        String full = sha256(value);
        return length <= 0 || length >= full.length()
                ? full : full.substring(0, length);
    }

    /** Every class file under {@code root}, in path order. */
    public static List<Path> classFiles(Path root) throws IOException {
        List<Path> files = new ArrayList<>();
        try (Stream<Path> walk = Files.walk(root)) {
            walk.filter(path -> Files.isRegularFile(path)
                            && path.getFileName().toString().endsWith(".class"))
                    .sorted().forEach(files::add);
        }
        return files;
    }

    public static Path sibling(Path path, String name) {
        Path parent = path.toAbsolutePath().getParent();
        return parent == null ? Paths.get(name) : parent.resolve(name);
    }

    private static MessageDigest digest() {
        try {
            return MessageDigest.getInstance("SHA-256");
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException(impossible);
        }
    }

    private static String hex(byte[] hash) {
        char[] encoded = new char[hash.length * 2];
        for (int index = 0; index < hash.length; index++) {
            int value = hash[index] & 0xff;
            encoded[index * 2] = HEX[value >>> 4];
            encoded[index * 2 + 1] = HEX[value & 0x0f];
        }
        return new String(encoded);
    }

    private static String format(String pattern, Path path, int line) {
        return String.format(Locale.ROOT, pattern, path, line);
    }
}

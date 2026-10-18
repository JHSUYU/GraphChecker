package edu.uva.liftlab.graphchecker.smt;


import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.BufferedInputStream;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.ByteArrayOutputStream;
import java.io.EOFException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.UncheckedIOException;
import java.nio.ByteBuffer;
import java.nio.channels.SeekableByteChannel;
import java.nio.charset.StandardCharsets;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Locale;
import java.util.stream.Stream;
import java.util.zip.Deflater;
import java.util.zip.GZIPInputStream;
import java.util.zip.GZIPOutputStream;
import java.util.zip.ZipException;

/**
 * Schema-free file operations shared by concolic command boundaries.
 */
public final class ArtifactIO {
    private static final char[] HEX = "0123456789abcdef".toCharArray();
    /** The SHA-256 every digest is a clone of ({@link #digest()}). */
    private static final MessageDigest SHA256 = sha256Instance();

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
        return new BufferedReader(new InputStreamReader(input(path),
                StandardCharsets.UTF_8));
    }

    // ---- gzip: the one opener -------------------------------------------

    /** A file whose name ends so is one gzip stream (or several members of
     *  one, RFC 1952 §2.2): every reader and writer here takes its bytes as
     *  they decode (CONTRACT-SPEC §2.1-2.2). */
    public static final String GZIP = ".gz";
    /**
     * The level every gzip stream here is written at: zlib's default.  In the
     * replay's interpreted VM the level costs nothing beside the stream's own
     * interpreted plumbing -- SGF7-adhoc-40's 172 MB session written a row a
     * flush: 45.8 s of CPU plain, 51.6 at level 1, 52.1 at 6 -- and level 6
     * writes 26 % fewer bytes (12.8x -> 17.3x; a planner round's files 20x
     * -> 39x, deflated on every core).
     */
    private static final int GZIP_LEVEL = Deflater.DEFAULT_COMPRESSION;
    /** How many bytes a gzip stream here buffers, either way. */
    private static final int GZIP_BUFFER = 1 << 16;
    /** The four bytes a sync flush ends with ({@link #appending}). */
    private static final byte[] SYNC_TAIL = {0, 0, (byte) 0xff, (byte) 0xff};

    /** Whether {@code file} is named a gzip stream ({@link #GZIP}). */
    public static boolean gzipped(Path file) {
        Path name = file == null ? null : file.getFileName();
        return name != null && name.toString().endsWith(GZIP);
    }

    /**
     * THE ONE OPENER: the bytes a file holds as its readers take them -- a
     * gzip file's decoded ({@link #GZIP}).  A gzip stream its writer never
     * finished reads as far as it was written, as a plain file cut there
     * reads: a replay killed before its close leaves each row stream ending
     * at its last flush ({@link #appending}), a whole row, and one killed
     * inside a write leaves a cut line for its reader to refuse, as a cut
     * plain file's.  A file that holds no gzip stream, or a damaged one,
     * fails its read ({@link UncheckedIOException}, as a malformed row does).
     */
    public static InputStream input(Path file) throws IOException {
        InputStream bytes = new BufferedInputStream(Files.newInputStream(file),
                GZIP_BUFFER);
        return gzipped(file) ? new Decoded(bytes, file) : bytes;
    }

    /**
     * The UTF-8 lines of {@link #input}, malformed text refused as {@code
     * Files#newBufferedReader} refuses it.
     */
    public static BufferedReader lines(Path file) throws IOException {
        return new BufferedReader(new InputStreamReader(input(file),
                StandardCharsets.UTF_8.newDecoder()), GZIP_BUFFER);
    }

    /**
     * One gzip member of {@code text}, whole: members written one after
     * another are one gzip file, so a file's runs are deflated side by side
     * and written in order ({@code contract.RowCodec#writeAll}).
     */
    public static byte[] gzip(byte[] text) throws IOException {
        ByteArrayOutputStream member = new ByteArrayOutputStream(
                text.length / 8 + 64);
        try (OutputStream out = new Encoder(member, false)) {
            out.write(text);
        }
        return member.toByteArray();
    }

    /**
     * A file one writer appends to as its rows come ({@code
     * runtime.SessionPublisher}), each {@code flush} on disk whole: a gzip
     * file's stream ends every flush at a sync point, its dictionary kept,
     * so what was flushed decodes whether or not the stream is ever finished
     * ({@code close} finishes it).  java.io, never a channel: the runtime
     * writes from workload threads, and a channel on a thread the program
     * interrupts closes truncating ({@code RowCodec#writeObject}).
     */
    public static OutputStream appending(Path file) throws IOException {
        OutputStream bytes = new FileOutputStream(file.toFile(), true);
        if (!gzipped(file)) return bytes;
        try {
            return new Encoder(bytes, true);
        } catch (IOException | RuntimeException refused) {
            bytes.close();
            throw refused;
        }
    }

    /**
     * The bytes a reader of {@code file} meets ({@link #input}): a plain
     * file's size; a gzip file of one stream the count its trailer states
     * (mod 2^32), or, never finished (it ends at a sync point, or before a
     * whole member), the bytes it decodes to.  What a session's rows weigh
     * in a heap is their decoded text ({@code
     * explore.ObligationSolverMain#bytes}).
     */
    public static long decodedSize(Path file) throws IOException {
        long size = Files.size(file);
        if (!gzipped(file)) return size;
        byte[] tail = new byte[4];
        if (size >= 20) {
            try (SeekableByteChannel channel = Files.newByteChannel(file)) {
                channel.position(size - tail.length);
                ByteBuffer read = ByteBuffer.wrap(tail);
                while (read.hasRemaining() && channel.read(read) >= 0) {
                    // Fills the trailer's count.
                }
            }
        }
        if (size < 20 || Arrays.equals(tail, SYNC_TAIL)) {
            long decoded = 0L;
            byte[] buffer = new byte[GZIP_BUFFER];
            try (InputStream in = input(file)) {
                int read;
                while ((read = in.read(buffer)) >= 0) decoded += read;
            }
            return decoded;
        }
        return (tail[0] & 0xffL) | (tail[1] & 0xffL) << 8
                | (tail[2] & 0xffL) << 16 | (tail[3] & 0xffL) << 24;
    }

    /** A gzip stream at {@link #GZIP_LEVEL}. */
    private static final class Encoder extends GZIPOutputStream {
        Encoder(OutputStream out, boolean syncFlush) throws IOException {
            super(out, GZIP_BUFFER, syncFlush);
            def.setLevel(GZIP_LEVEL);
        }
    }

    /**
     * A gzip file's bytes decoded ({@link #input}), ending where its stream
     * ends or where its writer stopped: the decoder's end of input (an
     * {@link EOFException}, which it raises only once every byte that
     * decodes was handed out) is the file's end, and so is an empty file or
     * one cut inside its header.  Opened at the first read.
     */
    private static final class Decoded extends InputStream {
        private final InputStream bytes;
        private final Path file;
        private GZIPInputStream decoder;
        private boolean ended;

        Decoded(InputStream bytes, Path file) {
            this.bytes = bytes;
            this.file = file;
        }

        @Override
        public int read() throws IOException {
            byte[] one = new byte[1];
            int read;
            while ((read = read(one, 0, 1)) == 0) {
                // A decoder hands out at least one byte or ends.
            }
            return read < 0 ? -1 : one[0] & 0xff;
        }

        @Override
        public int read(byte[] into, int offset, int length)
                throws IOException {
            if (ended) return -1;
            try {
                if (decoder == null) {
                    decoder = new GZIPInputStream(bytes, GZIP_BUFFER);
                }
                int read = decoder.read(into, offset, length);
                if (read < 0) ended = true;
                return read;
            } catch (EOFException cut) {
                ended = true;
                return -1;
            } catch (ZipException damaged) {
                throw new UncheckedIOException("malformed gzip stream in "
                        + file + ": " + damaged.getMessage(), damaged);
            }
        }

        @Override
        public void close() throws IOException {
            if (decoder != null) {
                decoder.close();
            } else {
                bytes.close();
            }
        }
    }

    /** One artifact written as text, UTF-8 ({@link #atomicWrite}). */
    public static void atomicReplace(Path path, Body body)
            throws IOException {
        atomicWrite(path, bytes -> {
            try (BufferedWriter output = new BufferedWriter(
                    new OutputStreamWriter(bytes,
                            StandardCharsets.UTF_8.newEncoder()))) {
                body.writeTo(output);
            }
        });
    }

    /**
     * One artifact write: a temporary sibling, then one atomic move, so no
     * reader sees a partial write and a failure keeps the old artifact.  The
     * one staging envelope in the repository.
     */
    public static void atomicWrite(Path path, Bytes body)
            throws IOException {
        Path absolute = path.toAbsolutePath().normalize();
        Path parent = absolute.getParent();
        if (parent != null) Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent,
                "artifact-" + absolute.getFileName(), ".tmp");
        try {
            try (OutputStream output = Files.newOutputStream(temporary)) {
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

    /** {@link Body}, for a writer of bytes. */
    public interface Bytes {
        void writeTo(OutputStream output) throws IOException;
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

    /** A fresh SHA-256, cloned from one never updated: {@code
     *  MessageDigest#getInstance} looks its provider up under the
     *  provider's lock, and the planner's keys, digested on every core,
     *  waited there (SGF8-adhoc-05 round 5: 28 s of waits past 10 ms in a
     *  33 s phase). */
    private static MessageDigest digest() {
        try {
            return (MessageDigest) SHA256.clone();
        } catch (CloneNotSupportedException impossible) {
            throw new IllegalStateException(impossible);
        }
    }

    private static MessageDigest sha256Instance() {
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

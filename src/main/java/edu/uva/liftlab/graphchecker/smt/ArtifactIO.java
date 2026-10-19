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

public final class ArtifactIO {
    private static final char[] HEX = "0123456789abcdef".toCharArray();
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


    public static final String GZIP = ".gz";
    private static final int GZIP_LEVEL = Deflater.DEFAULT_COMPRESSION;
    private static final int GZIP_BUFFER = 1 << 16;
    private static final byte[] SYNC_TAIL = {0, 0, (byte) 0xff, (byte) 0xff};

    public static boolean gzipped(Path file) {
        Path name = file == null ? null : file.getFileName();
        return name != null && name.toString().endsWith(GZIP);
    }

    public static InputStream input(Path file) throws IOException {
        InputStream bytes = new BufferedInputStream(Files.newInputStream(file),
                GZIP_BUFFER);
        return gzipped(file) ? new Decoded(bytes, file) : bytes;
    }

    public static BufferedReader lines(Path file) throws IOException {
        return new BufferedReader(new InputStreamReader(input(file),
                StandardCharsets.UTF_8.newDecoder()), GZIP_BUFFER);
    }

    public static byte[] gzip(byte[] text) throws IOException {
        ByteArrayOutputStream member = new ByteArrayOutputStream(
                text.length / 8 + 64);
        try (OutputStream out = new Encoder(member, false)) {
            out.write(text);
        }
        return member.toByteArray();
    }

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

    public static long decodedSize(Path file) throws IOException {
        long size = Files.size(file);
        if (!gzipped(file)) return size;
        byte[] tail = new byte[4];
        if (size >= 20) {
            try (SeekableByteChannel channel = Files.newByteChannel(file)) {
                channel.position(size - tail.length);
                ByteBuffer read = ByteBuffer.wrap(tail);
                while (read.hasRemaining() && channel.read(read) >= 0) {
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

    private static final class Encoder extends GZIPOutputStream {
        Encoder(OutputStream out, boolean syncFlush) throws IOException {
            super(out, GZIP_BUFFER, syncFlush);
            def.setLevel(GZIP_LEVEL);
        }
    }

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
            try {
                Files.deleteIfExists(temporary);
            } catch (IOException cleanup) {
                failure.addSuppressed(cleanup);
            }
            throw failure;
        }
    }

    public interface Body {
        void writeTo(BufferedWriter output) throws IOException;
    }

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
        MessageDigest digest = sha256Digest();
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
        return hex(sha256Digest().digest((value == null ? "" : value)
                .getBytes(StandardCharsets.UTF_8)));
    }

    public static String digest(String value, int length) {
        String full = sha256(value);
        return length <= 0 || length >= full.length()
                ? full : full.substring(0, length);
    }

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

    public static MessageDigest sha256Digest() {
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

    public static String hex(byte[] hash) {
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

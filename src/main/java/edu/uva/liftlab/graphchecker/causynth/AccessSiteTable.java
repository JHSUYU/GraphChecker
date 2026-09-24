package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.AccessSites;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.JvmNames;

import java.io.DataInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

/**
 * The VM site of every shared-access hook the replay weave put in, read off
 * the woven class files ({@link AccessSites}).
 *
 * <p>A hook is a static call placed immediately before one access statement
 * ({@code CausynthPipeline#instrumentSharedAccess}); its last argument is the
 * statement's woven site id, pushed by the instruction right before the call.
 * The access it stands before is the first field instruction or invocation
 * after it that is not the runtime's own -- a statement's operands are locals,
 * so nothing of the program runs between the hook and its access.  The row
 * states that instruction's bytecode index in the VM's spelling, which is the
 * index the VM logs the access at in every replay of these classes.</p>
 */
public final class AccessSiteTable {
    /** The class the replay weave binds every hook to. */
    static final String HOOK_OWNER =
            "edu/uva/liftlab/graphchecker/runtime/ConcolicRegionRuntime";
    static final String READ_HOOK = "sharedRead";
    static final String WRITE_HOOK = "sharedWrite";
    /** Calls the weave adds, which are never the access a hook guards. */
    private static final String RUNTIME_PREFIX =
            "edu/uva/liftlab/graphchecker/";
    private static final String SYSTEM = "java/lang/System";

    private AccessSiteTable() {
    }

    /** Writes the table beside the woven classes under {@code classes}. */
    public static int write(Path classes) throws IOException {
        Map<String, String> sites = new LinkedHashMap<String, String>();
        List<Path> files = new ArrayList<Path>();
        try (Stream<Path> walk = Files.walk(classes)) {
            walk.filter(path -> path.toString().endsWith(".class"))
                    .sorted().forEach(files::add);
        }
        for (Path file : files) {
            try (InputStream in = Files.newInputStream(file)) {
                sites.putAll(scan(in));
            }
        }
        AccessSites.write(classes, sites);
        return sites.size();
    }

    /** Woven site id -> VM site, for every access hook of one class file. */
    static Map<String, String> scan(InputStream stream) throws IOException {
        DataInputStream in = new DataInputStream(stream);
        if (in.readInt() != 0xCAFEBABE) {
            throw new IOException("not a class file");
        }
        in.readUnsignedShort();
        in.readUnsignedShort();
        Pool pool = new Pool(in);
        in.readUnsignedShort();
        String owner = pool.className(in.readUnsignedShort());
        in.readUnsignedShort();
        skip(in, in.readUnsignedShort() * 2);
        int fields = in.readUnsignedShort();
        for (int field = 0; field < fields; field++) {
            in.readUnsignedShort();
            in.readUnsignedShort();
            in.readUnsignedShort();
            skipAttributes(in);
        }
        Map<String, String> sites = new LinkedHashMap<String, String>();
        int methods = in.readUnsignedShort();
        for (int method = 0; method < methods; method++) {
            in.readUnsignedShort();
            String name = pool.utf8(in.readUnsignedShort());
            String descriptor = pool.utf8(in.readUnsignedShort());
            int attributes = in.readUnsignedShort();
            for (int attribute = 0; attribute < attributes; attribute++) {
                String kind = pool.utf8(in.readUnsignedShort());
                int length = in.readInt();
                if (!"Code".equals(kind)) {
                    skip(in, length);
                    continue;
                }
                byte[] body = new byte[length];
                in.readFully(body);
                code(body, pool, owner, name, descriptor, sites);
            }
        }
        return sites;
    }

    /** One method's code: every hook, and the access after it. */
    private static void code(byte[] attribute, Pool pool, String owner,
                             String method, String descriptor,
                             Map<String, String> sites) {
        int length = u4(attribute, 4);
        int base = 8;
        String pendingSite = null;
        boolean pendingWrite = false;
        String lastString = null;
        int pc = 0;
        while (pc < length) {
            int opcode = attribute[base + pc] & 0xFF;
            int size = size(attribute, base, pc, opcode);
            String loaded = null;
            if (opcode == 0x12) {
                loaded = pool.string(attribute[base + pc + 1] & 0xFF);
            } else if (opcode == 0x13) {
                loaded = pool.string(u2(attribute, base + pc + 1));
            }
            boolean field = opcode >= 0xB2 && opcode <= 0xB5;
            boolean invoke = opcode >= 0xB6 && opcode <= 0xB9;
            if (invoke) {
                String[] callee = pool.member(u2(attribute, base + pc + 1));
                boolean runtime = callee[0].startsWith(RUNTIME_PREFIX)
                        || SYSTEM.equals(callee[0]);
                if (opcode == 0xB8 && HOOK_OWNER.equals(callee[0])
                        && (READ_HOOK.equals(callee[1])
                        || WRITE_HOOK.equals(callee[1]))
                        && lastString != null) {
                    pendingSite = lastString;
                    pendingWrite = WRITE_HOOK.equals(callee[1]);
                } else if (!runtime && pendingSite != null) {
                    sites.put(pendingSite, site(owner, method, descriptor,
                            pc, pendingWrite));
                    pendingSite = null;
                }
            } else if (field && pendingSite != null) {
                sites.put(pendingSite, site(owner, method, descriptor, pc,
                        pendingWrite));
                pendingSite = null;
            }
            lastString = loaded;
            pc += size;
        }
    }

    /** The VM's spelling of one access site (runtime.LoggedEventSites). */
    private static String site(String owner, String method,
                               String descriptor, int bci, boolean write) {
        return Endpoint.stateSite(JvmNames.stable(owner).replace('/', '.'),
                method, descriptor, bci, write);
    }

    /** The length of the instruction at {@code pc} (JVMS 6.5). */
    private static int size(byte[] code, int base, int pc, int opcode) {
        switch (opcode) {
            case 0x10: case 0x12: case 0x15: case 0x16: case 0x17:
            case 0x18: case 0x19: case 0x36: case 0x37: case 0x38:
            case 0x39: case 0x3A: case 0xA9: case 0xBC:
                return 2;
            case 0x11: case 0x13: case 0x14: case 0x84: case 0xB2:
            case 0xB3: case 0xB4: case 0xB5: case 0xB6: case 0xB7:
            case 0xB8: case 0xBB: case 0xBD: case 0xC0: case 0xC1:
            case 0xC6: case 0xC7:
                return 3;
            case 0xC5:
                return 4;
            case 0xB9: case 0xBA: case 0xC8: case 0xC9:
                return 5;
            case 0xC4:
                return (code[base + pc + 1] & 0xFF) == 0x84 ? 6 : 4;
            case 0xAA: {
                int at = pc + 1 + pad(pc);
                int low = u4(code, base + at + 4);
                int high = u4(code, base + at + 8);
                return at - pc + 12 + (high - low + 1) * 4;
            }
            case 0xAB: {
                int at = pc + 1 + pad(pc);
                int pairs = u4(code, base + at + 4);
                return at - pc + 8 + pairs * 8;
            }
            default:
                if (opcode >= 0x99 && opcode <= 0xA8) return 3;
                return 1;
        }
    }

    /** The padding after a switch opcode to the next 4-byte boundary. */
    private static int pad(int pc) {
        return (4 - ((pc + 1) % 4)) % 4;
    }

    private static int u2(byte[] bytes, int at) {
        return ((bytes[at] & 0xFF) << 8) | (bytes[at + 1] & 0xFF);
    }

    private static int u4(byte[] bytes, int at) {
        return ((bytes[at] & 0xFF) << 24) | ((bytes[at + 1] & 0xFF) << 16)
                | ((bytes[at + 2] & 0xFF) << 8) | (bytes[at + 3] & 0xFF);
    }

    private static void skipAttributes(DataInputStream in)
            throws IOException {
        int attributes = in.readUnsignedShort();
        for (int attribute = 0; attribute < attributes; attribute++) {
            in.readUnsignedShort();
            skip(in, in.readInt());
        }
    }

    private static void skip(DataInputStream in, int bytes)
            throws IOException {
        int left = bytes;
        while (left > 0) {
            int skipped = in.skipBytes(left);
            if (skipped <= 0) throw new IOException("truncated class file");
            left -= skipped;
        }
    }

    /** The constant pool, as far as the scan reads it. */
    private static final class Pool {
        private final int[] tags;
        private final Object[] values;

        Pool(DataInputStream in) throws IOException {
            int count = in.readUnsignedShort();
            tags = new int[count];
            values = new Object[count];
            for (int index = 1; index < count; index++) {
                int tag = in.readUnsignedByte();
                tags[index] = tag;
                switch (tag) {
                    case 1:
                        values[index] = in.readUTF();
                        break;
                    case 7: case 8: case 16:
                        values[index] = in.readUnsignedShort();
                        break;
                    case 9: case 10: case 11: case 12: case 18:
                        values[index] = new int[] {in.readUnsignedShort(),
                                in.readUnsignedShort()};
                        break;
                    case 3: case 4:
                        in.readInt();
                        break;
                    case 5: case 6:
                        in.readLong();
                        index++;
                        break;
                    case 15:
                        in.readUnsignedByte();
                        in.readUnsignedShort();
                        break;
                    default:
                        throw new IOException("constant pool tag " + tag);
                }
            }
        }

        String utf8(int index) {
            return (String) values[index];
        }

        String className(int index) {
            return utf8((Integer) values[index]);
        }

        /** A String constant's text, or null for any other constant. */
        String string(int index) {
            return index > 0 && index < tags.length && tags[index] == 8
                    ? utf8((Integer) values[index]) : null;
        }

        /** A member reference: {owner, name}. */
        String[] member(int index) {
            int[] ref = (int[]) values[index];
            int[] nameAndType = (int[]) values[ref[1]];
            return new String[] {className(ref[0]), utf8(nameAndType[0])};
        }
    }
}

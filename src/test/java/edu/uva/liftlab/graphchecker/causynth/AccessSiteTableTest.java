package edu.uva.liftlab.graphchecker.causynth;

import static org.junit.Assert.assertEquals;

import edu.uva.liftlab.graphchecker.contract.AccessSites;
import java.io.ByteArrayInputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

/**
 * Every access hook of a woven class is named by the bytecode of the access
 * it stands before, in the VM's spelling -- the index the VM logs that access
 * at -- and the runtime's own calls in between are not that access.
 */
public class AccessSiteTableTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private static final String HOOK = AccessSiteTable.HOOK_OWNER;
    private static final String FIVE = "(Ljava/lang/Object;Ljava/lang/String;"
            + "Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)V";

    /**
     * {@code void m(Map map)}: a hooked field read at 13, and a hooked put
     * whose hook is followed by a runtime call before the put at 39.
     */
    private static byte[] woven() {
        ClassWriter writer = new ClassWriter(ClassWriter.COMPUTE_MAXS);
        writer.visit(Opcodes.V1_8, Opcodes.ACC_PUBLIC, "a/T", null,
                "java/lang/Object", null);
        writer.visitField(Opcodes.ACC_PRIVATE, "f", "I", null, null)
                .visitEnd();
        MethodVisitor m = writer.visitMethod(Opcodes.ACC_PUBLIC, "m",
                "(Ljava/util/Map;)V", null, null);
        m.visitCode();
        m.visitVarInsn(Opcodes.ALOAD, 0);                          // 0
        m.visitLdcInsn("a.T");                                     // 1
        m.visitLdcInsn("f");                                       // 3
        m.visitLdcInsn("I");                                       // 5
        m.visitLdcInsn("site-read");                               // 7
        m.visitMethodInsn(Opcodes.INVOKESTATIC, HOOK,
                AccessSiteTable.READ_HOOK, FIVE, false);            // 9
        m.visitVarInsn(Opcodes.ALOAD, 0);                          // 12
        m.visitFieldInsn(Opcodes.GETFIELD, "a/T", "f", "I");       // 13
        m.visitInsn(Opcodes.POP);                                  // 16
        m.visitLdcInsn("site-read");                               // 17
        m.visitMethodInsn(Opcodes.INVOKESTATIC, HOOK, "sharedDone",
                "(Ljava/lang/String;)V", false);                   // 19
        m.visitVarInsn(Opcodes.ALOAD, 1);                          // 22
        m.visitInsn(Opcodes.ACONST_NULL);                          // 23
        m.visitInsn(Opcodes.ACONST_NULL);                          // 24
        m.visitInsn(Opcodes.ACONST_NULL);                          // 25
        m.visitLdcInsn("site-write");                              // 26
        m.visitMethodInsn(Opcodes.INVOKESTATIC, HOOK,
                AccessSiteTable.WRITE_HOOK, FIVE, false);           // 28
        m.visitMethodInsn(Opcodes.INVOKESTATIC,
                "edu/uva/liftlab/graphchecker/runtime/Other", "startWork",
                "()V", false);                                     // 31
        m.visitVarInsn(Opcodes.ALOAD, 1);                          // 34
        m.visitLdcInsn("k");                                       // 35
        m.visitLdcInsn("v");                                       // 37
        m.visitMethodInsn(Opcodes.INVOKEINTERFACE, "java/util/Map", "put",
                "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;",
                true);                                             // 39
        m.visitInsn(Opcodes.POP);                                  // 44
        m.visitInsn(Opcodes.RETURN);                               // 45
        m.visitMaxs(0, 0);
        m.visitEnd();
        writer.visitEnd();
        return writer.toByteArray();
    }

    @Test
    public void eachHookNamesTheAccessItStandsBefore() throws Exception {
        Map<String, String> sites =
                AccessSiteTable.scan(new ByteArrayInputStream(woven()));
        assertEquals(2, sites.size());
        assertEquals("the field load after the hook, as the VM names it",
                "a.T#m(Ljava/util/Map;)V#13:READ", sites.get("site-read"));
        assertEquals("the put, past the runtime's own call in between",
                "a.T#m(Ljava/util/Map;)V#39:WRITE", sites.get("site-write"));
    }

    @Test
    public void theTableStandsBesideTheClassesAndReadsBack()
            throws Exception {
        Path classes = folder.newFolder("instrumented-classes").toPath();
        Files.createDirectories(classes.resolve("a"));
        Files.write(classes.resolve("a/T.class"), woven());
        assertEquals(2, AccessSiteTable.write(classes));
        AccessSites table = AccessSites.read(classes);
        assertEquals("a.T#m(Ljava/util/Map;)V#13:READ",
                table.vmSite("site-read"));
        assertEquals(true, table.holds("a.T#m(Ljava/util/Map;)V#39:WRITE"));
        assertEquals(false, table.holds("a.T#m(Ljava/util/Map;)V#13:WRITE"));
        assertEquals(true, AccessSites.read(folder.newFolder("none")
                .toPath()).isEmpty());
    }
}

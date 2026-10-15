package edu.uva.liftlab.graphchecker.causynth;

import org.junit.After;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import soot.G;
import soot.SootMethod;
import soot.Unit;

import java.io.File;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

/**
 * SYMBOL-SCOPE §2.2: a library call's result depends on its receiver when
 * the receiver is shared state, the callee's class is a library -- no class
 * of the system's own roots -- and its owner holds state a guard decides on.
 */
public class LibraryReceiversTest {
    @Rule
    public final TemporaryFolder roots = new TemporaryFolder();

    @After
    public void resetSoot() {
        G.reset();
    }

    @Test
    public void aLibraryCallReadsItsReceiverWhenItIsShared() throws Exception {
        SootMethod read = read();
        List<Unit> units = new ArrayList<>(read.getActiveBody().getUnits());
        File system = roots.newFolder("classes");
        Files.createDirectories(system.toPath().resolve("f"));
        Files.createFile(system.toPath().resolve("f/Caller.class"));
        String both = system + File.pathSeparator + roots.newFolder("other");
        Object[][] rows = {
            {"a field's object, through a cast", true,
                LibraryReceivers.shared(units, 4, JimpleScene.local(
                        read.getActiveBody(), "$r2"), c -> false)},
            {"an object the method allocated", false,
                LibraryReceivers.shared(units, 7, JimpleScene.local(
                        read.getActiveBody(), "$r3"), c -> false)},
            {"a configuration", true,
                LibraryReceivers.stateful("f.Conf", "getBoolean")},
            {"a logger", false,
                LibraryReceivers.stateful("org.slf4j.Logger", "isDebugEnabled")},
            {"a metrics registry", false,
                LibraryReceivers.stateful("a.metrics2.Registry", "get")},
            {"an identity method", false,
                LibraryReceivers.stateful("f.Conf", "hashCode")},
            {"a class of the system's own roots is no library", true,
                LibraryReceivers.systemClasses(both).test("f.Caller")},
            {"a class no root holds is one", false,
                LibraryReceivers.systemClasses(both).test("f.Conf")}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
        for (String none : new String[]{null, " "}) {
            try {
                LibraryReceivers.systemClasses(none);
                fail("no system root is refused by name");
            } catch (IllegalStateException refused) {
                assertEquals(true, refused.getMessage()
                        .contains(LibraryReceivers.ROOTS));
            }
        }
    }

    /**
     * {@code f.Caller.read()}: {@code getBoolean} on its field's
     * {@code f.Conf} through a cast (unit 4), then on one it allocates
     * (unit 7).
     */
    private static SootMethod read() {
        JimpleScene.load(JimpleScene.OBJECT,
                "public class f.Conf extends java.lang.Object {"
                        + " public boolean getBoolean() { } }",
                "application public class f.Caller extends java.lang.Object {"
                        + " java.lang.Object conf; public void read() {"
                        + " f.Caller r0; java.lang.Object $r1; f.Conf $r2, $r3;"
                        + " boolean $z0; r0 := @this: f.Caller;"
                        + " $r1 = r0.<f.Caller: java.lang.Object conf>;"
                        + " $r2 = (f.Conf) $r1; nop; $z0 = virtualinvoke"
                        + " $r2.<f.Conf: boolean getBoolean()>();"
                        + " $r3 = new f.Conf; nop; $z0 = virtualinvoke"
                        + " $r3.<f.Conf: boolean getBoolean()>(); return; } }");
        return JimpleScene.method("<f.Caller: void read()>");
    }
}

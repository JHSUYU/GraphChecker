package edu.uva.liftlab.graphchecker.causynth;

import org.junit.After;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import soot.BooleanType;
import soot.G;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.VoidType;
import soot.jimple.Jimple;

import java.io.File;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

/**
 * SYMBOL-SCOPE §2.2: a library call's result depends on its receiver when
 * the receiver is shared state, the callee's class is a library -- no class
 * of the system's own roots -- and its owner holds state a guard decides on.
 */
public class LibraryReceiversTest {
    private static final Jimple J = Jimple.v();

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
        List<Local> locals = new ArrayList<>(read.getActiveBody().getLocals());
        File system = roots.newFolder("classes");
        Files.createDirectories(system.toPath().resolve("f"));
        Files.createFile(system.toPath().resolve("f/Caller.class"));
        String both = system + File.pathSeparator + roots.newFolder("other");
        Object[][] rows = {
            {"a field's object, through a cast", true,
                LibraryReceivers.shared(units, 4, locals.get(2), c -> false)},
            {"an object the method allocated", false,
                LibraryReceivers.shared(units, 7, locals.get(3), c -> false)},
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
        G.reset();
        SootClass object = type("java.lang.Object", null);
        SootClass conf = type("f.Conf", object);
        SootMethod flag = method(conf, "getBoolean", BooleanType.v());
        SootClass caller = type("f.Caller", object);
        caller.setApplicationClass();
        SootField held = new SootField("conf", object.getType(), 0);
        caller.addField(held);
        RefType self = caller.getType();
        SootMethod read = method(caller, "read", VoidType.v());
        Local e0 = local(read, "r0", self);
        Local field = local(read, "$r1", object.getType());
        Local cast = local(read, "$r2", conf.getType());
        Local fresh = local(read, "$r3", conf.getType());
        Local answer = local(read, "$z0", BooleanType.v());
        read.getActiveBody().getUnits().addAll(Arrays.asList(
                J.newIdentityStmt(e0, J.newThisRef(self)),
                J.newAssignStmt(field, J.newInstanceFieldRef(e0,
                        held.makeRef())),
                J.newAssignStmt(cast, J.newCastExpr(field, conf.getType())),
                J.newNopStmt(),
                J.newAssignStmt(answer, J.newVirtualInvokeExpr(cast,
                        flag.makeRef())),
                J.newAssignStmt(fresh, J.newNewExpr(conf.getType())),
                J.newNopStmt(),
                J.newAssignStmt(answer, J.newVirtualInvokeExpr(fresh,
                        flag.makeRef())),
                J.newReturnVoidStmt()));
        return read;
    }

    private static SootClass type(String name, SootClass parent) {
        SootClass type = new SootClass(name, Modifier.PUBLIC);
        if (parent != null) type.setSuperclass(parent);
        Scene.v().addClass(type);
        return type;
    }

    private static SootMethod method(SootClass owner, String name,
                                     Type returned) {
        SootMethod method = new SootMethod(name,
                Collections.<Type>emptyList(), returned, Modifier.PUBLIC);
        owner.addMethod(method);
        method.setActiveBody(J.newBody(method));
        return method;
    }

    private static Local local(SootMethod method, String name, Type type) {
        Local local = J.newLocal(name, type);
        method.getActiveBody().getLocals().add(local);
        return local;
    }
}

package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import org.junit.After;
import org.junit.Test;
import soot.G;
import soot.IntType;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.VoidType;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.options.Options;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;

/**
 * F3: a protobuf field the slice demands crosses the wire by rule, when an
 * RPC carries its message.  The scene is protobuf-shaped: a message {@code
 * KeyProto} whose hierarchy reaches {@code GeneratedMessageV3}, held by the
 * response of a service method {@code getKeys(RpcController, KeysRequest)},
 * its {@code KeyProto$Builder.setKeyId}, two producers calling it, and an
 * annotated throw deciding on two {@code getKeyId()} reads -- beside a third
 * read nothing demands -- and on the same field of {@code SectionProto}, a
 * message no service carries (an on-disk section) with its own setter call.
 */
public class WirePortDerivationTest {
    private static final String MESSAGE = "m.Protos$KeyProto";
    private static final String BUILDER = MESSAGE + "$Builder";
    private static final String GETTER = "<" + MESSAGE + ": int getKeyId()>";
    private static final String SETTER = "<" + BUILDER + ": " + BUILDER
            + " setKeyId(int)>";
    private static final String ENCODE_A = "<m.Codec: void encodeA("
            + BUILDER + ",int)>";
    private static final String ENCODE_B = "<m.Codec: void encodeB("
            + BUILDER + ",int)>";
    private static final String SECTION = "m.Protos$SectionProto";
    private static final String CHECK = "<m.Codec: void check(" + MESSAGE
            + "," + MESSAGE + "," + SECTION + ")>";

    @After
    public void resetSoot() {
        G.reset();
    }

    @Test
    public void aDemandedFieldReadIsAPortOfItsMessageField() throws Exception {
        StaticProgram program = new SeedBackwardStaticAnalyzer(target())
                .analyze();
        assertEquals("one port: the RPC message's field, the on-disk"
                + " section's none", 1, program.communicationCallSites.size());
        Map<String, Object> port = program.communicationCallSites.get(0);
        String portId = MapFields.text(port.get(
                CommunicationCatalogContract.PORT_ID));
        Object[][] rows = {
                {"its name", "auto:KeyProto.KeyId", port.get(
                        CommunicationCatalogContract.PORT_NAME)},
                {"a direction-free declared port id", true,
                        CommunicationCatalogContract.declaredPortId(portId)
                                && portId.endsWith(
                                ".wire.auto:KeyProto.KeyId")},
                {"its type", "int", port.get(
                        CommunicationCatalogContract.PORT_JAVA_TYPE)},
                {"every setter call is a producer, argument 0",
                        Arrays.asList(
                                "CALL_ARGUMENT " + ENCODE_A + "#u2 0 "
                                        + SETTER,
                                "CALL_ARGUMENT " + ENCODE_B + "#u3 0 "
                                        + SETTER),
                        captures(port, CommunicationCatalogContract
                                .PORT_PRODUCERS)},
                {"every demanded getter read is a consumer, the idle one"
                        + " is none", Arrays.asList(
                        "CALL_RETURN " + CHECK + "#u3 null " + GETTER,
                        "CALL_RETURN " + CHECK + "#u4 null " + GETTER),
                        captures(port, CommunicationCatalogContract
                                .PORT_CONSUMERS)},
                {"each producer's value reaches each consumer",
                        new LinkedHashSet<>(Arrays.asList(
                                ENCODE_A + "::i0 -> " + CHECK + "::i0",
                                ENCODE_A + "::i0 -> " + CHECK + "::i1",
                                ENCODE_B + "::i1 -> " + CHECK + "::i0",
                                ENCODE_B + "::i1 -> " + CHECK + "::i1")),
                        edges(program, "wire_handoff")},
                {"and the slice goes on on the sending side",
                        true, edges(program, "local_def_use").containsAll(
                        Arrays.asList(
                                ENCODE_A + ".param1:int -> " + ENCODE_A
                                        + "::i0",
                                ENCODE_B + "::i0 -> " + ENCODE_B
                                        + "::i1"))}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    private static List<String> captures(Map<String, Object> port,
                                         String side) {
        List<String> found = new ArrayList<>();
        for (Map<String, Object> capture : MapFields.rows(port.get(side))) {
            found.add(capture.get(CommunicationCatalogContract
                    .PORT_OUTPUT_CAPTURE_KIND) + " "
                    + capture.get(CommunicationCatalogContract.CALL_SITE_ID)
                    + " " + capture.get(
                    CommunicationCatalogContract.PORT_ARGUMENT_INDEX) + " "
                    + capture.get(
                    CommunicationCatalogContract.DECLARED_CALLEE));
        }
        return found;
    }

    private static Set<String> edges(StaticProgram program, String kind) {
        Set<String> found = new LinkedHashSet<>();
        for (Map<String, Object> edge : program.edges) {
            if (kind.equals(edge.get("kind"))) {
                found.add(edge.get("fromCell") + " -> " + edge.get("toCell"));
            }
        }
        return found;
    }

    /** The scene, and the annotated throw in {@code check}. */
    private static CausynthTargetContext target() {
        G.reset();
        Options.v().set_allow_phantom_refs(true);
        SootClass object = library("java.lang.Object", null);
        SootClass runtime = library("com.google.protobuf.GeneratedMessageV3",
                object);
        SootClass message = application(MESSAGE, runtime);
        SootClass section = application(SECTION, runtime);
        SootClass codec = application("m.Codec", object);
        library("java.lang.IllegalStateException", object);
        RefType messageType = message.getType();
        RefType sectionType = section.getType();

        // The service: getKeys(RpcController, KeysRequest) answers a
        // KeysReply whose repeated field holds KeyProto.
        SootClass reply = library("m.Protos$KeysReply", runtime);
        method(reply, "getKey", Collections.<Type>singletonList(IntType.v()),
                messageType, 0);
        method(library("m.Protos$KeyService$BlockingInterface", object),
                "getKeys", Arrays.<Type>asList(library(
                        "com.google.protobuf.RpcController", object).getType(),
                        library("m.Protos$KeysRequest", runtime).getType()),
                reply.getType(), 0);

        SootMethod[] keyId = keyIdField(message, object);
        SootMethod[] sectionKeyId = keyIdField(section, object);
        // encodeA sets its parameter; encodeB a value it computed;
        // saveSection writes the on-disk section.
        for (String name : new String[]{"encodeA", "encodeB", "saveSection"}) {
            SootMethod set = ("saveSection".equals(name) ? sectionKeyId
                    : keyId)[1];
            Type builderType = set.getDeclaringClass().getType();
            SootMethod encode = method(codec, name, Arrays.<Type>asList(
                    builderType, IntType.v()), VoidType.v(), Modifier.STATIC);
            Local target = local(encode, "r0", builderType);
            Local key = local(encode, "i0", IntType.v());
            List<Unit> units = new ArrayList<>(Arrays.asList(
                    Jimple.v().newIdentityStmt(target,
                            Jimple.v().newParameterRef(builderType, 0)),
                    Jimple.v().newIdentityStmt(key,
                            Jimple.v().newParameterRef(IntType.v(), 1))));
            Local sent = key;
            if ("encodeB".equals(name)) {
                sent = local(encode, "i1", IntType.v());
                units.add(Jimple.v().newAssignStmt(sent,
                        Jimple.v().newAddExpr(key, IntConstant.v(1))));
            }
            units.add(Jimple.v().newInvokeStmt(Jimple.v()
                    .newVirtualInvokeExpr(target, set.makeRef(),
                            Collections.<Value>singletonList(sent))));
            units.add(Jimple.v().newReturnVoidStmt());
            body(encode, units.toArray(new Unit[0]));
        }

        SootMethod check = method(codec, "check", Arrays.<Type>asList(
                messageType, messageType, sectionType), VoidType.v(),
                Modifier.STATIC);
        Local first = local(check, "r0", messageType);
        Local second = local(check, "r1", messageType);
        Local stored = local(check, "r2", sectionType);
        Local firstKey = local(check, "i0", IntType.v());
        Local secondKey = local(check, "i1", IntType.v());
        Local idle = local(check, "i2", IntType.v());
        Local storedKey = local(check, "i3", IntType.v());
        RefType failure = RefType.v("java.lang.IllegalStateException");
        Local thrown = local(check, "r3", failure);
        Unit done = Jimple.v().newReturnVoidStmt();
        body(check, Jimple.v().newIdentityStmt(first,
                        Jimple.v().newParameterRef(messageType, 0)),
                Jimple.v().newIdentityStmt(second,
                        Jimple.v().newParameterRef(messageType, 1)),
                Jimple.v().newIdentityStmt(stored,
                        Jimple.v().newParameterRef(sectionType, 2)),
                Jimple.v().newAssignStmt(firstKey, Jimple.v()
                        .newVirtualInvokeExpr(first, keyId[0].makeRef())),
                Jimple.v().newAssignStmt(secondKey, Jimple.v()
                        .newVirtualInvokeExpr(second, keyId[0].makeRef())),
                Jimple.v().newAssignStmt(idle, Jimple.v()
                        .newVirtualInvokeExpr(first, keyId[0].makeRef())),
                Jimple.v().newAssignStmt(storedKey, Jimple.v()
                        .newVirtualInvokeExpr(stored,
                                sectionKeyId[0].makeRef())),
                Jimple.v().newIfStmt(Jimple.v().newNeExpr(firstKey,
                        secondKey), done),
                Jimple.v().newIfStmt(Jimple.v().newEqExpr(storedKey,
                        IntConstant.v(0)), done),
                Jimple.v().newAssignStmt(thrown,
                        Jimple.v().newNewExpr(failure)),
                Jimple.v().newThrowStmt(thrown),
                done);
        return new CausynthTargetContext(Paths.get("unused"), "t",
                new ExceptionTargetSite("t", "m.Codec", "check",
                        "(Lm/Protos$KeyProto;Lm/Protos$KeyProto;"
                                + "Lm/Protos$SectionProto;)V", CHECK,
                        "java.lang.IllegalStateException", 0));
    }

    /** {@code int getKeyId()} on the message and {@code setKeyId(int)} on
     *  its {@code $Builder}. */
    private static SootMethod[] keyIdField(SootClass message,
                                           SootClass object) {
        SootClass builder = application(message.getName() + "$Builder",
                object);
        RefType messageType = message.getType();
        RefType builderType = builder.getType();
        SootMethod getter = method(message, "getKeyId",
                Collections.<Type>emptyList(), IntType.v(), 0);
        Local self = local(getter, "r0", messageType);
        body(getter, Jimple.v().newIdentityStmt(self,
                        Jimple.v().newThisRef(messageType)),
                Jimple.v().newReturnStmt(IntConstant.v(0)));
        SootMethod setter = method(builder, "setKeyId",
                Collections.<Type>singletonList(IntType.v()), builderType, 0);
        Local held = local(setter, "r0", builderType);
        Local value = local(setter, "i0", IntType.v());
        body(setter, Jimple.v().newIdentityStmt(held,
                        Jimple.v().newThisRef(builderType)),
                Jimple.v().newIdentityStmt(value,
                        Jimple.v().newParameterRef(IntType.v(), 0)),
                Jimple.v().newReturnStmt(held));
        return new SootMethod[]{getter, setter};
    }

    private static SootClass application(String name, SootClass parent) {
        SootClass type = library(name, parent);
        type.setApplicationClass();
        return type;
    }

    private static SootClass library(String name, SootClass parent) {
        SootClass type = new SootClass(name, Modifier.PUBLIC);
        if (parent != null) type.setSuperclass(parent);
        Scene.v().addClass(type);
        return type;
    }

    private static SootMethod method(SootClass owner, String name,
                                     List<Type> parameters, Type returned,
                                     int modifiers) {
        SootMethod method = new SootMethod(name, parameters, returned,
                Modifier.PUBLIC | modifiers);
        owner.addMethod(method);
        method.setActiveBody(Jimple.v().newBody(method));
        return method;
    }

    private static Local local(SootMethod method, String name, Type type) {
        Local local = Jimple.v().newLocal(name, type);
        method.getActiveBody().getLocals().add(local);
        return local;
    }

    private static void body(SootMethod method, Unit... units) {
        method.getActiveBody().getUnits().addAll(Arrays.asList(units));
    }
}

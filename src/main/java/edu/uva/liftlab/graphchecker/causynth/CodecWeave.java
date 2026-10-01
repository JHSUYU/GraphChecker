package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.causynth.CausynthPipeline.Hook;
import edu.uva.liftlab.graphchecker.causynth.CausynthPipeline.HookCatalog;
import edu.uva.liftlab.graphchecker.contract.WireDeclarations;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.ArrayType;
import soot.Body;
import soot.IntType;
import soot.Local;
import soot.LongType;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.NullConstant;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;

import java.util.ArrayList;
import java.util.List;

/**
 * The codec hooks (WIRE-CODEC §4.1), woven at INSTRUMENT by rule from the
 * declarations ({@link WireDeclarations}), the way {@link DoorWeave} weaves
 * doors -- but as runtime plumbing no pass analyses, into the concolic weave
 * only:
 *
 * <ul>
 * <li>a declared encoder, at each return: {@code encodedByCodec(codec,
 * depth, graph, encoded, exchange)};</li>
 * <li>a declared decoder, at each return ({@code graph: return}) or at entry
 * ({@code graph: argN}): {@code graph = decodedByCodec(codec, depth,
 * encoded, graph)}, which may hand back a re-homed leaf;</li>
 * <li>a {@code call} hook, after each call site in the application scope its
 * pattern matches, the same call around the call's values;</li>
 * <li>a declared {@code EXCHANGE}, entry and every exit (throws included):
 * {@code beginCodecExchange(transport)} / {@code endCodecExchange(token)}.</li>
 * </ul>
 *
 * <p>Every declared method's body enters its codec on entry and leaves it on
 * every exit, so one called inside another declared method of the same codec
 * is transparent (its depth is not 0).  Each body's original units are
 * numbered before any hook goes in, so the site vocabulary is the
 * recording's.  A declared method that does not resolve to a concrete
 * application method is refused, never skipped.</p>
 */
final class CodecWeave {
    private static final Logger LOG = LoggerFactory.getLogger(
            CodecWeave.class);

    private CodecWeave() {
    }

    /** Weaves every declared codec and exchange of {@code declared}. */
    static void apply(WireDeclarations declared, HookCatalog refs) {
        for (WireDeclarations.Codec codec : declared.codecs()) {
            for (WireDeclarations.Hook encoder : codec.encoders()) {
                weave(codec.name(), encoder, true, refs);
            }
            for (WireDeclarations.Hook decoder : codec.decoders()) {
                weave(codec.name(), decoder, false, refs);
            }
        }
        for (WireDeclarations.Exchange exchange : declared.exchanges()) {
            bracket(exchange, refs);
        }
    }

    private static void weave(String codec, WireDeclarations.Hook hook,
                              boolean encoder, HookCatalog refs) {
        if (hook.call()) {
            int woven = 0;
            for (SootClass type : new ArrayList<>(
                    Scene.v().getApplicationClasses())) {
                for (SootMethod method : new ArrayList<>(type.getMethods())) {
                    Body body = CausynthStaticFacts.activeBody(method);
                    if (body != null) {
                        woven += calls(codec, hook, encoder, body, refs);
                    }
                }
            }
            LOG.info("Codec {}: {} call site(s) of {}",
                    codec, woven, hook.target());
            return;
        }
        Body body = declaredBody(hook.target());
        SootMethod method = body.getMethod();
        List<Unit> original = CausynthPipeline.snapshotUnits(body);
        CausynthPipeline.tagOriginalUnits(original);
        Unit entry = CausynthPipeline.safeInstrumentationEntry(body, method);
        if (entry == null) {
            throw refused("CODEC_METHOD_HAS_NO_SAFE_ENTRY", hook);
        }
        boolean atEntry = !encoder && hook.graph().startsWith("arg");
        if (!encoder && !atEntry && !"return".equals(hook.graph())
                || "return".equals(hook.encoded()) && atEntry) {
            throw refused("CODEC_HOOK_SLOT_UNAVAILABLE", hook);
        }
        StringConstant name = StringConstant.v(codec);
        Local depth = CausynthPipeline.newTraceLocal(body, IntType.v(),
                "$causynthCodecDepth");
        List<Unit> prologue = new ArrayList<>();
        refs.bracket(prologue, depth, Hook.ENTER_CODEC, name);
        if (atEntry) {
            Local graph = slot(body, method, hook.graph(), null, hook);
            decode(body, prologue, name, depth, value(body, method,
                    hook.encoded(), null, hook), graph, refs);
        }
        CausynthPipeline.insertBeforeOrAppendNoRedirect(body, entry,
                prologue);
        for (Unit exit : CausynthPipeline.originalReturns(original, 0)) {
            List<Unit> units = new ArrayList<>();
            Value returned = exit instanceof ReturnStmt
                    ? ((ReturnStmt) exit).getOp() : null;
            if (encoder) {
                refs.bracket(units, Hook.ENCODED_BY_CODEC, name, depth,
                        value(body, method, hook.graph(), returned, hook),
                        value(body, method, hook.encoded(), returned, hook),
                        IntConstant.v(hook.exchange() ? 1 : 0));
            } else if (!atEntry) {
                Local graph = CausynthPipeline.newTraceLocal(body,
                        method.getReturnType(), "$causynthCodecGraph");
                units.add(Jimple.v().newAssignStmt(graph, value(body, method,
                        hook.graph(), returned, hook)));
                decode(body, units, name, depth, value(body, method,
                        hook.encoded(), returned, hook), graph, refs);
                ((ReturnStmt) exit).setOp(graph);
            }
            refs.bracket(units, Hook.EXIT_CODEC, name, depth);
            CausynthPipeline.insertBeforeSequence(body, exit, units);
        }
        CausynthPipeline.appendCatchAll(body,
                CausynthPipeline.afterWovenPrologue(body, prologue),
                "$causynthCodecThrown", (units, caught) -> refs.bracket(units,
                        Hook.EXIT_CODEC, name, depth));
    }

    /**
     * Hooks every original call {@code hook}'s pattern matches in one body,
     * after the call: the call's values are the hook's slots.
     */
    private static int calls(String codec, WireDeclarations.Hook hook,
                             boolean encoder, Body body, HookCatalog refs) {
        List<Unit> original = CausynthPipeline.snapshotUnits(body);
        List<Stmt> matched = new ArrayList<>();
        for (Unit unit : original) {
            if (unit instanceof Stmt && ((Stmt) unit).containsInvokeExpr()
                    && hook.calls(((Stmt) unit).getInvokeExpr()
                    .getMethodRef().getSignature())) {
                matched.add((Stmt) unit);
            }
        }
        if (matched.isEmpty()) return 0;
        CausynthPipeline.tagOriginalUnits(original);
        StringConstant name = StringConstant.v(codec);
        int woven = 0;
        for (Stmt call : matched) {
            Value result = call instanceof AssignStmt
                    ? ((AssignStmt) call).getLeftOp() : null;
            boolean graphReturned = "return".equals(hook.graph());
            if ((graphReturned || "return".equals(hook.encoded()))
                    && !(result instanceof Local)) {
                continue;
            }
            List<Unit> units = new ArrayList<>();
            Local depth = CausynthPipeline.newTraceLocal(body, IntType.v(),
                    "$causynthCodecDepth");
            refs.bracket(units, depth, Hook.ENTER_CODEC, name);
            Value graph = callValue(body, call, hook.graph(), result, units,
                    hook);
            Value encoded = callValue(body, call, hook.encoded(), result,
                    units, hook);
            if (encoder) {
                refs.bracket(units, Hook.ENCODED_BY_CODEC, name, depth, graph,
                        encoded, IntConstant.v(hook.exchange() ? 1 : 0));
            } else if (graph instanceof Local) {
                decode(body, units, name, depth, encoded, (Local) graph,
                        refs);
            } else {
                throw refused("CODEC_HOOK_SLOT_UNAVAILABLE", hook);
            }
            refs.bracket(units, Hook.EXIT_CODEC, name, depth);
            CausynthPipeline.insertAfterSequence(body, call, units);
            woven++;
        }
        return woven;
    }

    /** {@code graph = (T) decodedByCodec(codec, depth, encoded, graph)}. */
    private static void decode(Body body, List<Unit> units,
                               StringConstant codec, Local depth,
                               Value encoded, Local graph, HookCatalog refs) {
        Local decoded = CausynthPipeline.newTraceLocal(body,
                RefType.v("java.lang.Object"), "$causynthCodecDecoded");
        refs.bracket(units, decoded, Hook.DECODED_BY_CODEC, codec, depth,
                encoded, graph);
        units.add(Jimple.v().newAssignStmt(graph,
                Jimple.v().newCastExpr(decoded, graph.getType())));
    }

    /** Brackets one declared exchange method, entry to every exit. */
    private static void bracket(WireDeclarations.Exchange exchange,
                                HookCatalog refs) {
        Body body = declaredBody(exchange.method());
        SootMethod method = body.getMethod();
        List<Unit> original = CausynthPipeline.snapshotUnits(body);
        CausynthPipeline.tagOriginalUnits(original);
        Unit entry = CausynthPipeline.safeInstrumentationEntry(body, method);
        if (entry == null) {
            throw new IllegalStateException("CODEC_METHOD_HAS_NO_SAFE_ENTRY: "
                    + exchange.method());
        }
        Local token = CausynthPipeline.newTraceLocal(body, LongType.v(),
                "$causynthCodecExchange");
        List<Unit> prologue = new ArrayList<>();
        refs.bracket(prologue, token, Hook.BEGIN_CODEC_EXCHANGE,
                StringConstant.v(exchange.transport()));
        CausynthPipeline.insertBeforeOrAppendNoRedirect(body, entry,
                prologue);
        for (Unit exit : CausynthPipeline.originalReturns(original, 0)) {
            List<Unit> units = new ArrayList<>();
            refs.bracket(units, Hook.END_CODEC_EXCHANGE, token);
            CausynthPipeline.insertBeforeSequence(body, exit, units);
        }
        CausynthPipeline.appendCatchAll(body,
                CausynthPipeline.afterWovenPrologue(body, prologue),
                "$causynthCodecExchangeThrown", (units, caught) ->
                        refs.bracket(units, Hook.END_CODEC_EXCHANGE, token));
    }

    /** The body of a declared method: concrete, of an application class. */
    private static Body declaredBody(String signature) {
        SootMethod method = CausynthStaticFacts.method(signature);
        if (method == null || !method.isConcrete()
                || !method.getDeclaringClass().isApplicationClass()) {
            throw new IllegalStateException("CODEC_METHOD_UNAVAILABLE: "
                    + signature + " is no concrete method of a woven class");
        }
        return method.retrieveActiveBody();
    }

    /** A method hook's slot: {@code this}, {@code argN} or the returned
     *  value; null (the constant) when the hook states none. */
    private static Value value(Body body, SootMethod method, String slot,
                               Value returned, WireDeclarations.Hook hook) {
        if (slot == null) return NullConstant.v();
        if ("return".equals(slot)) {
            if (returned == null) {
                throw refused("CODEC_HOOK_SLOT_UNAVAILABLE", hook);
            }
            return object(returned, hook);
        }
        return slot(body, method, slot, returned, hook);
    }

    private static Local slot(Body body, SootMethod method, String slot,
                              Value returned, WireDeclarations.Hook hook) {
        Local local;
        if ("this".equals(slot)) {
            if (method.isStatic()) {
                throw refused("CODEC_HOOK_SLOT_UNAVAILABLE", hook);
            }
            local = body.getThisLocal();
        } else {
            int index = Integer.parseInt(slot.substring("arg".length()));
            if (index >= method.getParameterCount()) {
                throw refused("CODEC_HOOK_SLOT_UNAVAILABLE", hook);
            }
            local = body.getParameterLocal(index);
        }
        return (Local) object(local, hook);
    }

    /** A call hook's slot: the call's receiver, an argument or its result. */
    private static Value callValue(Body body, Stmt call, String slot,
                                   Value result, List<Unit> units,
                                   WireDeclarations.Hook hook) {
        if (slot == null) return NullConstant.v();
        InvokeExpr invoke = call.getInvokeExpr();
        Value value;
        if ("return".equals(slot)) {
            value = result;
        } else if ("this".equals(slot)) {
            if (!(invoke instanceof InstanceInvokeExpr)) {
                throw refused("CODEC_HOOK_SLOT_UNAVAILABLE", hook);
            }
            value = ((InstanceInvokeExpr) invoke).getBase();
        } else {
            int index = Integer.parseInt(slot.substring("arg".length()));
            if (index >= invoke.getArgCount()) {
                throw refused("CODEC_HOOK_SLOT_UNAVAILABLE", hook);
            }
            value = invoke.getArg(index);
        }
        if (value instanceof Local || value instanceof NullConstant) {
            return object(value, hook);
        }
        // A constant argument is still a value the hook reads.
        Local held = CausynthPipeline.newTraceLocal(body, value.getType(),
                "$causynthCodecValue");
        units.add(Jimple.v().newAssignStmt(held, value));
        return object(held, hook);
    }

    /** A slot's value, which must be an object: a graph or its encoding. */
    private static Value object(Value value, WireDeclarations.Hook hook) {
        Type type = value.getType();
        if (!(type instanceof RefType || type instanceof ArrayType
                || value instanceof NullConstant)) {
            throw refused("CODEC_SLOT_NOT_AN_OBJECT", hook);
        }
        return value;
    }

    private static IllegalStateException refused(String code,
                                                  WireDeclarations.Hook hook) {
        return new IllegalStateException(code + ": " + hook);
    }
}

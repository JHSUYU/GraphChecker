package edu.uva.liftlab.graphchecker.causynth;

import soot.Body;
import soot.G;
import soot.Local;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.parser.JimpleAST;
import soot.options.Options;

import java.io.ByteArrayInputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * A Soot scene stated in Jimple, one class per text, as Soot prints a class:
 * every class a library class unless its text starts {@code application},
 * every method stating a body ({@code { }} for an empty one) given it as
 * its active body.
 */
public final class JimpleScene {
    /** The root class, and the declared throws' exception. */
    public static final String OBJECT = "public class java.lang.Object { }";
    public static final String FAILURE = "public class"
            + " java.lang.IllegalStateException extends java.lang.Object { }";

    private static final Pattern NAME = Pattern.compile(
            "(?:class|interface)\\s+'?([\\w.$]+)'?");

    private JimpleScene() {
    }

    /** Soot reset, phantom references allowed, the classes loaded. */
    public static void load(String... classes) {
        G.reset();
        Options.v().set_allow_phantom_refs(true);
        add(classes);
    }

    /** The classes added to the scene as it stands. */
    public static void add(String... classes) {
        List<SootClass> types = new ArrayList<>();
        List<JimpleAST> parsed = new ArrayList<>();
        for (String text : classes) {
            boolean application = text.startsWith("application ");
            String jimple = application ? text.substring(12) : text;
            Matcher name = NAME.matcher(jimple);
            if (!name.find()) throw new IllegalArgumentException(text);
            SootClass type = Scene.v().containsClass(name.group(1))
                    ? Scene.v().getSootClass(name.group(1))
                    : new SootClass(name.group(1));
            if (!type.isInScene()) Scene.v().addClass(type);
            if (application) type.setApplicationClass();
            types.add(type);
            try {
                parsed.add(new JimpleAST(new ByteArrayInputStream(
                        jimple.getBytes(StandardCharsets.UTF_8))));
            } catch (Exception unparsed) {
                throw new IllegalArgumentException(unparsed + ": " + text,
                        unparsed);
            }
        }
        for (int k = 0; k < types.size(); k++) {
            parsed.get(k).getSkeleton(types.get(k));
        }
        for (int k = 0; k < types.size(); k++) {
            for (SootMethod method : types.get(k).getMethods()) {
                Body body = parsed.get(k).getBody(method);
                if (body != null) method.setActiveBody(body);
            }
        }
    }

    /** The method of that signature. */
    public static SootMethod method(String signature) {
        return Scene.v().getMethod(signature);
    }

    /** The local of {@code body} named {@code name}. */
    public static Local local(Body body, String name) {
        for (Local local : body.getLocals()) {
            if (local.getName().equals(name)) return local;
        }
        throw new IllegalArgumentException(name);
    }

    /** The unit of {@code signature}'s body that prints as {@code text}. */
    public static Unit unit(String signature, String text) {
        for (Unit unit : method(signature).getActiveBody().getUnits()) {
            if (unit.toString().equals(text)) return unit;
        }
        throw new IllegalArgumentException(text + " in " + signature);
    }
}

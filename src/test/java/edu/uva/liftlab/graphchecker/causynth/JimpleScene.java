package edu.uva.liftlab.graphchecker.causynth;

import soot.Body;
import soot.G;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.jimple.parser.JimpleAST;
import soot.options.Options;

import java.io.ByteArrayInputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public final class JimpleScene {
    public static final String OBJECT = "public class java.lang.Object { }";

    private static final Pattern NAME = Pattern.compile(
            "(?:class|interface)\\s+'?([\\w.$]+)'?");

    private JimpleScene() {
    }

    public static void load(String... classes) {
        G.reset();
        Options.v().set_allow_phantom_refs(true);
        add(classes);
    }

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

    public static SootMethod method(String signature) {
        return Scene.v().getMethod(signature);
    }
}

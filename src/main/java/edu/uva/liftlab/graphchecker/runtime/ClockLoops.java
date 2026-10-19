package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.primitiveString;

final class ClockLoops {
    private static volatile Set<String> methods = Collections.emptySet();

    private ClockLoops() {
    }

    static boolean reads(StackTraceElement[] stack) {
        Set<String> declared = methods;
        if (declared.isEmpty()) return false;
        for (StackTraceElement frame : stack) {
            if (declared.contains(frame.getClassName() + "#"
                    + frame.getMethodName())) {
                return true;
            }
        }
        return false;
    }

    static void install(List<JsonObject> rows) {
        Set<String> found = new HashSet<String>();
        for (JsonObject row : rows) {
            String method = clockMethod(row);
            if (!method.isEmpty()) found.add(method);
        }
        methods = found;
    }

    static String clockMethod(JsonObject row) {
        if (!StaticScopeMap.SITE_KIND.equals(primitiveString(row, "kind"))
                || !StaticScopeMap.DECLARED_SITE.equals(
                        primitiveString(row, "role"))
                || !StaticScopeMap.CLOCK_INPUT.equals(
                        primitiveString(row, "inputKind"))) {
            return "";
        }
        String site = primitiveString(row, "vmSite");
        int owner = site.indexOf('#');
        int descriptor = site.indexOf('(', owner + 1);
        if (owner <= 0 || descriptor <= owner + 1) return "";
        return site.substring(0, descriptor);
    }
}

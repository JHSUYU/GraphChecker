package edu.uva.liftlab.graphchecker.runtime;

import java.util.ArrayList;
import java.util.List;

import static edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.javaTypeDescriptor;

final class JvmSignature {
    private JvmSignature() {
    }

    static String[] parse(String signature) {
        String text = signature == null ? "" : signature.trim();
        int colon = text.indexOf(": ");
        int open = text.indexOf('(');
        int close = text.lastIndexOf(')');
        if (!text.startsWith("<") || !text.endsWith(">") || colon < 0
                || open < colon || close < open) {
            return null;
        }
        String owner = text.substring(1, colon).trim();
        String[] head = text.substring(colon + 2, open).trim().split(" ");
        if (owner.isEmpty() || head.length != 2) return null;
        StringBuilder descriptor = new StringBuilder("(");
        for (String parameter : parameters(text.substring(open + 1, close))) {
            descriptor.append(javaTypeDescriptor(parameter));
        }
        descriptor.append(')').append(javaTypeDescriptor(head[0]));
        return new String[] {owner.replace('.', '/'), head[1],
                descriptor.toString()};
    }

    private static List<String> parameters(String list) {
        List<String> parameters = new ArrayList<String>();
        for (String parameter : list.split(",")) {
            if (!parameter.trim().isEmpty()) parameters.add(parameter.trim());
        }
        return parameters;
    }
}

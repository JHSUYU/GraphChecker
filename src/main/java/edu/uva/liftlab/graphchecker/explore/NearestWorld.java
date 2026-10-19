package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.compose.SmtNames;
import edu.uva.liftlab.graphchecker.smt.Z3;

import java.io.IOException;
import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

final class NearestWorld {
    final String pins;
    final Z3.Answer answer;

    private NearestWorld(String pins, Z3.Answer answer) {
        this.pins = pins;
        this.answer = answer;
    }

    interface Ask {
        Z3.Answer ask(String query) throws IOException;
    }

    static NearestWorld of(Ask ask, String smt2, List<String> symbols,
                           Map<String, String> recorded,
                           Set<String> flipVariables, Z3.Answer first,
                           boolean oneByOne) throws IOException {
        Map<String, String> unneeded = new LinkedHashMap<String, String>();
        for (Map.Entry<String, String> variable : recorded.entrySet()) {
            if (!flipVariables.contains(variable.getKey())
                    && symbols.contains(variable.getKey())) {
                unneeded.put(variable.getKey(), variable.getValue());
            }
        }
        if (at(unneeded, first)) return new NearestWorld("", first);
        String every = pins(unneeded);
        Z3.Answer whole = ask.ask(smt2 + every);
        if (whole.decided() && whole.sat()) {
            return new NearestWorld(every, whole);
        }
        if (!oneByOne) return new NearestWorld("", first);
        StringBuilder kept = new StringBuilder();
        Z3.Answer current = first;
        for (Map.Entry<String, String> variable : unneeded.entrySet()) {
            String pin = pin(variable.getKey(), variable.getValue());
            if (same(current.values().get(variable.getKey()),
                    variable.getValue())) {
                kept.append(pin);
                continue;
            }
            Z3.Answer again = ask.ask(smt2 + kept + pin);
            if (again.decided() && again.sat()) {
                kept.append(pin);
                current = again;
            }
        }
        return new NearestWorld(kept.toString(), current);
    }

    private static boolean at(Map<String, String> recorded, Z3.Answer model) {
        for (Map.Entry<String, String> variable : recorded.entrySet()) {
            if (!same(model.values().get(variable.getKey()),
                    variable.getValue())) {
                return false;
            }
        }
        return true;
    }

    private static String pins(Map<String, String> recorded) {
        StringBuilder pins = new StringBuilder();
        for (Map.Entry<String, String> variable : recorded.entrySet()) {
            pins.append(pin(variable.getKey(), variable.getValue()));
        }
        return pins.toString();
    }

    private static String pin(String variable, String literal) {
        return SmtNames.legalSymbols("(assert (= " + variable + " " + literal
                + "))\n");
    }

    static boolean same(String value, String literal) {
        if (value == null) return false;
        if (value.trim().equals(literal.trim())) return true;
        String text = Z3.javaString(value);
        if (text != null) return text.equals(Z3.javaString(literal));
        BigInteger number = integer(value);
        return number != null && number.equals(integer(literal));
    }

    private static BigInteger integer(String value) {
        String text = value.replaceAll("[()\\s]", "");
        try {
            return new BigInteger(text);
        } catch (NumberFormatException notInteger) {
            return null;
        }
    }
}

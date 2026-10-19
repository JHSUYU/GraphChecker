package edu.uva.liftlab.graphchecker.contract;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public final class RunSpellings {
    public static final Pattern UNNAMED = Pattern.compile(
            "\\d{13,}|\\d{1,3}(?:\\.\\d{1,3}){3}:\\d+");

    public static final Pattern IDENTITY = Pattern.compile(
            "((?<![\\w$.])(?:[A-Za-z_$][\\w$]*\\.)*[A-Z][\\w$]*"
                    + "|\\[+(?:[BCDFIJSZ]|L[\\w$.]+;))"
                    + "@[0-9a-f]{1,8}(?![\\w])");

    public static final Pattern SEQUENCE = Pattern.compile(
            "([A-Za-z]+[-_])(\\d{10})(?!\\d)");

    public static final RunSpellings NONE =
            new RunSpellings(Collections.<String[]>emptyList());

    private final List<String[]> spellings;

    private RunSpellings(List<String[]> spellings) {
        this.spellings = Collections.unmodifiableList(spellings);
    }

    public RunSpellings with(String node, String spelling) {
        if (spelling == null || node == null || node.isEmpty()) return this;
        List<String> stated = new ArrayList<String>();
        Matcher inside = UNNAMED.matcher(spelling);
        while (inside.find()) stated.add(inside.group());
        if (stated.isEmpty()) return this;
        stated.add(0, spelling);
        List<String[]> next = new ArrayList<String[]>(spellings);
        for (String each : stated) {
            boolean held = false;
            for (String[] named : next) held |= named[0].equals(each);
            if (!held) next.add(new String[] {each, node});
        }
        if (next.size() == spellings.size()) return this;
        next.sort(Comparator.comparingInt(
                (String[] named) -> named[0].length()).reversed());
        return new RunSpellings(next);
    }

    public String name(String text) {
        if (text == null) return null;
        String named = text;
        for (String[] spelling : spellings) {
            if (named.contains(spelling[0])) {
                named = named.replace(spelling[0], "{" + spelling[1] + "}");
            }
        }
        return named;
    }

    public static String unnamed(String named) {
        Matcher left = UNNAMED.matcher(named == null ? "" : named);
        return left.find() ? left.group() : "";
    }

    public static String strip(String text) {
        int run = 0;
        int longest = 0;
        boolean port = false;
        for (int at = 0; at < text.length(); at++) {
            char c = text.charAt(at);
            run = c >= '0' && c <= '9' ? run + 1 : 0;
            longest = Math.max(longest, run);
            port |= c == ':' && at + 1 < text.length()
                    && Character.isDigit(text.charAt(at + 1));
        }
        String out = text;
        if (longest >= 10) out = SEQUENCE.matcher(out).replaceAll("$1");
        if (longest >= 13 || port) {
            out = UNNAMED.matcher(out).replaceAll("#");
        }
        if (out.indexOf('@') >= 0) {
            out = IDENTITY.matcher(out).replaceAll("$1@");
        }
        return out;
    }

    public Map<String, String> asMap() {
        Map<String, String> map = new TreeMap<String, String>();
        for (String[] spelling : spellings) map.put(spelling[0], spelling[1]);
        return map;
    }

    public static RunSpellings of(Map<String, String> stated) {
        RunSpellings spellings = NONE;
        for (Map.Entry<String, String> each : stated.entrySet()) {
            spellings = spellings.with(each.getValue(), each.getKey());
        }
        return spellings;
    }
}

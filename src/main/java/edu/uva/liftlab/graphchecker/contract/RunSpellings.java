package edu.uva.liftlab.graphchecker.contract;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * The names nodes have only in one run -- the id of a node's store session,
 * its host and port -- each standing for the node's own name, its registered
 * source ({@code runtime.MessageDoors#spelledAs}, stated at the node's
 * start).  What a run spells by them is named by the node, alike in the
 * recording and every replay: the runtime keys a store location so ({@code
 * runtime.RunNames}), each session states them at its close ({@link
 * SessionManifest#runSpellings}), and an arm's key names a written term's
 * constants and observed values so ({@code explore.Corpus#programNames}).
 * An object's identity hash, as the JDK's default {@code toString} spells
 * it ({@code <Class>@<hex>}, also inside a longer string: {@code
 * Searcher@1a2b3c[core] main}), is a run's own name too ({@link
 * #IDENTITY}), but of an object, not a node: only an arm's key names it,
 * by its first appearance there ({@code explore.Corpus#handle}); a store
 * key keeps it, so two objects' paths stay two locations.
 */
public final class RunSpellings {
    /** What spells a run's own name: a long number (a session id, a time)
     *  or a host and port. */
    public static final Pattern UNNAMED = Pattern.compile(
            "\\d{13,}|\\d{1,3}(?:\\.\\d{1,3}){3}:\\d+");

    /** An identity hash after the class name the JDK's default {@code
     *  toString} puts before it: a class (a whole word: its package, if
     *  any, then a name starting upper case, nested names after {@code $})
     *  or an array's ({@code [I}, {@code [Ljava.lang.String;}), {@code @},
     *  and one to eight hex digits no word character follows. */
    public static final Pattern IDENTITY = Pattern.compile(
            "((?<![\\w$.])(?:[A-Za-z_$][\\w$]*\\.)*[A-Z][\\w$]*"
                    + "|\\[+(?:[BCDFIJSZ]|L[\\w$.]+;))"
                    + "@[0-9a-f]{1,8}(?![\\w])");

    public static final RunSpellings NONE =
            new RunSpellings(Collections.<String[]>emptyList());

    /** Spelling and node, the longest spelling first (a host:port inside a
     *  longer one is named as part of it). */
    private final List<String[]> spellings;

    private RunSpellings(List<String[]> spellings) {
        this.spellings = Collections.unmodifiableList(spellings);
    }

    /**
     * These, and {@code spelling} as node {@code node}'s, with each run-only
     * name inside it ({@link #UNNAMED}: a node name's host and port, which a
     * URL spells bare).  A spelling that holds none is no statement (a
     * session not yet connected spells {@code 0}, which would rename every
     * 0); one stated again (a restarted node, a renewed session) is kept
     * once, as first stated.
     */
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

    /** {@code text} with each spelling named by its node, {@code {node}}
     *  (a spelling it does not hold costs a search, never a pattern: an
     *  arm's key names every constant so, solr-adhoc-09 SC7). */
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

    /** The first run-only name {@code named} still spells, or "". */
    public static String unnamed(String named) {
        Matcher left = UNNAMED.matcher(named == null ? "" : named);
        return left.find() ? left.group() : "";
    }

    /** Spelling -> node, as a session's manifest states them. */
    public Map<String, String> asMap() {
        Map<String, String> map = new TreeMap<String, String>();
        for (String[] spelling : spellings) map.put(spelling[0], spelling[1]);
        return map;
    }

    /** The spellings a manifest stated ({@link #asMap}), each as {@link
     *  #with} takes it. */
    public static RunSpellings of(Map<String, String> stated) {
        RunSpellings spellings = NONE;
        for (Map.Entry<String, String> each : stated.entrySet()) {
            spellings = spellings.with(each.getValue(), each.getKey());
        }
        return spellings;
    }
}

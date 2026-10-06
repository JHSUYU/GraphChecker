package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * A MODEL's world, as a replay plants it over a session's (an exploration
 * plants it so, ObligationFactory): every root the model moved, by root id,
 * at the occurrence the recording mints it -- a clock as a skew, any other
 * root as its value.  Read by CONFIRM, which plants it ({@link #plant}), and
 * by CONFIRM and COMPOSE alike to ask whether a session is itself that
 * model's run ({@link #ranBy}).
 *
 * <p>THE CLOCKS ARE THE MODEL'S ALONE.  On every clock cell the composition
 * anchors (its CLOCK roots) the model's clock is its jumps -- the moved
 * cells -- and every other cell runs on from the jump before it; a skew a
 * session planted there would be a jump the model does not make, carried on
 * by the replay's node clock ({@code runtime.NodeClocks}).  A jump's skew is
 * off the reading the composition anchored its cell to: the model's
 * instants are on that timeline, the recording's; the selected session is a
 * later replay whose host read its own (SOLR-18406 a37f2: 1168 s later).</p>
 *
 * <p>A moved root no row of the session or the recording names, one the
 * recording mints nowhere (no occurrence of a replay can be focused to
 * plant it), or a moved clock the composition anchors nowhere is a refusal,
 * named when the model is planted.</p>
 */
public final class Moved {
    /** Non-clock root id -> the model's value. */
    final Map<String, String> values = new LinkedHashMap<String, String>();
    /** Clock root id -> the model's skew off its anchored reading. */
    final Map<String, String> skews = new LinkedHashMap<String, String>();
    /** Root id -> the occurrence the recording mints it at. */
    final Map<String, String> mints = new LinkedHashMap<String, String>();
    /** Every clock root id the composition anchors. */
    final Set<String> anchored = new LinkedHashSet<String>();
    /** Root id -> the value the recording minted it at. */
    final Map<String, String> recorded = new LinkedHashMap<String, String>();
    /** Why a moved root cannot be planted, or "". */
    String refusal = "";

    private Moved() {
    }

    /**
     * The model's {@code movedRoots} (a root id, or a clock cell's symbol,
     * -> its value, or the model's instant) over the composition's clock
     * {@code readings} (every CLOCK root id it anchors -> its reading), each
     * named by the session's or the recording's rows, the recording's first.
     */
    public static Moved of(Map<String, String> movedRoots,
                           Map<String, String> readings,
                           SessionReader session, SessionReader recording) {
        Moved moved = new Moved();
        moved.anchored.addAll(readings.keySet());
        // By root id and by cell symbol; the recording's row first.
        Map<String, RootMintRow> named =
                new LinkedHashMap<String, RootMintRow>();
        Map<String, RootMintRow> minted =
                new LinkedHashMap<String, RootMintRow>();
        for (SessionReader rows : Arrays.asList(recording, session)) {
            for (RootMintRow row : rows.roots()) {
                named.putIfAbsent(row.rootId(), row);
                named.putIfAbsent(row.symbol(), row);
                if (rows == recording) {
                    minted.putIfAbsent(row.rootId(), row);
                    moved.recorded.putIfAbsent(row.rootId(),
                            row.recordedValue());
                }
            }
        }
        for (Map.Entry<String, String> entry : movedRoots.entrySet()) {
            RootMintRow row = named.get(entry.getKey());
            RootMintRow mint = row == null ? null : minted.get(row.rootId());
            if (mint == null) {
                moved.refuse("the claim moves " + entry.getKey()
                        + ", which the recording mints nowhere, so no "
                        + "occurrence of a replay can be focused to plant it");
                continue;
            }
            String model = entry.getValue().trim();
            if (row.kind() == RootKind.CLOCK) {
                String skew = ObligationFactory.skew(model,
                        readings.get(row.rootId()));
                if (skew.isEmpty()) {
                    moved.refuse("the model moves clock cell "
                            + entry.getKey() + " to " + model + " and the "
                            + "composition anchors no reading of it, so no "
                            + "skew states that instant");
                    continue;
                }
                moved.skews.put(row.rootId(), skew);
            } else {
                moved.values.put(row.rootId(), model);
            }
            moved.mints.put(row.rootId(), mint.occurrence().render());
        }
        return moved;
    }

    private void refuse(String why) {
        if (refusal.isEmpty()) refusal = why;
    }

    /** The model planted over the session's world, or refused. */
    void plant(Map<String, String> assignments,
               Map<String, String> clockDeltas,
               Map<String, String> mints) {
        if (!refusal.isEmpty()) throw new ConfirmMain.Refused(refusal);
        clockDeltas.keySet().removeAll(anchored);
        clockDeltas.putAll(skews);
        assignments.putAll(values);
        mints.putAll(this.mints);
    }

    /**
     * Whether {@code session}, run in {@code world}, IS this model's run:
     * the model plants (no refusal), its world planted no pairing (a pairing
     * is a moved choice its own run took under an order the replay held, so
     * CONFIRM makes it again in a replay of its own, strict), it planted no
     * root beyond the model's moved ones at a value other than the
     * recording's (such a world ran another model, which a replay of the
     * claim's own decides), it minted every
     * moved root at the model's value (its mint row), and its clocks are the
     * model's jumps and nothing else ({@link #clocksOf}: skews, each off its
     * own run's host, so the two timelines compare; an instant of the replay
     * is not one of the recording's).  The one test of it: CONFIRM's
     * ({@code ConfirmMain#realizedBy}) and COMPOSE's claim rank
     * ({@code compose.ClaimPolicy}).
     */
    public boolean ranBy(Corpus.World world, SessionReader session) {
        return ranRootsBy(world, session) && clocksOf(world.clockDeltas);
    }

    /** {@link #ranBy} but its clocks: what a model that is not yet refined
     *  (its clocks not yet pinned back) can already be judged by. */
    public boolean ranRootsBy(Corpus.World world, SessionReader session) {
        if (!refusal.isEmpty() || !world.pairings.isEmpty()) return false;
        for (Map.Entry<String, String> planted
                : world.rootAssignments.entrySet()) {
            if (values.containsKey(planted.getKey())) continue;
            String at = recorded.get(planted.getKey());
            if (at == null || !at.trim().equalsIgnoreCase(
                    planted.getValue().trim())) {
                return false;
            }
        }
        Map<String, String> ran = new LinkedHashMap<String, String>();
        for (RootMintRow row : session.roots()) {
            ran.put(row.rootId(), row.recordedValue());
        }
        for (Map.Entry<String, String> value : values.entrySet()) {
            String at = ran.get(value.getKey());
            if (at == null
                    || !at.trim().equalsIgnoreCase(value.getValue())) {
                return false;
            }
        }
        return true;
    }

    /** How many roots and clocks the model moves. */
    int count() {
        return values.size() + skews.size();
    }

    /** Whether this world's clocks are the model's: on every anchored
     *  cell, the same skews planted (a skew compares as a number). */
    private boolean clocksOf(Map<String, String> clockDeltas) {
        Map<String, BigInteger> planted =
                new LinkedHashMap<String, BigInteger>();
        for (Map.Entry<String, String> delta : clockDeltas.entrySet()) {
            if (!anchored.contains(delta.getKey())) continue;
            BigInteger skew = number(delta.getValue());
            if (skew == null) return false;
            planted.put(delta.getKey(), skew);
        }
        Map<String, BigInteger> model =
                new LinkedHashMap<String, BigInteger>();
        for (Map.Entry<String, String> skew : skews.entrySet()) {
            model.put(skew.getKey(), number(skew.getValue()));
        }
        return planted.equals(model);
    }

    private static BigInteger number(String text) {
        try {
            return new BigInteger(text.trim());
        } catch (NumberFormatException notANumber) {
            return null;
        }
    }
}

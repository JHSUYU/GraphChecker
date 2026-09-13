package edu.uva.liftlab.graphchecker.contract;

/**
 * OCC-1: the address of one region occurrence, with or without the
 * activation that ran it.
 *
 * <p>The grammar is {@code <plannedAddress>} optionally followed by
 * {@code #a<ordinal>}: a task plans an address, and one address may be
 * entered several times, so every compatible activation is published as
 * its own occurrence rather than one being answered and the rest reported
 * as an ambiguous address.  A relation, a target reach query and a region
 * plan are all keyed on the planned address the campaign scheduled, so a
 * match between one of them and a per-activation summary is made on the
 * address, not the activation.</p>
 *
 * <p>A string that carries no activation suffix -- a planned address that
 * no activation has claimed yet -- is its own planned address and renders
 * back unchanged.  The ordinal is kept as
 * written rather than as a number so that {@link #render()} reproduces the
 * bytes it parsed.</p>
 */
public final class OccurrenceId {
    private static final String ACTIVATION_MARKER = "#a";
    private static final String REGION_MARKER = "/region/";

    private final String planned;
    private final String activation;

    private OccurrenceId(String planned, String activation) {
        this.planned = planned;
        this.activation = activation;
    }

    /** Reads one occurrence id; a null one reads as the empty address. */
    public static OccurrenceId parse(String occurrenceId) {
        String value = occurrenceId == null ? "" : occurrenceId;
        int marker = value.lastIndexOf(ACTIVATION_MARKER);
        int ordinal = marker + ACTIVATION_MARKER.length();
        if (marker <= 0 || ordinal >= value.length()) {
            return new OccurrenceId(value, "");
        }
        for (int index = ordinal; index < value.length(); index++) {
            if (!Character.isDigit(value.charAt(index))) {
                return new OccurrenceId(value, "");
            }
        }
        return new OccurrenceId(value.substring(0, marker),
                value.substring(ordinal));
    }

    /** The planned address shared by every activation of this occurrence. */
    public String planned() {
        return planned;
    }

    /**
     * The execution source this address belongs to -- the node and epoch the
     * occurrence ran on -- or {@code ""} when the address names none.
     *
     * <p>One message is sent to one peer, so the source is what decides
     * whether two occurrences can be two consumers of one delivery or name
     * two different ones.</p>
     */
    public String sourceKey() {
        int marker = planned.indexOf(REGION_MARKER);
        return marker <= 0 ? "" : planned.substring(0, marker);
    }

    /** This address as the given activation of it. */
    public OccurrenceId withActivation(int activationOrdinal) {
        return new OccurrenceId(planned, String.valueOf(activationOrdinal));
    }

    /** The wire form: the planned address, plus the activation when named. */
    public String render() {
        return activation.isEmpty() ? planned
                : planned + ACTIVATION_MARKER + activation;
    }
}

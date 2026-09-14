package edu.uva.liftlab.graphchecker.contract;

import java.io.UnsupportedEncodingException;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.UUID;

/**
 * The identity of one handoff occurrence, and the VM label minted at it.
 *
 * <p>A handoff occurrence is
 * {@code H = (portId, consumer OccurrenceAddress, k-th attach of that element
 * within the activation, element path)} -- and nothing else. The VM's
 * {@code attachEventId} and {@code exportEventId} are this replay's evidence
 * of H; they are assigned by a live session and differ in every run, so an
 * identity built on them cannot join two replays. The address is
 * {@link OccurrenceAddress#render()}, the planned form without the
 * {@code #a<n>} activation suffix, so H is the same string in the seed and in
 * every replay of it. A loop that attaches the same element on each turn is
 * distinguished by k, which is what makes one variable per turn.</p>
 *
 * <p>This is the same construction {@link ConfiguredSourcePhaseContract}
 * uses for a configured source site, for the same reason: two independent
 * producers of the id have to agree without consulting each other, so the id
 * is a hash of the identity and of nothing else. The answering side then
 * works out of the box -- a handoff assignment is a configured-source
 * assignment whose phase id is this one.</p>
 */
public final class HandoffPhaseContract {
    /** Prefix of every handoff phase id. */
    public static final String PHASE_PREFIX = "HANDOFF_PHASE.";
    /** Prefix of every VM label minted at a handoff. */
    public static final String LABEL_PREFIX = "HOFF.";

    private HandoffPhaseContract() {
    }

    /**
     * The phase id of one handoff occurrence.
     *
     * @param portId           the declared receiving port
     * @param consumerAddress  the consumer occurrence, as
     *                         {@link OccurrenceAddress#render()} spells it
     * @param attachOrdinal    k, the 1-based attach of this element within
     *                         the consumer activation
     * @param elementPath      the element the value landed on, as the exact
     *                         destination field signature
     */
    public static String phaseId(String portId, String consumerAddress,
                                 int attachOrdinal, String elementPath) {
        String identity = required(portId, "portId") + "\n"
                + required(consumerAddress, "consumerAddress") + "\n"
                + positive(attachOrdinal) + "\n"
                + required(elementPath, "elementPath");
        return PHASE_PREFIX + UUID.nameUUIDFromBytes(
                identity.getBytes(StandardCharsets.UTF_8));
    }

    /**
     * The label the VM mints the handoff variable under.
     *
     * <p>Deliberately not the configured source's {@code SRC.} label: a
     * handoff root and a configured-source root must be told apart by name
     * alone, because the importer recognises a configured source mint by the
     * {@code _field_SRC.<label>_} marker inside the root it reads back.</p>
     */
    public static String engineLabelForPhase(String handoffPhaseId,
                                             String portId) {
        return LABEL_PREFIX + sha256(requiredPhaseId(handoffPhaseId) + "\n"
                + required(portId, "portId"));
    }

    /** Whether {@code value} spells a handoff phase id. */
    public static boolean isPhaseId(String value) {
        return value != null && value.startsWith(PHASE_PREFIX)
                && value.length() > PHASE_PREFIX.length();
    }

    private static String requiredPhaseId(String value) {
        if (!isPhaseId(value)) {
            throw new IllegalArgumentException(
                    "handoff phase id is required: " + value);
        }
        return value;
    }

    private static String required(String value, String field) {
        String text = value == null ? "" : value.trim();
        if (text.isEmpty()) {
            throw new IllegalArgumentException(
                    "handoff occurrence requires " + field);
        }
        return text;
    }

    private static int positive(int ordinal) {
        if (ordinal < 1) {
            throw new IllegalArgumentException(
                    "handoff occurrence requires a 1-based attach ordinal");
        }
        return ordinal;
    }

    private static String sha256(String value) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] hash = digest.digest(value.getBytes("UTF-8"));
            StringBuilder rendered = new StringBuilder(hash.length * 2);
            for (byte octet : hash) {
                rendered.append(Character.forDigit((octet >> 4) & 0xF, 16));
                rendered.append(Character.forDigit(octet & 0xF, 16));
            }
            return rendered.toString();
        } catch (NoSuchAlgorithmException | UnsupportedEncodingException
                unsupported) {
            throw new IllegalStateException(unsupported);
        }
    }
}

package edu.uva.liftlab.graphchecker.causynth;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Response decode windows of one region activation.
 *
 * <p>Between the request send and the caller's own result the caller runs
 * nothing but the configured stub's reply decoding.  A field write recorded
 * in that window rebuilds the transferred carrier; it does not produce the
 * value.  Treating it as the authoritative last writer closes the demand
 * chain one hop early and hides the server region that actually produced the
 * value.</p>
 *
 * <p>The declared client/server correspondence is the only authority used
 * here, so no serialization implementation ever has to be analysed.  Windows
 * of one activation are disjoint because a caller sends its next request only
 * after the previous result arrived; an overlap is reported instead of
 * silently picked.</p>
 */
public final class ProtocolCarrierReconstruction {

    /** Response port that carries the value a rebuilt carrier holds. */
    public static final String RESPONSE_PORT = "protocolCarrierResponsePort";

    /** Configured mapping that declares the correspondence. */
    public static final String MAPPING_ID = "protocolCarrierMappingId";

    /** Evidence authority for the penetrated demand. */
    public static final String AUTHORITY = "protocolCarrierAuthority";

    /** Named gap for a carrier leaf without an exact declared projection. */
    public static final String PROJECTION_GAP =
            "protocolCarrierProjectionGap";

    static final String TRUSTED_AUTHORITY =
            "TRUSTED_CONFIGURED_RPC_MAPPING_V1";

    static final String MISSING_PROJECTION =
            "MISSING_EXACT_PROTOCOL_CARRIER_PROJECTION";

    private final Map<Long, List<Window>> windows;

    private ProtocolCarrierReconstruction(Map<Long, List<Window>> windows) {
        this.windows = windows;
    }

    /** Reads the configured response windows out of one region's inputs. */
    public static ProtocolCarrierReconstruction of(
            List<Map<String, Object>> regionInputs) {
        Map<Long, List<Window>> result = new LinkedHashMap<>();
        for (Map<String, Object> port : regionInputs) {
            if (!"PROTOCOL_INPUT".equals(text(port.get("sourceKind")))
                    || !"RESPONSE".equals(first(
                    text(port.get("protocolDirection")),
                    text(port.get("direction"))))
                    || !TRUSTED_AUTHORITY.equals(
                    text(port.get("authority")))) {
                continue;
            }
            long rootCallId = longNumber(port.get("toRootCallId"), -1L);
            long send = longNumber(port.get("sendEventSeq"), -1L);
            long result_ = longNumber(port.get("callerResultEventSeq"), -1L);
            String portId = text(port.get("portId"));
            String mappingId = text(port.get("mappingId"));
            if (rootCallId < 0L || send < 0L || result_ <= send
                    || portId.isEmpty() || mappingId.isEmpty()) {
                continue;
            }
            result.computeIfAbsent(rootCallId, ignored -> new ArrayList<>())
                    .add(new Window(send, result_, portId, mappingId));
        }
        return new ProtocolCarrierReconstruction(result);
    }

    public boolean isEmpty() {
        return windows.isEmpty();
    }

    /**
     * Response port a value written at {@code eventSeq} penetrates to, or an
     * empty string when that write is local production.
     */
    public String responsePortFor(long rootCallId, long eventSeq) {
        Window window = reconstructionOf(rootCallId, eventSeq);
        return window == null ? "" : window.responsePort;
    }

    /**
     * Returns the decode window that rebuilt a value written at
     * {@code eventSeq}, or {@code null} when the write is local production.
     */
    Window reconstructionOf(long rootCallId, long eventSeq) {
        if (eventSeq < 0L) return null;
        Window found = null;
        for (Window window : windows.getOrDefault(rootCallId,
                Collections.<Window>emptyList())) {
            if (eventSeq <= window.sendEventSeq
                    || eventSeq > window.callerResultEventSeq) {
                continue;
            }
            if (found != null) {
                throw new IllegalStateException("configured response decode "
                        + "windows overlap at event " + eventSeq + ": "
                        + found.responsePort + " and " + window.responsePort);
            }
            found = window;
        }
        return found;
    }

    /** Records the penetrated demand on one port. */
    static void mark(Map<String, Object> port, Window window,
                     boolean projected) {
        port.put(RESPONSE_PORT, window.responsePort);
        port.put(MAPPING_ID, window.mappingId);
        port.put(AUTHORITY, TRUSTED_AUTHORITY);
        if (projected) {
            port.remove(PROJECTION_GAP);
        } else {
            port.put(PROJECTION_GAP, MISSING_PROJECTION);
        }
    }

    /** Response port a demanded port penetrates to, or an empty string. */
    public static String responsePort(Map<String, Object> port) {
        return port == null ? "" : text(port.get(RESPONSE_PORT));
    }

    private static String first(String value, String fallback) {
        return value.isEmpty() ? fallback : value;
    }

    private static String text(Object value) {
        return value == null ? "" : String.valueOf(value);
    }

    private static long longNumber(Object value, long fallback) {
        if (value instanceof Number) return ((Number) value).longValue();
        try {
            return Long.parseLong(text(value).trim());
        } catch (RuntimeException invalid) {
            return fallback;
        }
    }

    static final class Window {
        private final long sendEventSeq;
        private final long callerResultEventSeq;
        private final String responsePort;
        private final String mappingId;

        private Window(long sendEventSeq, long callerResultEventSeq,
                       String responsePort, String mappingId) {
            this.sendEventSeq = sendEventSeq;
            this.callerResultEventSeq = callerResultEventSeq;
            this.responsePort = responsePort;
            this.mappingId = mappingId;
        }
    }
}

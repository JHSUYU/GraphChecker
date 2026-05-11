package edu.uva.liftlab.graphchecker.grey;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;
import java.security.MessageDigest;
import java.nio.charset.StandardCharsets;

public final class SemanticEvent {
    private final String eventType;
    private final String method;
    private final String unit;
    private final Map<String, String> attributes;

    public SemanticEvent(String eventType, String method, String unit, Map<String, String> attributes) {
        this.eventType = eventType;
        this.method = method;
        this.unit = unit;
        this.attributes = new LinkedHashMap<String, String>();
        if (attributes != null) {
            this.attributes.putAll(attributes);
        }
    }

    public String getEventType() {
        return eventType;
    }

    public String getMethod() {
        return method;
    }

    public String getUnit() {
        return unit;
    }

    public Map<String, String> getAttributes() {
        return attributes;
    }

    public String stableId() {
        return eventType + ":" + sha1(eventType + "\n" + method + "\n" + unit + "\n" + attributes.toString());
    }

    private static String sha1(String text) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-1");
            byte[] bytes = digest.digest(text.getBytes(StandardCharsets.UTF_8));
            StringBuilder out = new StringBuilder();
            for (byte b : bytes) {
                String hex = Integer.toHexString(b & 0xff);
                if (hex.length() == 1) {
                    out.append('0');
                }
                out.append(hex);
            }
            return out.toString();
        } catch (Exception exception) {
            return Integer.toHexString(text.hashCode());
        }
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof SemanticEvent)) {
            return false;
        }
        SemanticEvent that = (SemanticEvent) o;
        return Objects.equals(eventType, that.eventType)
                && Objects.equals(method, that.method)
                && Objects.equals(unit, that.unit)
                && Objects.equals(attributes, that.attributes);
    }

    @Override
    public int hashCode() {
        return Objects.hash(eventType, method, unit, attributes);
    }
}

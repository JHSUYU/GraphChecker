package edu.uva.liftlab.graphchecker.contract;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * CONTRACT-SPEC §2.2: one typed piece of one leaf of one message a codec
 * carried: the codec that wrote the message, the key path from the
 * message's root to the leaf, and the hole's index in the leaf's template.
 * The message is the row's own ({@link ExportRow#messageKey},
 * {@link AttachRow#correlationId}).  A key path component is a map key or a
 * NamedList name (a String, {@code name#k} for a name's k-th repeat) or a
 * list or array index (an Integer); the empty path is a leaf that is the
 * whole message.
 */
public final class Hole extends Value {
    private final String codec;
    private final List<Object> keyPath;
    private final int index;

    private Hole(String codec, List<Object> keyPath, int index) {
        this.codec = codec;
        this.keyPath = keyPath;
        this.index = index;
    }

    public static Hole of(String codec, List<?> keyPath, int index) {
        List<Object> path = new ArrayList<Object>();
        for (Object component : Fields.required(keyPath, "keyPath")) {
            if (component instanceof Integer) {
                path.add(Fields.nonNegative((Integer) component,
                        "keyPath index"));
            } else if (component instanceof String) {
                path.add(component);
            } else {
                throw new IllegalArgumentException("a keyPath component is a "
                        + "String key or an int index; got " + component);
            }
        }
        return new Hole(Fields.text(codec, "codec"),
                Collections.unmodifiableList(path),
                Fields.nonNegative(index, "hole"));
    }

    /** The codec that wrote the message. */
    public String codec() {
        return codec;
    }

    /** The components, String keys and Integer indexes, root first. */
    public List<Object> keyPath() {
        return keyPath;
    }

    /** The hole's index in its leaf's template, from 0. */
    public int index() {
        return index;
    }

    /**
     * The key path's text form, {@code /a/b[3]/c}: a key after {@code /}
     * with {@code % / [ ]} escaped as {@code %25 %2F %5B %5D}, an index in
     * brackets; the empty path is {@code ""}.
     */
    public String path() {
        StringBuilder text = new StringBuilder();
        for (Object component : keyPath) {
            if (component instanceof Integer) {
                text.append('[').append(component).append(']');
                continue;
            }
            text.append('/');
            for (char c : ((String) component).toCharArray()) {
                if (c == '%') text.append("%25");
                else if (c == '/') text.append("%2F");
                else if (c == '[') text.append("%5B");
                else if (c == ']') text.append("%5D");
                else text.append(c);
            }
        }
        return text.toString();
    }

    /** {@code <codec>:<path>#<index>}: the hole within its message. */
    public String render() {
        return codec + ":" + path() + "#" + index;
    }

    @Override
    Object[] parts() {
        return new Object[] {codec, keyPath, index};
    }

    @Override
    public String toString() {
        return render();
    }
}

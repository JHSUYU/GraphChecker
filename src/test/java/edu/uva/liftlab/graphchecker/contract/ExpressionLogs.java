package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/** A session's expression log as a run writes it, for synthetic sessions. */
public final class ExpressionLogs {
    private ExpressionLogs() {
    }

    public static void write(Path file, Map<String, JsonObject> expressions)
            throws IOException {
        SessionExpressionLog.Writer log = new SessionExpressionLog.Writer();
        List<JsonObject> lines = new ArrayList<>();
        lines.add(SessionExpressionLog.header());
        for (Map.Entry<String, JsonObject> entry : expressions.entrySet()) {
            lines.addAll(log.lines(entry.getKey(), entry.getValue()));
        }
        RowCodec.writeJsonl(file, lines);
    }
}

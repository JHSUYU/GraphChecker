package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.Map;

final class Fixtures {
    private static final List<Long> OPENED = new ArrayList<>();

    private Fixtures() {
    }

    static JsonObject json(String text) {
        return JsonParser.parseString(text.replace('\'', '"'))
                .getAsJsonObject();
    }

    static JsonObject with(JsonObject row, String members) {
        for (Map.Entry<String, JsonElement> member
                : json("{" + members + "}").entrySet()) {
            row.add(member.getKey(), member.getValue());
        }
        return row;
    }

    static JsonObject taskRow(String source, String occurrence, String method,
                              boolean named, String members) {
        return with(json("{'taskId':'TASK.1','goalId':'GOAL.1','goalKind':"
                + "'REGION_PATH_CLOSURE','regionId':'REGION.1','relationKey':"
                + "'REL.1','sourceKey':'" + source + "','occurrenceId':'"
                + occurrence + "','rootMethod':'" + method + "',"
                + "'instrumentationSelector':'sel','admission':{'state':"
                + "'EXECUTABLE'},'rootSelector':{'kind':'GLOBAL_INVOCATION',"
                + "'invocationOrdinal':1," + (named ? "'method':'" + method
                + "'," : "") + "'causalAnchor':{'sourceKey':'" + source
                + "','kind':'REGISTERED_SOURCE'}},'branchMethods':[],"
                + "'inputActions':[],'loopBound':{'schemaVersion':1,"
                + "'defaultBackedgeTraversals':8}}"), members);
    }

    static ConcolicTaskPlan.RuntimeTask runtimeTask(JsonObject row) {
        return new ConcolicTaskPlan.RuntimeTask(ExecutionTask.decode(row));
    }

    static ActiveRegion region(long token, JsonObject row) {
        return new ActiveRegion(token, runtimeTask(row), null,
                Thread.currentThread());
    }

    static ActiveRegion live(ActiveRegion active) {
        ConcolicRegionRuntime.ACTIVE.put(active.token, active);
        OPENED.add(active.token);
        return active;
    }

    static ActiveRegion pushed(ActiveRegion active) {
        live(active);
        tokens().push(active.token);
        return active;
    }

    static void release() {
        OPENED.forEach(ConcolicRegionRuntime.ACTIVE::remove);
        OPENED.clear();
        tokens().clear();
    }

    @SuppressWarnings("unchecked")
    static Deque<Long> tokens() {
        return ((ThreadLocal<Deque<Long>>) get(ConcolicRegionRuntime.class,
                "CURRENT_TOKENS")).get();
    }

    static Object get(Object owner, String name) {
        try {
            return field(owner, name).get(owner instanceof Class ? null
                    : owner);
        } catch (ReflectiveOperationException failure) {
            throw new IllegalStateException(failure);
        }
    }

    static void set(Object owner, String name, Object value) {
        try {
            field(owner, name).set(owner instanceof Class ? null : owner,
                    value);
        } catch (ReflectiveOperationException failure) {
            throw new IllegalStateException(failure);
        }
    }

    static Object call(Object owner, String name, Class<?>[] types,
                       Object... arguments) throws Exception {
        Class<?> type = owner instanceof Class ? (Class<?>) owner
                : owner.getClass();
        Method method = type.getDeclaredMethod(name, types);
        method.setAccessible(true);
        return method.invoke(owner instanceof Class ? null : owner,
                arguments);
    }

    private static Field field(Object owner, String name)
            throws NoSuchFieldException {
        Class<?> type = owner instanceof Class ? (Class<?>) owner
                : owner.getClass();
        Field field = type.getDeclaredField(name);
        field.setAccessible(true);
        return field;
    }

    static void openSession(Path root) throws Exception {
        Path results = root.resolve("iteration-0000").resolve("seed-result")
                .resolve("concolic_region_results.jsonl");
        Files.createDirectories(results.getParent());
        RowRuntime.configure(results);
    }

    static SessionDir session(Path root) {
        return SessionDir.of(root.resolve("iteration-0000"),
                RowRuntime.sessionId());
    }

    static List<GapRow> gaps(Path root) throws Exception {
        return RowCodec.readAll(session(root).gaps(), RowCodec::readGap);
    }

    static GapRow lastGap(Path root) throws Exception {
        List<GapRow> rows = gaps(root);
        return rows.isEmpty() ? null : rows.get(rows.size() - 1);
    }

    static String focusRow(String focused, String members) {
        return with(json("{'taskId':'T','obligationId':'OB','pathId':'p',"
                + "'focused':'" + focused + "','focusedOccurrenceId':'"
                + OccurrenceAddress.parse(focused).id() + "',"
                + "'seedSessionId':'seed','flip':null,'inheritedFlips':[],"
                + "'rootAssignments':{},'clockDeltas':{},'answers':{},"
                + "'rootMints':{}}"), members).toString();
    }

    static void focus(Path worker, String... rows) throws Exception {
        Files.write(worker.resolve(ObligationDir.FOCUSED_TASK),
                (String.join("\n", rows) + "\n")
                        .getBytes(StandardCharsets.UTF_8));
        Path plan = worker.resolve("execution_task_plan.jsonl");
        Files.write(plan, new byte[0]);
        System.setProperty(FocusedReplay.PLAN_PROPERTY, plan.toString());
    }

    static JsonObject symbol(String name, String javaType) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "SymbolExpression");
        node.addProperty("_exp", name);
        node.addProperty("_java_type", javaType);
        return node;
    }
}

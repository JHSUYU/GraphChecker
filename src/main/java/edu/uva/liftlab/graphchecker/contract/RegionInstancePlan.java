package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.CanonicalJson;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Once-decoded execution goals for one concrete region invocation. */
public final class RegionInstancePlan {
    public static final String OCCURRENCE_CATALOG =
            "occurrenceInstantiationCatalog";
    private final JsonObject encoded;
    private final List<Goal> goals;

    private RegionInstancePlan(JsonObject encoded) {
        this.encoded = encoded;
        if (regionId().isEmpty() || regionInstanceId().isEmpty()) {
            throw new IllegalArgumentException(
                    "region plan requires regionId and regionInstanceId");
        }
        List<Goal> decoded = new ArrayList<>();
        Set<String> ids = new LinkedHashSet<>();
        for (JsonElement element : array(encoded, "closureGoals")) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "closureGoals must contain objects for "
                                + regionInstanceId());
            }
            Goal goal = new Goal(this, element.getAsJsonObject());
            if (!ids.add(goal.goalId())) {
                throw new IllegalArgumentException(
                        "closure goal ids must be nonempty and unique for "
                                + regionInstanceId());
            }
            decoded.add(goal);
        }
        goals = Collections.unmodifiableList(decoded);
    }

    public static RegionInstancePlan decode(JsonObject encoded) {
        if (encoded == null) {
            throw new IllegalArgumentException("region plan is required");
        }
        return new RegionInstancePlan(encoded);
    }

    public String regionId() {
        return string(encoded, "regionId");
    }

    public String regionInstanceId() {
        return string(encoded, "regionInstanceId");
    }

    public String logicalRegionId() {
        String logical = string(encoded, "logicalRegionId");
        return logical.isEmpty() ? regionInstanceId() : logical;
    }

    public int logicalInstanceCount() {
        return integer(encoded, "logicalInstanceCount", 1);
    }

    public JsonArray occurrences() {
        return array(encoded, "occurrences").deepCopy();
    }

    public boolean containsRegionInstance(String instance) {
        if (regionInstanceId().equals(instance)) return true;
        for (JsonElement element : array(encoded, "occurrences")) {
            if (element.isJsonObject()
                    && instance.equals(string(element.getAsJsonObject(),
                    "regionInstanceId"))) {
                return true;
            }
        }
        return false;
    }

    public List<Goal> goals() {
        return goals;
    }

    void writeTaskIdentityTo(JsonObject target) {
        target.addProperty("regionId", regionId());
        target.addProperty("regionInstanceId", regionInstanceId());
        target.addProperty("logicalRegionId", logicalRegionId());
        target.addProperty("logicalInstanceCount", logicalInstanceCount());
        target.addProperty("summaryReuseKey", firstNonBlank(
                string(encoded, "summaryReuseKey"), logicalRegionId()));
        copyIfPresent(encoded, target, "rootSelector");
        copyIfPresent(encoded, target, "targetMethod");
        if (encoded.has("rootCallId")) {
            target.addProperty("rootCallId",
                    longInteger(encoded, "rootCallId", 0L));
        }
    }

    public static final class Goal {
        private final RegionInstancePlan plan;
        private final JsonObject encoded;
        private final ClosureGoalKind kind;
        private final Set<String> runtimeDefinitionMethods;
        private final OutputClosureContract outputClosure;

        private Goal(RegionInstancePlan plan, JsonObject encoded) {
            this.plan = plan;
            this.encoded = encoded;
            if (goalId().isEmpty()) {
                throw new IllegalArgumentException(
                        "closure goal ids must be nonempty and unique for "
                                + plan.regionInstanceId());
            }
            try {
                kind = ClosureGoalKind.fromGoal(encoded);
            } catch (RuntimeException invalid) {
                throw new IllegalArgumentException(
                        "goal kind must be OUTPUT_RELATION_CLOSURE or "
                                + "TARGET_REACH_CLOSURE");
            }
            runtimeDefinitionMethods = decodeRuntimeDefinitionMethods();
            outputClosure = encoded.has(OutputClosureContract.FIELD)
                    ? decodeOutputClosure() : null;
        }

        public RegionInstancePlan plan() {
            return plan;
        }

        public String goalId() {
            return string(encoded, "goalId");
        }

        public String pathSeedKey() {
            return string(encoded, "pathSeedKey");
        }

        public ClosureGoalKind kind() {
            return kind;
        }

        public boolean replayable() {
            String admissionState = admissionState();
            return "READY".equals(admissionState)
                    || "DISCOVERED".equals(admissionState);
        }

        public String admissionState() {
            return string(object(encoded, "admission"), "state");
        }

        public JsonArray admissionBlockers() {
            return array(object(encoded, "admission"), "blockers");
        }

        public Set<String> runtimeDefinitionMethods() {
            return runtimeDefinitionMethods;
        }

        private Set<String> decodeRuntimeDefinitionMethods() {
            JsonElement definitions = encoded.get(
                    "runtimeDefinitionMethods");
            if (definitions == null || !definitions.isJsonArray()) {
                throw new IllegalArgumentException(
                        "closure goal requires runtimeDefinitionMethods array: "
                                + plan.regionInstanceId());
            }
            Set<String> methods = new LinkedHashSet<>();
            for (JsonElement method : definitions.getAsJsonArray()) {
                if (!method.isJsonPrimitive()
                        || !method.getAsJsonPrimitive().isString()
                        || method.getAsString().trim().isEmpty()) {
                    throw new IllegalArgumentException(
                            "runtimeDefinitionMethods must contain nonempty "
                                    + "strings: "
                                    + plan.regionInstanceId());
                }
                methods.add(method.getAsString().trim());
            }
            return Collections.unmodifiableSet(methods);
        }

        private OutputClosureContract decodeOutputClosure() {
            OutputClosureContract contract =
                    OutputClosureCodec.decode(encoded);
            OutputClosureContract.Producer producer = contract.producer();
            if (!plan.regionId().equals(producer.regionId())
                    || !executionRegionInstanceId().equals(
                    producer.regionInstanceId())
                    || executionRootCallId() >= 0L
                    && executionRootCallId()
                    != producer.rootCallId()) {
                throw new IllegalArgumentException(
                        "outputClosure producer conflicts with artifact scope");
            }
            return contract;
        }

        public OutputClosureContract outputClosure() {
            return outputClosure;
        }

        public void rejectOutputClosure() {
            if (encoded.has(OutputClosureContract.FIELD)) {
                throw new IllegalArgumentException(
                        "outputClosure requires OUTPUT_RELATION_CLOSURE");
            }
        }

        public JsonArray symbolize() {
            return array(encoded, "symbolize");
        }

        public JsonArray branches() {
            return array(encoded, "branches");
        }

        public JsonArray edgeBindings() {
            return array(encoded, "edgeBindings");
        }

        /**
         * Compact exact-occurrence adapter for one shared VM relation.
         * Full occurrence plans remain in the planner artifact; executable
         * tasks carry only identities, exact causal binding ids and the
         * canonical-to-exact port bijection required by composition.
         */
        public JsonObject occurrenceInstantiationCatalog() {
            JsonObject result = new JsonObject();
            result.addProperty("schemaVersion", 1);
            result.addProperty("kind",
                    "LOGICAL_SUMMARY_OCCURRENCE_CATALOG");
            result.addProperty("logicalRegionId", plan.logicalRegionId());
            result.addProperty("summaryReuseKey", firstNonBlank(
                    string(plan.encoded, "summaryReuseKey"),
                    plan.logicalRegionId()));
            result.addProperty("canonicalRegionInstanceId",
                    executionRegionInstanceId());
            if (executionRootCallId() >= 0L) {
                result.addProperty("canonicalRootCallId",
                        executionRootCallId());
            }

            String semanticKey = semanticGoalKey(encoded,
                    plan.regionId());
            List<JsonObject> sourceOccurrences = occurrenceRows();
            JsonArray catalog = new JsonArray();
            for (JsonObject occurrence : sourceOccurrences) {
                JsonObject exactGoal = exactGoal(occurrence, semanticKey);
                if (exactGoal.size() == 0) continue;
                JsonObject item = occurrenceIdentity(occurrence);
                item.add("inputPortMap", portMap(
                        array(encoded, "symbolize"),
                        array(exactGoal, "symbolize"), false,
                        string(occurrence, "regionInstanceId")));
                item.add("outputPortMap", portMap(
                        closureMembers(encoded), closureMembers(exactGoal),
                        true, string(occurrence, "regionInstanceId")));
                item.add("bindingIds", bindingIds(
                        string(occurrence, "regionInstanceId")));
                catalog.add(item);
            }
            if (catalog.size() == 0) {
                throw new IllegalArgumentException(
                        "logical summary goal has no exact occurrence: "
                                + goalId());
            }
            boolean canonicalFound = false;
            Set<String> instances = new LinkedHashSet<>();
            for (JsonElement element : catalog) {
                JsonObject occurrence = element.getAsJsonObject();
                String instance = string(occurrence, "regionInstanceId");
                if (!instances.add(instance)) {
                    throw new IllegalArgumentException(
                            "duplicate summary occurrence " + instance);
                }
                canonicalFound |= executionRegionInstanceId().equals(
                        instance);
            }
            if (!canonicalFound) {
                throw new IllegalArgumentException(
                        "canonical execution occurrence is missing from "
                                + "logical summary catalog: "
                                + executionRegionInstanceId());
            }
            result.add("occurrences", catalog);
            return result;
        }

        private List<JsonObject> occurrenceRows() {
            List<JsonObject> result = new ArrayList<>();
            for (JsonElement element : array(plan.encoded,
                    "occurrences")) {
                if (element.isJsonObject()) {
                    result.add(element.getAsJsonObject());
                }
            }
            if (result.isEmpty()) {
                JsonObject singleton = plan.encoded.deepCopy();
                singleton.add("closureGoals", new JsonArray());
                singleton.getAsJsonArray("closureGoals")
                        .add(encoded.deepCopy());
                result.add(singleton);
            }
            result.sort(Comparator.comparingLong(value ->
                    longInteger(value, "rootCallId", Long.MAX_VALUE)));
            return result;
        }

        private JsonObject exactGoal(JsonObject occurrence,
                                     String semanticKey) {
            List<JsonObject> matches = new ArrayList<>();
            for (JsonElement element : array(occurrence,
                    "closureGoals")) {
                if (element.isJsonObject()
                        && semanticKey.equals(semanticGoalKey(
                        element.getAsJsonObject(), plan.regionId()))) {
                    matches.add(element.getAsJsonObject());
                }
            }
            if (matches.size() > 1) {
                String contract = exactExecutionContract(matches.get(0));
                for (int index = 1; index < matches.size(); index++) {
                    if (!contract.equals(exactExecutionContract(
                            matches.get(index)))) {
                        throw new IllegalArgumentException(
                                "conflicting exact goals for occurrence "
                                        + string(occurrence,
                                        "regionInstanceId"));
                    }
                }
                // Planner aggregation can repeat an otherwise identical
                // exact goal through several selected outputs.  Goal ids do
                // not change the VM contract, so collapse those duplicates
                // deterministically.  Any contract difference above remains
                // fail-closed.
                matches.sort(Comparator
                        .comparing((JsonObject value) ->
                                string(value, "goalId"))
                        .thenComparing(CanonicalJson::render));
            }
            return matches.isEmpty() ? new JsonObject() : matches.get(0);
        }

        /**
         * Stable VM contract for duplicate exact-goal detection.
         *
         * <p>Absolute trace positions and heap identities are evidence for
         * this run, not part of a replayable relation.  Consumer-edge ledgers
         * are composition metadata and are likewise excluded; the logical
         * goal retains their union.  Everything that can affect VM
         * materialization, branch selection or output capture is retained.
         * Arrays whose wire meaning is a set are sorted before comparison.</p>
         */
        private static String exactExecutionContract(JsonObject goal) {
            Set<String> outgoingLedgers = outgoingConsumerLedgerIds(goal);
            JsonObject contract = new JsonObject();
            for (Map.Entry<String, JsonElement> field
                    : goal.entrySet()) {
                String name = field.getKey();
                if ("goalId".equals(name)
                        || "baselineObservedMethods".equals(name)
                        || "excludedOutputBlockers".equals(name)
                        || runtimeIdentityField(name)) {
                    continue;
                }
                contract.add(name, stableContractValue(
                        name, field.getValue(), outgoingLedgers));
            }
            return CanonicalJson.render(contract);
        }

        private static JsonElement stableContractValue(
                String field, JsonElement value,
                Set<String> outgoingLedgers) {
            if (value == null || value.isJsonNull()
                    || value.isJsonPrimitive()) {
                return value == null ? com.google.gson.JsonNull.INSTANCE
                        : value.deepCopy();
            }
            if (value.isJsonObject()) {
                JsonObject result = new JsonObject();
                for (Map.Entry<String, JsonElement> entry
                        : value.getAsJsonObject().entrySet()) {
                    String name = entry.getKey();
                    if ("goalId".equals(name)
                            || runtimeIdentityField(name)) {
                        continue;
                    }
                    result.add(name, stableContractValue(
                            name, entry.getValue(), outgoingLedgers));
                }
                return result;
            }

            List<JsonElement> elements = new ArrayList<>();
            for (JsonElement element : value.getAsJsonArray()) {
                if (outgoingLedgerElement(field, element,
                        outgoingLedgers)) {
                    continue;
                }
                // The containing field decides whether this array is a set;
                // nested arrays (notably ordered field paths) keep order.
                elements.add(stableContractValue("", element,
                        outgoingLedgers));
            }
            if (setValuedContractField(field)) {
                elements.sort(Comparator.comparing(CanonicalJson::render));
            }
            JsonArray result = new JsonArray();
            for (JsonElement element : elements) result.add(element);
            return result;
        }

        private static Set<String> outgoingConsumerLedgerIds(
                JsonObject goal) {
            Set<String> outputs = new LinkedHashSet<>();
            for (JsonElement element : closureMembers(goal)) {
                if (!element.isJsonObject()) continue;
                String port = portId(element.getAsJsonObject(), true);
                if (!port.isEmpty()) outputs.add(port);
            }
            String producerInstance = string(object(object(goal,
                    OutputClosureContract.FIELD), "producer"),
                    "regionInstanceId");
            Set<String> result = new LinkedHashSet<>();
            for (JsonElement element : array(goal, "edgeBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                String edgeId = string(binding, "edgeId");
                String fromPort = firstNonBlank(string(binding,
                        "fromOutputPort"), string(binding, "fromPort"));
                boolean exactProducer = !producerInstance.isEmpty()
                        && producerInstance.equals(string(binding,
                        "fromRegionInstance"));
                if (!edgeId.isEmpty()
                        && (exactProducer || outputs.contains(fromPort))) {
                    result.add(edgeId);
                }
            }
            return result;
        }

        /**
         * Only an outgoing binding named by the exact goal proves that an
         * edge id is a consumer ledger.  Slice-internal causal ids remain
         * part of the VM contract even when they happen to use the same
         * field name.
         */
        private static boolean outgoingLedgerElement(
                String field, JsonElement element,
                Set<String> outgoingLedgers) {
            if (outgoingLedgers.isEmpty()) return false;
            if ("causalEdgeIds".equals(field)
                    && element.isJsonPrimitive()
                    && element.getAsJsonPrimitive().isString()) {
                return outgoingLedgers.contains(element.getAsString());
            }
            if (("edgeBindings".equals(field)
                    || "causalEdges".equals(field))
                    && element.isJsonObject()) {
                return outgoingLedgers.contains(string(
                        element.getAsJsonObject(), "edgeId"));
            }
            return false;
        }

        private static boolean setValuedContractField(String field) {
            return "runtimeDefinitionMethods".equals(field)
                    || "symbolize".equals(field)
                    || "branches".equals(field)
                    || "edgeBindings".equals(field)
                    || "members".equals(field)
                    || "causalEdges".equals(field)
                    || "inputPorts".equals(field)
                    || "sites".equals(field)
                    || "staticSites".equals(field)
                    || "methods".equals(field)
                    || "causalEdgeIds".equals(field)
                    || "captureBindings".equals(field)
                    || "captureBindingIssues".equals(field)
                    || "operandCells".equals(field)
                    || "occurrences".equals(field)
                    || "runtimeAccesses".equals(field)
                    || "dependencyCells".equals(field)
                    || "fieldPaths".equals(field)
                    || "blockers".equals(field);
        }

        private static boolean runtimeIdentityField(String field) {
            String normalized = field == null ? ""
                    : field.trim().toLowerCase(java.util.Locale.ROOT);
            return normalized.equals("activationid")
                    || normalized.endsWith("callid")
                    || normalized.endsWith("invocationid")
                    || normalized.endsWith("seq")
                    || normalized.endsWith("objectid")
                    || normalized.endsWith("objectids")
                    || normalized.endsWith("rootcallid")
                    || normalized.endsWith("regioninstanceid")
                    || normalized.equals("fromregioninstance")
                    || normalized.equals("toregioninstance")
                    || normalized.endsWith("ownerid")
                    || normalized.endsWith("laneid")
                    || normalized.endsWith("spanid")
                    || normalized.endsWith("threadid");
        }

        private JsonObject occurrenceIdentity(JsonObject occurrence) {
            JsonObject result = new JsonObject();
            copyIfPresent(occurrence, result, "regionInstanceId");
            copyIfPresent(occurrence, result, "activationId");
            copyIfPresent(occurrence, result, "rootCallId");
            copyIfPresent(occurrence, result, "ownerId");
            copyIfPresent(occurrence, result, "laneId");
            copyIfPresent(occurrence, result, "spanId");
            copyIfPresent(occurrence, result, "parentSpanId");
            copyIfPresent(occurrence, result, "remoteParentSpanId");
            if (string(result, "regionInstanceId").isEmpty()) {
                throw new IllegalArgumentException(
                        "summary occurrence requires regionInstanceId");
            }
            return result;
        }

        private JsonArray bindingIds(String instance) {
            Set<String> ids = new LinkedHashSet<>();
            for (JsonElement element : edgeBindings()) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                if (!instance.equals(string(binding,
                        "fromRegionInstance"))
                        && !instance.equals(string(binding,
                        "toRegionInstance"))) {
                    continue;
                }
                String id = string(binding, "edgeId");
                if (id.isEmpty()) {
                    throw new IllegalArgumentException(
                            "exact occurrence binding requires edgeId: "
                                    + instance);
                }
                ids.add(id);
            }
            JsonArray result = new JsonArray();
            for (String id : ids) result.add(id);
            return result;
        }

        private static JsonArray closureMembers(JsonObject goal) {
            return array(object(goal, OutputClosureContract.FIELD),
                    "members");
        }

        private static JsonArray portMap(JsonArray canonical,
                                         JsonArray exact,
                                         boolean output,
                                         String occurrenceInstance) {
            Map<String, String> exactByShape = indexPorts(exact, output,
                    "exact", occurrenceInstance);
            Set<String> canonicalShapes = new LinkedHashSet<>();
            JsonArray result = new JsonArray();
            for (JsonElement element : canonical) {
                if (!element.isJsonObject()) continue;
                JsonObject port = element.getAsJsonObject();
                String shape = portShape(port, output);
                if (!canonicalShapes.add(shape)) {
                    throw new IllegalArgumentException(
                            "ambiguous canonical port shape for "
                                    + occurrenceInstance + ": " + shape);
                }
                String canonicalPort = portId(port, output);
                String exactPort = exactByShape.get(shape);
                if (canonicalPort.isEmpty() || exactPort == null
                        || exactPort.isEmpty()) {
                    throw new IllegalArgumentException(
                            "missing exact port mapping for "
                                    + occurrenceInstance + ": " + shape);
                }
                JsonObject mapping = new JsonObject();
                mapping.addProperty("canonicalPort", canonicalPort);
                mapping.addProperty("exactPort", exactPort);
                result.add(mapping);
            }
            return result;
        }

        private static Map<String, String> indexPorts(
                JsonArray ports, boolean output, String label,
                String occurrenceInstance) {
            Map<String, String> result = new LinkedHashMap<>();
            for (JsonElement element : ports) {
                if (!element.isJsonObject()) continue;
                JsonObject port = element.getAsJsonObject();
                String shape = portShape(port, output);
                String prior = result.putIfAbsent(shape,
                        portId(port, output));
                if (prior != null) {
                    throw new IllegalArgumentException("ambiguous " + label
                            + " port shape for " + occurrenceInstance
                            + ": " + shape);
                }
            }
            return result;
        }

        private static String portId(JsonObject port, boolean output) {
            JsonObject value = output ? object(port, "output") : port;
            return firstNonBlank(string(value, "portId"),
                    string(value, "symbol"));
        }

        private static String portShape(JsonObject port, boolean output) {
            JsonObject value = output ? object(port, "output") : port;
            JsonObject shape = new JsonObject();
            copyIfPresent(value, shape, "cell");
            copyIfPresent(value, shape, "kind");
            copyIfPresent(value, shape, "javaTypeDescriptor");
            copyIfPresent(value, shape, "location");
            copyIfPresent(value, shape, "javaType");
            copyIfPresent(value, shape, "sourceKind");
            copyIfPresent(value, shape, "rootKind");
            copyIfPresent(value, shape, "rootParameterIndex");
            copyIfPresent(value, shape, "argumentIndex");
            copyIfPresent(value, shape, "index");
            copyIfPresent(value, shape, "bindingMode");
            copyIfPresent(value, shape, "dependencyRole");
            copyIfPresent(value, shape, "fieldPath");
            copyIfPresent(value, shape, "fieldPaths");
            copyIfPresent(value, shape, "outputSiteId");
            copyIfPresent(value, shape, "outputOccurrence");
            // Two replies of one repeated call are the same cell, type and
            // boundary; only their position in the activation's own send
            // order tells them apart, and the path decides that order.
            copyIfPresent(value, shape, "protocolExchangeOccurrence");
            // Repeated accessor/container reads can intentionally expose the
            // same declared field several times in one bounded activation.
            // Their invocation-local ordinal plus static call/declaration
            // identity is the stable slot key across exact occurrences.
            // Runtime call/object/value ids are deliberately excluded.
            copyIfPresent(value, shape, "accessorOccurrence");
            copyIfPresent(value, shape, "replayOccurrence");
            copyIfPresent(value, shape,
                    "helperActivationBoundedOccurrence");
            copyIfPresent(value, shape, "containerAccessOrdinal");
            copyIfPresent(value, shape, "siteId");
            copyIfPresent(value, shape, "unitIndex");
            copyIfPresent(value, shape, "callerMethod");
            copyIfPresent(value, shape, "declaredCallee");
            copyIfPresent(value, shape, "implementationMethod");
            copyIfPresent(value, shape, "accessorCallerMethod");
            copyIfPresent(value, shape, "accessorCallUnitIndex");
            copyIfPresent(value, shape, "accessorDeclaredCallee");
            copyIfPresent(value, shape, "accessorImplementationMethod");
            copyIfPresent(value, shape, "declaredFieldSignature");
            copyIfPresent(value, shape, "accessFieldSignature");
            copyIfPresent(value, shape, "leafFieldSignature");
            copyIfPresent(value, shape, "fieldPathDeclarations");
            copyIfPresent(value, shape, "accessSites");
            copyIfPresent(value, shape, "materialization");
            if (output) {
                JsonObject slice = object(port, "slice");
                copyIfPresent(slice, shape, "containerMemberOrdinal");
                copyIfPresent(slice, shape, "methods");
                copyIfPresent(slice, shape, "sites");
                copyIfPresent(slice, shape, "staticSites");
            }
            return CanonicalJson.render(shape);
        }

        public static String semanticGoalKey(
                JsonObject goal, String regionId) {
            String kind = string(goal, "kind");
            String pathSeed = string(goal, "pathSeedKey");
            if ("TARGET_REACH_CLOSURE".equals(kind)) {
                return kind + "\n" + regionId + "\n" + pathSeed + "\n"
                        + admissionIdentity(goal);
            }
            List<String> members = new ArrayList<>();
            for (JsonElement element : closureMembers(goal)) {
                if (element.isJsonObject()) {
                    members.add(portShape(element.getAsJsonObject(), true));
                }
            }
            Collections.sort(members);
            List<String> inputs = new ArrayList<>();
            for (JsonElement element : array(goal, "symbolize")) {
                if (element.isJsonObject()) {
                    inputs.add(portShape(element.getAsJsonObject(), false));
                }
            }
            Collections.sort(inputs);
            return kind + "\n" + regionId + "\n" + pathSeed + "\n"
                    + members + "\n" + inputs + "\n"
                    + admissionIdentity(goal);
        }

        private static String admissionIdentity(JsonObject goal) {
            JsonObject admission = object(goal, "admission");
            List<String> blockers = stringValues(array(admission,
                    "blockers"));
            Collections.sort(blockers);
            return string(admission, "state") + "\n" + blockers;
        }

        private static List<String> stringValues(JsonArray values) {
            List<String> result = new ArrayList<>();
            for (JsonElement value : values) {
                if (value.isJsonPrimitive()
                        && value.getAsJsonPrimitive().isString()) {
                    result.add(value.getAsString());
                }
            }
            return result;
        }

        public String executionRegionInstanceId() {
            String instance = string(object(encoded,
                    "executionOccurrence"), "regionInstanceId");
            return instance.isEmpty() ? plan.regionInstanceId() : instance;
        }

        public long executionRootCallId() {
            JsonObject occurrence = object(encoded, "executionOccurrence");
            if (occurrence.has("rootCallId")) {
                return longInteger(occurrence, "rootCallId", -1L);
            }
            return plan.encoded.has("rootCallId")
                    ? longInteger(plan.encoded, "rootCallId", -1L) : -1L;
        }

        void writeTaskIdentityTo(JsonObject target) {
            plan.writeTaskIdentityTo(target);
            JsonObject occurrence = object(encoded, "executionOccurrence");
            if (occurrence.size() == 0) return;
            target.addProperty("regionInstanceId",
                    executionRegionInstanceId());
            copyIfPresent(occurrence, target, "rootSelector");
            copyIfPresent(occurrence, target, "targetMethod");
            copyIfPresent(occurrence, target, "rootCallId");
            copyIfPresent(occurrence, target, "ownerId");
            copyIfPresent(occurrence, target, "laneId");
            copyIfPresent(occurrence, target, "spanId");
            copyIfPresent(occurrence, target, "parentSpanId");
            copyIfPresent(occurrence, target, "remoteParentSpanId");
            copyIfPresent(occurrence, target, "process");
            copyIfPresent(occurrence, target, "thread");
            copyIfPresent(occurrence, target, "threadId");
        }

        void writeTaskPayloadTo(JsonObject target) {
            target.addProperty("goalId", goalId());
            if (encoded.has("pathSeedKey")) {
                target.add("pathSeedKey",
                        encoded.get("pathSeedKey").deepCopy());
            }
            if (kind().capturesOutputRelation()) {
                OutputClosureContract contract = outputClosure();
                if (contract != null) {
                    target.add(OutputClosureContract.FIELD,
                            contract.toJson());
                }
            } else {
                rejectOutputClosure();
            }
        }
    }

    private static void copyIfPresent(JsonObject source, JsonObject target,
                                      String field) {
        if (source.has(field)) {
            target.add(field, source.get(field).deepCopy());
        }
    }
}

package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.option.LongOptions;
import edu.uva.liftlab.graphchecker.smt.JsonFields;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public final class KeyGate {
    private KeyGate() {
    }

    enum Answer {
        ADMITTED,
        SAT,
        UNSAT,
        NONE;

        boolean satisfiable() {
            return this == ADMITTED || this == SAT;
        }
    }

    static final class Asked {
        final String round;
        final String obligationId;
        final String arm;
        final String pathId;
        final String sessionId;
        final Set<String> world;
        final Answer answer;
        final boolean settles;
        final String detail;

        Asked(String round, String obligationId, String arm,
              Corpus.RecordedPath path, Set<String> world, Answer answer,
              boolean settles, String detail) {
            this.round = round;
            this.obligationId = obligationId;
            this.arm = arm;
            this.pathId = path.pathId;
            this.sessionId = path.sessionId;
            this.world = world;
            this.answer = answer;
            this.settles = settles;
            this.detail = detail;
        }

        JsonObject json() {
            JsonObject row = new JsonObject();
            row.addProperty("obligationId", obligationId);
            row.addProperty("round", round);
            row.addProperty("session", sessionId);
            row.addProperty("depth", world.size());
            row.addProperty("answer", answer.name());
            row.addProperty("settles", settles);
            row.addProperty("detail", detail.length() > 300
                    ? detail.substring(0, 300) : detail);
            return row;
        }
    }

    public static void main(String[] argv) throws Exception {
        LongOptions options = LongOptions.parse(argv);
        Path iteration = options.path("iteration");
        Path claim = options.path("claim");
        Path out = options.path("out");
        Corpus corpus = Corpus.read(iteration, options.path("root-domains"));
        JsonObject report = gate(corpus, iteration, claim);
        Files.write(out, new GsonBuilder().setPrettyPrinting().create()
                .toJson(report).getBytes(StandardCharsets.UTF_8));
        System.out.println("asked=" + report.get("asked") + " arms="
                + report.get("arms") + " idsBefore="
                + report.get("idsBefore") + " keys=" + report.get("keys")
                + " armsUnderSeveralKeys=" + report.get("armsUnderSeveralKeys")
                + " mixed=" + report.get("mixed") + " nested="
                + report.get("nested") + " defects="
                + report.get("defects") + " unsafe=" + report.get("unsafe")
                + " lostOnWitnessChain="
                + report.getAsJsonArray("lostOnWitnessChain").size());
        if (report.get("defects").getAsInt() > 0
                || report.get("unsafe").getAsInt() > 0
                || report.getAsJsonArray("lostOnWitnessChain").size() > 0) {
            System.exit(1);
        }
    }

    static JsonObject gate(Corpus corpus, Path iteration, Path claim)
            throws IOException {
        Map<String, List<Asked>> byKey = new LinkedHashMap<String, List<Asked>>();
        Set<String> arms = new LinkedHashSet<String>();
        Set<String> idsBefore = new LinkedHashSet<String>();
        int asked = 0;
        Map<String, Task> tasks = new LinkedHashMap<String, Task>();
        for (Path worker : ObligationDir.workerDirs(iteration)) {
            Asked arm = rekeyed(corpus, worker, byKey, tasks);
            if (arm == null) continue;
            asked++;
            arms.add(arm.arm);
            idsBefore.add(arm.obligationId);
        }
        Set<String> chain = witnessChain(corpus, claim);
        JsonArray defects = new JsonArray();
        JsonArray unsafe = new JsonArray();
        JsonArray lost = new JsonArray();
        int mixed = 0;
        int nested = 0;
        Map<String, Integer> keysPerArm = new LinkedHashMap<String, Integer>();
        for (Map.Entry<String, List<Asked>> key : byKey.entrySet()) {
            List<Asked> asks = key.getValue();
            asks.sort(Comparator.comparingInt((Asked ask) -> ask.world.size())
                    .thenComparing(ask -> ask.round));
            Asked first = asks.get(0);
            keysPerArm.merge(first.arm, 1, Integer::sum);
            Asked settling = null;
            for (Asked ask : asks) {
                if (ask.settles) {
                    settling = ask;
                    break;
                }
            }
            List<Set<String>> satisfiable = new ArrayList<Set<String>>();
            List<Set<String>> unsat = new ArrayList<Set<String>>();
            boolean admitted = false;
            for (Asked ask : asks) {
                if (ask.answer.satisfiable()) satisfiable.add(ask.world);
                if (ask.answer == Answer.UNSAT) unsat.add(ask.world);
                admitted |= ask.answer == Answer.ADMITTED;
            }
            if (!satisfiable.isEmpty() && !unsat.isEmpty()) {
                mixed++;
                if (nestedOnly(satisfiable, unsat)) {
                    nested++;
                } else {
                    defects.add(row(key.getKey(), asks));
                }
            }
            if (admitted && settling != null
                    && settling.answer != Answer.ADMITTED) {
                unsafe.add(row(key.getKey(), asks));
            }
            for (Asked ask : asks) {
                if (ask != first && chain.contains(ask.obligationId)
                        && !ask.pathId.equals(first.pathId)) {
                    lost.add(row(key.getKey(), asks));
                }
            }
        }
        JsonObject report = new JsonObject();
        report.addProperty("asked", asked);
        report.addProperty("arms", arms.size());
        report.addProperty("idsBefore", idsBefore.size());
        report.addProperty("keys", byKey.size());
        int several = 0;
        for (int count : keysPerArm.values()) if (count > 1) several++;
        report.addProperty("armsUnderSeveralKeys", several);
        report.addProperty("mixed", mixed);
        report.addProperty("nested", nested);
        report.addProperty("defects", defects.size());
        report.addProperty("unsafe", unsafe.size());
        report.add("witnessChain", ExploreCodec.list(
                new ArrayList<String>(chain)));
        report.add("lostOnWitnessChain", lost);
        report.add("defectKeys", defects);
        report.add("unsafeKeys", unsafe);
        return report;
    }

    static boolean nestedOnly(List<Set<String>> satisfiable,
                              List<Set<String>> unsat) {
        for (Set<String> no : unsat) {
            boolean extended = false;
            for (Set<String> yes : satisfiable) {
                extended |= no.size() > yes.size() && no.containsAll(yes);
            }
            if (!extended) return false;
        }
        return true;
    }

    private static JsonObject row(String key, List<Asked> asks) {
        JsonObject row = new JsonObject();
        row.addProperty("key", key);
        row.addProperty("arm", asks.get(0).arm);
        JsonArray members = new JsonArray();
        for (Asked ask : asks) members.add(ask.json());
        row.add("asks", members);
        return row;
    }

    private static Asked rekeyed(Corpus corpus, Path worker,
                                 Map<String, List<Asked>> byKey,
                                 Map<String, Task> tasks)
            throws IOException {
        Path row = worker.resolve(ObligationDir.OBLIGATION);
        Path result = worker.resolve(ObligationDir.RESULT);
        if (!Files.isRegularFile(row) || !Files.isRegularFile(result)) {
            return null;
        }
        List<Obligation> rows = RowCodec.readAll(row,
                ExploreCodec::readObligation);
        if (rows.isEmpty()) return null;
        Obligation obligation = rows.get(0);
        if (obligation.force() || Obligation.pairing(obligation.siteId())) {
            return null;
        }
        List<ObligationResult> answers = RowCodec.readAll(result,
                RowCodec::readObligationResult);
        if (answers.isEmpty()) return null;
        ObligationResult last = answers.get(answers.size() - 1);
        boolean model = Files.isRegularFile(worker.resolve(
                ObligationDir.FOCUSED_TASK)) && Files.size(worker.resolve(
                ObligationDir.FOCUSED_TASK)) > 0;
        Answer answer = last.verdict() == Verdict.ADMITTED ? Answer.ADMITTED
                : last.verdict() == Verdict.UNSAT ? Answer.UNSAT
                : model ? Answer.SAT : Answer.NONE;
        Task task = tasks.computeIfAbsent(obligation.taskId(),
                id -> ClosurePlanner.taskOf(corpus, id));
        if (task == null) return null;
        for (Corpus.RecordedPath path : corpus.pathsOf(task.focused())) {
            if (!path.pathId.equals(obligation.pathId())) continue;
            for (int index = 0; index < path.decisions.size(); index++) {
                DecisionRow decision = path.decisions.get(index);
                if (!decision.siteId().equals(obligation.siteId())
                        || decision.ordinal() != obligation.ordinal()) {
                    continue;
                }
                String arm = task.taskId() + "|" + decision.siteId() + "#"
                        + decision.ordinal() + " -> "
                        + obligation.flippedOutcome();
                String key = ObligationFactory.obligationId(task.taskId(),
                        decision.siteId(), decision.ordinal(),
                        obligation.flippedOutcome(),
                        ObligationFactory.dependence(corpus, task, path,
                                index));
                Set<String> world = new LinkedHashSet<String>();
                for (Corpus.Flip flip : corpus.world(path.sessionId).flips) {
                    world.add(flip.focusedOccurrenceId + "|" + flip.siteId
                            + "#" + flip.ordinal + "=" + flip.outcome);
                }
                Asked ask = new Asked(worker.getParent().getFileName()
                        .toString(), obligation.obligationId(), arm, path,
                        world, answer, last.settlesArm(),
                        last.verdict() + " " + last.detail());
                byKey.computeIfAbsent(key, unused -> new ArrayList<Asked>())
                        .add(ask);
                return ask;
            }
        }
        return null;
    }

    private static Set<String> witnessChain(Corpus corpus, Path claim)
            throws IOException {
        Set<String> chain = new LinkedHashSet<String>();
        if (claim == null || !Files.isRegularFile(claim)) return chain;
        JsonObject read = ExploreCodec.readObject(claim);
        if (!read.has("valuations") || !read.has("claim")) return chain;
        String ordinal = JsonFields.optionalString(
                read.getAsJsonObject("claim"), "valuationOrdinal");
        for (JsonElement valuation : read.getAsJsonArray("valuations")) {
            JsonObject held = valuation.getAsJsonObject();
            if (!ordinal.equals(JsonFields.optionalString(held, "ordinal"))) {
                continue;
            }
            String session = JsonFields.optionalString(held,
                    "selectedSessionId");
            for (Corpus.Flip flip : corpus.world(session).flips) {
                if (!flip.obligationId.isEmpty()) chain.add(flip.obligationId);
            }
        }
        return chain;
    }
}

#!/usr/bin/env python3
"""Generate one deterministic round of fixed-RPC stress workloads."""

from pathlib import Path
import argparse
import shutil


ROOT = Path(__file__).resolve().parents[4]
JAVA_ROOT = (ROOT / "src/test/java/edu/uva/liftlab/graphchecker"
             / "fixtures/stress")
STRESS_ROOT = ROOT / "experiments/generic/three-thread-rpc/stress"
GENERATED = STRESS_ROOT / "generated"
HISTORY = STRESS_ROOT / "history"
PACKAGE = "edu.uva.liftlab.graphchecker.fixtures.stress"

FAMILIES = (
    "scalar-fields", "compound-guards", "cross-method-state",
    "nested-object", "inherited-alias", "array-decoy",
    "array-fixed-loop", "map-entry", "map-mutation", "list-index",
    "list-iterator", "linked-set", "queue", "map-of-array",
    "array-of-map", "boxed-primitives", "string-flow",
    "wide-and-narrow", "receiver-alias", "multiple-writes",
)


def producer(family, role, false_value, true_value):
    r = role
    f = false_value
    t = true_value
    if family == 0:
        return f"""
    static final class {r}Producer {{
        boolean enabled;
        int low = {f};
        int high = {t};

        {r}Producer(Boolean input) {{
            enabled = input.booleanValue();
        }}

        int compute() {{
            int result = low;
            if (enabled) {{
                result = high;
            }}
            if (result > 0 && !enabled) {{
                result = low;
            }}
            return result;
        }}
    }}
"""
    if family == 1:
        return f"""
    static final class {r}Producer {{
        boolean enabled;
        int left;
        int right = 2;

        {r}Producer(Boolean input) {{
            enabled = input.booleanValue();
            left = enabled ? 1 : 3;
        }}

        int compute() {{
            boolean ordered = (enabled && left < right)
                    || (!enabled && left > right);
            if (ordered && enabled) {{
                return {t};
            }}
            if (ordered || left == right + 1) {{
                return {f};
            }}
            return {f};
        }}
    }}
"""
    if family == 2:
        return f"""
    static final class {r}State {{
        boolean enabled;
        int result;

        {r}State(Boolean input) {{
            enabled = input.booleanValue();
            result = {f};
        }}
    }}

    static final class {r}Producer {{
        {r}State state;

        {r}Producer(Boolean input) {{
            state = new {r}State(input);
        }}

        int compute() {{
            update(state);
            return finish(state);
        }}

        private static void update({r}State state) {{
            if (state.enabled) {{
                state.result = {t};
            }} else {{
                state.result = {f};
            }}
        }}

        private static int finish({r}State state) {{
            if (state.result > 0 && state.enabled) {{
                return state.result;
            }}
            return {f};
        }}
    }}
"""
    if family == 3:
        return f"""
    static final class {r}Flag {{
        boolean enabled;
        {r}Flag(Boolean input) {{ enabled = input.booleanValue(); }}
    }}

    static final class {r}State {{
        {r}Flag flag;
        int disabledValue = {f};
        int enabledValue = {t};
        {r}State(Boolean input) {{ flag = new {r}Flag(input); }}
    }}

    static final class {r}Envelope {{
        {r}State state;
        {r}Envelope(Boolean input) {{ state = new {r}State(input); }}
    }}

    static final class {r}Producer {{
        {r}Envelope envelope;
        {r}Producer(Boolean input) {{
            envelope = new {r}Envelope(input);
        }}
        int compute() {{
            return resolve(envelope);
        }}
        private static int resolve({r}Envelope input) {{
            {r}State state = input.state;
            if (state.flag.enabled) {{
                return state.enabledValue;
            }}
            return state.disabledValue;
        }}
    }}
"""
    if family == 4:
        return f"""
    static class {r}Base {{
        int value = {f};
    }}

    static final class {r}Derived extends {r}Base {{
        boolean enabled;
        int value;
        {r}Derived(Boolean input) {{
            enabled = input.booleanValue();
            super.value = enabled ? {t} : {f};
            value = enabled ? {f} : {t};
        }}
    }}

    static final class {r}Producer {{
        {r}Base base;
        {r}Derived derived;
        {r}Producer(Boolean input) {{
            derived = new {r}Derived(input);
            base = derived;
        }}
        int compute() {{
            return resolve(base, derived);
        }}
        private static int resolve({r}Base inheritedView,
                                   {r}Derived concreteView) {{
            int inheritedValue = inheritedView.value;
            int hiddenValue = concreteView.value;
            if (concreteView.enabled
                    && inheritedView == concreteView
                    && hiddenValue == {f}) {{
                return inheritedValue;
            }}
            return {f};
        }}
    }}
"""
    if family == 5:
        return f"""
    static final class {r}ArrayNode {{
        boolean enabled;
        int value;
        {r}ArrayNode(boolean enabled, int value) {{
            this.enabled = enabled;
            this.value = value;
        }}
    }}

    static final class {r}ArrayPayload {{
        {r}ArrayNode[] nodes;
        {r}ArrayPayload({r}ArrayNode[] nodes) {{
            this.nodes = nodes;
        }}
    }}

    static final class {r}Producer {{
        {r}ArrayPayload payload;
        {r}Producer(Boolean input) {{
            boolean enabled = input.booleanValue();
            payload = new {r}ArrayPayload(new {r}ArrayNode[]{{
                    new {r}ArrayNode(!enabled, enabled ? {f} : {t}),
                    new {r}ArrayNode(enabled, enabled ? {t} : {f})
            }});
        }}
        int compute() {{
            return select(payload.nodes[1]);
        }}
        private static int select({r}ArrayNode selected) {{
            if (selected.enabled) {{
                return selected.value;
            }}
            return {f};
        }}
    }}
"""
    if family == 6:
        return f"""
    static final class {r}Producer {{
        boolean enabled;
        int[] values;
        {r}Producer(Boolean input) {{
            enabled = input.booleanValue();
            values = enabled
                    ? new int[]{{1, 2, 3, 4}}
                    : new int[]{{-1, -2, -3, -4}};
        }}
        int compute() {{
            int sum = 0;
            for (int index = 0; index < 4; index++) {{
                sum += values[index];
            }}
            if (enabled && sum == 10) {{
                return {t};
            }}
            return {f};
        }}
    }}
"""
    if family == 7:
        return f"""
    static final class {r}MapNode {{
        boolean enabled;
        int value;
        {r}MapNode(boolean enabled, int value) {{
            this.enabled = enabled;
            this.value = value;
        }}
    }}

    static final class {r}Producer {{
        Map<Integer, {r}MapNode> values = new LinkedHashMap<>();
        {r}Producer(Boolean input) {{
            boolean enabled = input.booleanValue();
            values.put(Integer.valueOf(7),
                    new {r}MapNode(enabled, enabled ? {t} : {f}));
            values.put(Integer.valueOf(9),
                    new {r}MapNode(!enabled, enabled ? {f} : {t}));
        }}
        int compute() {{
            Iterator<Map.Entry<Integer, {r}MapNode>> iterator =
                    values.entrySet().iterator();
            Map.Entry<Integer, {r}MapNode> entry = iterator.next();
            Integer key = entry.getKey();
            {r}MapNode node = entry.getValue();
            if (key.intValue() == 7 && node.enabled) {{
                return node.value;
            }}
            return {f};
        }}
    }}
"""
    if family == 8:
        return f"""
    static final class {r}MutableNode {{
        boolean enabled;
        int value;
        {r}MutableNode(boolean enabled, int value) {{
            this.enabled = enabled;
            this.value = value;
        }}
    }}

    static final class {r}Producer {{
        boolean enabled;
        Map<Integer, {r}MutableNode> values = new LinkedHashMap<>();
        {r}Producer(Boolean input) {{
            enabled = input.booleanValue();
            values.put(Integer.valueOf(3),
                    new {r}MutableNode(false, {f}));
            values.put(Integer.valueOf(7),
                    new {r}MutableNode(false, {f}));
        }}
        int compute() {{
            if (enabled) {{
                values.put(Integer.valueOf(7),
                        new {r}MutableNode(true, {t}));
            }} else {{
                values.remove(Integer.valueOf(3));
            }}
            {r}MutableNode selected = values.get(Integer.valueOf(7));
            return selected.enabled ? selected.value : {f};
        }}
    }}
"""
    if family == 9:
        return f"""
    static final class {r}ListNode {{
        boolean enabled;
        int value;
        {r}ListNode(boolean enabled, int value) {{
            this.enabled = enabled;
            this.value = value;
        }}
    }}

    static final class {r}Producer {{
        List<{r}ListNode> nodes = new ArrayList<>();
        {r}Producer(Boolean input) {{
            boolean enabled = input.booleanValue();
            nodes.add(new {r}ListNode(!enabled, {f}));
            nodes.add(new {r}ListNode(enabled, enabled ? {t} : {f}));
        }}
        int compute() {{
            {r}ListNode selected = nodes.get(1);
            if (selected.enabled && nodes.size() == 2) {{
                return selected.value;
            }}
            return {f};
        }}
    }}
"""
    if family == 10:
        return f"""
    static final class {r}IterNode {{
        boolean enabled;
        int value;
        {r}IterNode(boolean enabled, int value) {{
            this.enabled = enabled;
            this.value = value;
        }}
    }}

    static final class {r}Producer {{
        List<{r}IterNode> nodes = new ArrayList<>();
        {r}Producer(Boolean input) {{
            boolean enabled = input.booleanValue();
            nodes.add(new {r}IterNode(!enabled, {f}));
            nodes.add(new {r}IterNode(enabled, enabled ? {t} : {f}));
        }}
        int compute() {{
            Iterator<{r}IterNode> iterator = nodes.iterator();
            {r}IterNode decoy = iterator.next();
            {r}IterNode selected = iterator.next();
            if (selected.enabled && decoy != selected) {{
                return selected.value;
            }}
            return {f};
        }}
    }}
"""
    if family == 11:
        return f"""
    static final class {r}Producer {{
        Set<Integer> values = new LinkedHashSet<>();
        {r}Producer(Boolean input) {{
            boolean enabled = input.booleanValue();
            values.add(Integer.valueOf(enabled ? {t} : {f}));
            values.add(Integer.valueOf(enabled ? {f} : {t}));
        }}
        int compute() {{
            Iterator<Integer> iterator = values.iterator();
            Integer selected = iterator.next();
            if (values.size() == 2 && selected.intValue() > 0) {{
                return selected.intValue();
            }}
            return {f};
        }}
    }}
"""
    if family == 12:
        return f"""
    static final class {r}Producer {{
        Queue<Integer> values = new ArrayDeque<>();
        boolean enabled;
        {r}Producer(Boolean input) {{
            enabled = input.booleanValue();
            values.offer(Integer.valueOf(enabled ? {t} : {f}));
            values.offer(Integer.valueOf(enabled ? {f} : {t}));
        }}
        int compute() {{
            Integer first = values.peek();
            if (enabled) {{
                Integer removed = values.poll();
                return removed.intValue();
            }}
            return first.intValue();
        }}
    }}
"""
    if family == 13:
        return f"""
    static final class {r}NestedNode {{
        boolean enabled;
        int value;
        {r}NestedNode(boolean enabled, int value) {{
            this.enabled = enabled;
            this.value = value;
        }}
    }}

    static final class {r}NestedPayload {{
        Map<Integer, {r}NestedNode[]> values = new LinkedHashMap<>();
        {r}NestedPayload(Boolean input) {{
            boolean enabled = input.booleanValue();
            values.put(Integer.valueOf(7), new {r}NestedNode[]{{
                    new {r}NestedNode(!enabled, {f}),
                    new {r}NestedNode(enabled, enabled ? {t} : {f})
            }});
        }}
    }}

    static final class {r}Producer {{
        {r}NestedPayload payload;
        {r}Producer(Boolean input) {{
            payload = new {r}NestedPayload(input);
        }}
        int compute() {{
            return resolve(payload);
        }}
        private static int resolve({r}NestedPayload input) {{
            {r}NestedNode[] row =
                    input.values.get(Integer.valueOf(7));
            {r}NestedNode selected = row[1];
            return selected.enabled ? selected.value : {f};
        }}
    }}
"""
    if family == 14:
        return f"""
    static final class {r}MapHolder {{
        Map<Integer, Integer> values = new LinkedHashMap<>();
        {r}MapHolder(boolean enabled) {{
            values.put(Integer.valueOf(7),
                    Integer.valueOf(enabled ? {t} : {f}));
        }}
    }}

    static final class {r}Producer {{
        boolean enabled;
        {r}MapHolder[] holders;
        {r}Producer(Boolean input) {{
            enabled = input.booleanValue();
            holders = new {r}MapHolder[]{{
                    new {r}MapHolder(!enabled),
                    new {r}MapHolder(enabled)
            }};
        }}
        int compute() {{
            return resolve(holders[1], enabled);
        }}
        private static int resolve({r}MapHolder input, boolean enabled) {{
            Integer selected =
                    input.values.get(Integer.valueOf(7));
            if (enabled && selected.intValue() == {t}) {{
                return selected.intValue();
            }}
            return {f};
        }}
    }}
"""
    if family == 15:
        return f"""
    static final class {r}Box {{
        Boolean enabled;
        Integer disabledValue = Integer.valueOf({f});
        Integer enabledValue = Integer.valueOf({t});
        {r}Box(Boolean input) {{ enabled = input; }}
    }}

    static final class {r}Producer {{
        {r}Box box;
        {r}Producer(Boolean input) {{ box = new {r}Box(input); }}
        int compute() {{
            Integer selected = box.enabled.booleanValue()
                    ? box.enabledValue : box.disabledValue;
            return selected.intValue();
        }}
    }}
"""
    if family == 16:
        return f"""
    static final class {r}Producer {{
        String token;
        int value;
        {r}Producer(Boolean input) {{
            boolean enabled = input.booleanValue();
            token = enabled ? "enabled" : "disabled";
            value = enabled ? {t} : {f};
        }}
        int compute() {{
            if (token.startsWith("e") && token.length() == 7) {{
                return value;
            }}
            return {f};
        }}
    }}
"""
    if family == 17:
        return f"""
    static final class {r}Producer {{
        boolean enabled;
        long wide;
        short narrow;
        byte tiny;
        char marker;
        {r}Producer(Boolean input) {{
            enabled = input.booleanValue();
            wide = enabled ? 9L : -9L;
            narrow = (short) (enabled ? 4 : -4);
            tiny = (byte) (enabled ? 2 : -2);
            marker = enabled ? 'T' : 'F';
        }}
        int compute() {{
            long total = wide + narrow + tiny;
            if (enabled && total > 0L && marker == 'T') {{
                return {t};
            }}
            return {f};
        }}
    }}
"""
    if family == 18:
        return f"""
    static final class {r}AliasNode {{
        boolean enabled;
        int value;
        {r}AliasNode(boolean enabled, int value) {{
            this.enabled = enabled;
            this.value = value;
        }}
    }}

    static final class {r}Producer {{
        {r}AliasNode primary;
        {r}AliasNode alias;
        {r}AliasNode decoy;
        {r}Producer(Boolean input) {{
            boolean enabled = input.booleanValue();
            primary = new {r}AliasNode(enabled, enabled ? {t} : {f});
            alias = primary;
            decoy = new {r}AliasNode(!enabled, enabled ? {f} : {t});
        }}
        int compute() {{
            {r}AliasNode selected = alias;
            if (selected == primary && selected != decoy
                    && selected.enabled) {{
                return selected.value;
            }}
            return {f};
        }}
    }}
"""
    return f"""
    static final class {r}Producer {{
        boolean enabled;
        int result;
        {r}Producer(Boolean input) {{
            enabled = input.booleanValue();
            result = {f};
        }}
        int compute() {{
            result = {f};
            if (enabled) {{
                result = {t};
            }} else {{
                result = {f};
            }}
            if (result > 0 && !enabled) {{
                result = {f};
            }}
            return result;
        }}
    }}
"""


def consumer(round_number, case_number, expected, af, at, bf, bt):
    variant = (round_number * 3 + case_number) % 5
    if expected == "SAT":
        bodies = (
            f"if (a == {at} && b == {bt}) {{",
            f"""boolean leftReady = a > {af} && a <= {at};
            boolean rightReady = b > {bf} && b <= {bt};
            if (leftReady && rightReady && a + b == {at + bt}) {{""",
            f"""int left = a < 0 ? -a : a;
            int right = b < 0 ? -b : b;
            if ((left == {at} && right == {bt})
                    || (left == {at + 100} && b != {bf})) {{""",
            f"""boolean exact = a == {at} && b == {bt};
            if (exact || (a == {at + 101} && b == {bf})) {{""",
            f"""int score = a + b;
            for (int index = 0; index < 4; index++) {{
                score++;
            }}
            if (a > 0 && b > 0 && score == {at + bt + 4}) {{""",
        )
    else:
        bodies = (
            f"if (a == {at} && b == {bt} && a + b == {at + bt + 1}) {{",
            """if (a > b && a <= b) {""",
            f"""boolean leftTrue = a == {at};
            boolean rightTrue = b == {bt};
            if ((leftTrue || rightTrue) && !leftTrue && !rightTrue) {{""",
            f"""int left = a < 0 ? -a : a;
            int right = b < 0 ? -b : b;
            if (left == {at} && right == {bt}
                    && left - right == {at - bt + 1}) {{""",
            f"""int score = a + b;
            for (int index = 0; index < 4; index++) {{
                score++;
            }}
            if (score == {at + bt + 4}
                    && score != {at + bt + 4}) {{""",
        )
    return bodies[variant], f"consumer-{expected.lower()}-{variant}"


def java_source(round_number, case_number):
    class_name = f"StressRoundFixture{case_number:02d}"
    target = f"stress-r{round_number:02d}-c{case_number:02d}"
    expected = "SAT" if case_number % 2 else "UNSAT"
    af = -(case_number + round_number + 1)
    at = case_number + round_number + 5
    bf = -(2 * case_number + round_number + 3)
    bt = 2 * case_number + round_number + 7
    family_a = (case_number - 1 + 2 * (round_number - 1)) % len(FAMILIES)
    family_b = (case_number + 7 + 3 * (round_number - 1)) % len(FAMILIES)
    guard, guard_name = consumer(
        round_number, case_number, expected, af, at, bf, bt)
    source = f"""package {PACKAGE};

import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.CountDownLatch;

/** Generated stress round {round_number}, case {case_number}: {expected}. */
public final class {class_name} {{
    private {class_name}() {{
    }}

{producer(family_a, "A", af, at)}
{producer(family_b, "B", bf, bt)}
    public static final class TargetReachedException
            extends RuntimeException {{
        TargetReachedException(int a, int b) {{
            super("stress target reached with a=" + a + ", b=" + b);
        }}
    }}

    static final class ProducerAThread
            extends StressRpcFixtureSupport.Worker {{
        private final AProducer producer;
        private final StressRpcFixtureSupport.Bus bus;
        private final StressRpcFixtureSupport.ProducerGate gate;

        ProducerAThread(CountDownLatch start, AProducer producer,
                        StressRpcFixtureSupport.Bus bus,
                        StressRpcFixtureSupport.ProducerGate gate) {{
            super("stress-a", start);
            this.producer = producer;
            this.bus = bus;
            this.gate = gate;
        }}

        @Override
        void executeWorker() throws InterruptedException {{
            gate.enterAndAwaitPeer();
            bus.publishA(producer.compute());
        }}
    }}

    static final class ProducerBThread
            extends StressRpcFixtureSupport.Worker {{
        private final BProducer producer;
        private final StressRpcFixtureSupport.Bus bus;
        private final StressRpcFixtureSupport.ProducerGate gate;

        ProducerBThread(CountDownLatch start, BProducer producer,
                        StressRpcFixtureSupport.Bus bus,
                        StressRpcFixtureSupport.ProducerGate gate) {{
            super("stress-b", start);
            this.producer = producer;
            this.bus = bus;
            this.gate = gate;
        }}

        @Override
        void executeWorker() throws InterruptedException {{
            gate.enterAndAwaitPeer();
            bus.publishB(producer.compute());
        }}
    }}

    static final class ConsumerThread
            extends StressRpcFixtureSupport.Worker {{
        private final StressRpcFixtureSupport.Bus bus;

        ConsumerThread(CountDownLatch start,
                       StressRpcFixtureSupport.Bus bus) {{
            super("stress-consumer", start);
            this.bus = bus;
        }}

        @Override
        void executeWorker() throws InterruptedException {{
            int a = bus.getRPCFromA();
            int b = bus.getRPCFromB();
            {guard}
                throw new @CausynthExceptionTarget("{target}")
                        TargetReachedException(a, b);
            }}
        }}
    }}

    public static void main(String[] args) throws Exception {{
        if (args.length != 2) {{
            throw new IllegalArgumentException(
                    "expected: <producerAInput> <producerBInput>");
        }}
        Boolean inputA = StressRpcFixtureSupport.parseBoolean(args[0]);
        Boolean inputB = StressRpcFixtureSupport.parseBoolean(args[1]);
        CountDownLatch start = new CountDownLatch(1);
        StressRpcFixtureSupport.ProducerGate gate =
                new StressRpcFixtureSupport.ProducerGate();
        StressRpcFixtureSupport.Bus bus =
                new StressRpcFixtureSupport.Bus();
        ProducerAThread producerA = new ProducerAThread(start,
                new AProducer(inputA), bus, gate);
        ProducerBThread producerB = new ProducerBThread(start,
                new BProducer(inputB), bus, gate);
        ConsumerThread consumer = new ConsumerThread(start, bus);
        Throwable failure = StressRpcFixtureSupport.run(
                start, producerA, producerB, consumer, bus);
        System.out.println("{{\\"kind\\":\\"STRESS_RESULT\\","
                + "\\"round\\":{round_number},\\"case\\":{case_number}}}");
        StressRpcFixtureSupport.propagate(failure);
    }}
}}
"""
    return {
        "class": class_name,
        "target": target,
        "expected": expected,
        "family_a": FAMILIES[family_a],
        "family_b": FAMILIES[family_b],
        "consumer": guard_name,
        "source": source,
    }


def workflow(round_number, case_number, row):
    profile = f"stress-r{round_number:02d}-c{case_number:02d}"
    fixture = f"{PACKAGE}.{row['class']}"
    target = f"target/{profile}"
    return f"""workflow_path_base=project

fixture_class={fixture}
fixture_support_class={PACKAGE}.StressRpcFixtureSupport
trace_test={row['class']}
custom_jdk_docker_image=causynth-openjdk8-build:ubuntu18

graphchecker_jar=target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar
graphchecker_pom=pom.xml
graphchecker_work_dir=.
java_bin=java
maven_bin=mvn
build_maven_args=package -DskipTests

project_repo=.
project_module_dir=.
project_classes_dir={target}/original-classes
project_test_classes_dir=target/test-classes
project_classpath={target}/original-classes:target/classes
analysis_classes_dir={target}/instrumented-classes
causynth_output_dir={target}/analysis
causynth_target_spec=experiments/generic/three-thread-rpc/stress/generated/case-{case_number:02d}/target.yaml
causynth_analysis_scope=stress_r{round_number:02d}_c{case_number:02d}
causynth_process_dirs={target}/original-classes

custom_jdk_home=third_party/OpenJDK-Concolic-Execution-Engine/build/linux-x86_64-normal-zero-release/images/j2sdk-image
z3_bin=z3
solver_timeout_ms=20000
producer_max_paths_per_region=128
workload_work_dir=.
workload_command=java -Dcausynth.trace.output.dir={target}/runtime -Dcausynth.static.graph={target}/analysis/candidate_dataflow_edges.jsonl.gz -Dcausynth.symbolic.regions={target}/analysis/symbolic_regions.jsonl -Dcausynth.symbolic.region.edges={target}/analysis/symbolic_region_edges.jsonl -Dcausynth.trace.test={row['class']} -cp {target}/instrumented-classes:target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar {fixture} false false

refined_regions={target}/analysis/symbolic_regions.jsonl
candidate_graph={target}/analysis/candidate_dataflow_edges.jsonl.gz
runtime_region_plan={target}/runtime/concolic_region_plan.jsonl
schedule_output_dir={target}/schedule
raw_concolic_results={target}/schedule/concolic_region_results.jsonl
import_task_plan={target}/schedule/execution_task_plan.jsonl
imported_summaries={target}/schedule/concolic_region_summaries.jsonl
merged_summaries={target}/schedule/merged_region_summaries.jsonl
fatal_queries={target}/schedule/branch_queries.jsonl
compose_summary_inputs={target}/schedule/merged_region_summaries.jsonl
composed_smt={target}/schedule/composed_fatal.smt2
"""


def generate(round_number):
    JAVA_ROOT.mkdir(parents=True, exist_ok=True)
    HISTORY.mkdir(parents=True, exist_ok=True)
    if GENERATED.exists():
        shutil.rmtree(GENERATED)
    GENERATED.mkdir(parents=True)
    for old in JAVA_ROOT.glob("StressRoundFixture*.java"):
        old.unlink()

    rows = []
    for case_number in range(1, 21):
        row = java_source(round_number, case_number)
        (JAVA_ROOT / f"{row['class']}.java").write_text(
            row["source"], encoding="utf-8")
        profile_dir = GENERATED / f"case-{case_number:02d}"
        profile_dir.mkdir()
        (profile_dir / "workflow.properties").write_text(
            workflow(round_number, case_number, row), encoding="utf-8")
        (profile_dir / "target.yaml").write_text(
            f"exception_target_id: {row['target']}\n", encoding="utf-8")
        rows.append("\t".join((
            f"{case_number:02d}", row["class"], row["target"],
            row["expected"], row["family_a"], row["family_b"],
            row["consumer"])))

    manifest = (
        f"# round={round_number}\n"
        "case\tclass\ttarget\texpected\tproducerA\tproducerB\tconsumer\n"
        + "\n".join(rows) + "\n")
    (STRESS_ROOT / "manifest.tsv").write_text(manifest, encoding="utf-8")
    (HISTORY / f"round-{round_number:02d}-manifest.tsv").write_text(
        manifest, encoding="utf-8")
    (STRESS_ROOT / "CURRENT_ROUND").write_text(
        f"{round_number}\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("round", type=int, choices=range(1, 11))
    args = parser.parse_args()
    generate(args.round)


if __name__ == "__main__":
    main()

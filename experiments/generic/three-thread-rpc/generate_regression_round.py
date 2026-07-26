#!/usr/bin/env python3
"""Generate one disposable 13-workload semantic regression round."""

from pathlib import Path
import json
import sys


PACKAGE = "edu.uva.liftlab.graphchecker.generated"
EXPECTED = ("REACHABLE",) * 6 + ("UNREACHABLE",) * 7

JAVA_TEMPLATE = """\
package @PACKAGE@;

import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

public final class @CLASS@ {
    private static final int SHIFT = @SHIFT@;
    private static final long JOIN_MILLIS = 10000L;

    private @CLASS@() {
    }

    private static final class Box {
        private int value;
    }

    private static final class Inner {
        private int value;
    }

    private static final class Nested {
        private final Inner inner = new Inner();
    }

    private static final class Mixed {
        private final int[] values = new int[2];
        private final Map<String, Integer> extras =
                new HashMap<String, Integer>();
        private final Nested nested = new Nested();
    }

    public static final class LeftProducer {
        public int compute(Boolean flag) {
@LEFT_BODY@
        }
    }

    public static final class RightProducer {
        public int compute(Boolean flag) {
@RIGHT_BODY@
        }
    }

    public static final class RpcBus {
        private final CountDownLatch leftReady = new CountDownLatch(1);
        private final CountDownLatch rightReady = new CountDownLatch(1);
        private volatile int left;
        private volatile int right;

        public void publishLeft(int value) {
            left = value;
            leftReady.countDown();
        }

        public void publishRight(int value) {
            right = value;
            rightReady.countDown();
        }

        public int getRPCFromLeft() throws InterruptedException {
            if (!leftReady.await(JOIN_MILLIS, TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException("left RPC timed out");
            }
            int received = left;
            return received;
        }

        public int getRPCFromRight() throws InterruptedException {
            if (!rightReady.await(JOIN_MILLIS, TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException("right RPC timed out");
            }
            int received = right;
            return received;
        }
    }

    public static final class GeneratedBugReachedException
            extends RuntimeException {
        GeneratedBugReachedException(int left, int right) {
            super("generated target reached with left=" + left
                    + ", right=" + right);
        }
    }

    private abstract static class WorkerThread extends Thread {
        WorkerThread(String name) {
            super(name);
        }

        @Override
        public final void run() {
            try {
                executeWorker();
            } catch (InterruptedException exception) {
                Thread.currentThread().interrupt();
                throw new IllegalStateException(
                        "generated worker interrupted", exception);
            }
        }

        abstract void executeWorker() throws InterruptedException;
    }

    private static final class LeftThread extends WorkerThread {
        private final Boolean flag;
        private final RpcBus bus;

        LeftThread(Boolean flag, RpcBus bus) {
            super("generated-left-producer");
            this.flag = flag;
            this.bus = bus;
        }

        @Override
        void executeWorker() {
            bus.publishLeft(new LeftProducer().compute(flag));
        }
    }

    private static final class RightThread extends WorkerThread {
        private final Boolean flag;
        private final RpcBus bus;

        RightThread(Boolean flag, RpcBus bus) {
            super("generated-right-producer");
            this.flag = flag;
            this.bus = bus;
        }

        @Override
        void executeWorker() {
            bus.publishRight(new RightProducer().compute(flag));
        }
    }

    private static final class ConsumerThread extends WorkerThread {
        private final RpcBus bus;

        ConsumerThread(RpcBus bus) {
            super("generated-consumer");
            this.bus = bus;
        }

        @Override
        void executeWorker() throws InterruptedException {
            int left = bus.getRPCFromLeft();
            int right = bus.getRPCFromRight();
            int delta = left - right;
            if ((left > SHIFT - 1000 && right < SHIFT + 1000)
                    || (delta == 0 && left < 0)) {
                if (@TARGET@) {
                    throw new @CausynthExceptionTarget("@TARGET_ID@")
                            GeneratedBugReachedException(left, right);
                }
            }
        }
    }

    public static void main(String[] arguments) throws Exception {
        if (arguments.length != 2) {
            throw new IllegalArgumentException("expected two booleans");
        }
        Boolean leftFlag = parseBoolean(arguments[0]);
        Boolean rightFlag = parseBoolean(arguments[1]);
        RpcBus bus = new RpcBus();
        AtomicReference<Throwable> failure =
                new AtomicReference<Throwable>();
        Thread.UncaughtExceptionHandler handler =
                new Thread.UncaughtExceptionHandler() {
                    @Override
                    public void uncaughtException(
                            Thread thread, Throwable throwable) {
                        failure.compareAndSet(null, throwable);
                    }
                };
        Thread left = new LeftThread(leftFlag, bus);
        Thread right = new RightThread(rightFlag, bus);
        Thread consumer = new ConsumerThread(bus);
        left.setUncaughtExceptionHandler(handler);
        right.setUncaughtExceptionHandler(handler);
        consumer.setUncaughtExceptionHandler(handler);

        left.start();
        join(left);
        right.start();
        join(right);
        consumer.start();
        join(consumer);

        System.out.println("{\\"kind\\":\\"GENERATED_RPC_RESULT\\","
                + "\\"failed\\":" + (failure.get() != null) + "}");
        Throwable observed = failure.get();
        if (observed instanceof RuntimeException) {
            throw (RuntimeException) observed;
        }
        if (observed instanceof Error) {
            throw (Error) observed;
        }
        if (observed != null) {
            throw new IllegalStateException("worker failed", observed);
        }
    }

    private static void join(Thread thread) throws InterruptedException {
        thread.join(JOIN_MILLIS);
        if (thread.isAlive()) {
            thread.interrupt();
            throw new IllegalStateException(
                    "worker did not terminate: " + thread.getName());
        }
    }

    private static Boolean parseBoolean(String value) {
        if ("true".equalsIgnoreCase(value)) {
            return Boolean.TRUE;
        }
        if ("false".equalsIgnoreCase(value)) {
            return Boolean.FALSE;
        }
        throw new IllegalArgumentException("not a boolean: " + value);
    }
}
"""


def indented(body):
    return "\n".join("            " + line for line in body.strip().splitlines())


def programs():
    return [
        (
            """
Box box = new Box();
box.value = 2 + SHIFT;
if ((flag.booleanValue() && SHIFT >= 0)
        || (flag.booleanValue() && SHIFT < 0)) {
    box.value = 20 + SHIFT;
} else {
    box.value = 2 + SHIFT;
}
return box.value;
""",
            """
Box box = new Box();
if ((flag.booleanValue() && (SHIFT & 1) == 0)
        || (flag.booleanValue() && (SHIFT & 1) != 0)) {
    box.value = 4 + SHIFT;
} else {
    box.value = 10 + SHIFT;
}
return box.value;
""",
            "(left > right && delta >= 6)"
            " || (left == right && left < 0)",
        ),
        (
            """
int value = flag.booleanValue() ? 3 + SHIFT : 1 + SHIFT;
for (int index = 0; index < 4; index++) {
    if ((flag.booleanValue()
            && (((index & 1) == 0) || index == 3))
            || (!flag.booleanValue() && index < 0)) {
        value = value + index + 1;
    }
}
return value;
""",
            """
Nested nested = new Nested();
nested.inner.value = flag.booleanValue()
        ? 15 + SHIFT : 7 + SHIFT;
return nested.inner.value;
""",
            "(left > right && delta == 4)"
            " || (left < 0 && right < 0)",
        ),
        (
            """
Nested state = new Nested();
state.inner.value = 2 + SHIFT;
if ((flag.booleanValue() && state.inner.value >= SHIFT)
        || (flag.booleanValue() && state.inner.value < SHIFT)) {
    state.inner.value = 14 + SHIFT;
}
return state.inner.value;
""",
            """
Nested state = new Nested();
state.inner.value = flag.booleanValue()
        ? 3 + SHIFT : 9 + SHIFT;
return state.inner.value;
""",
            "(left > right && left + right > 20 + 2 * SHIFT)"
            " || (delta == 0 && left < 0)",
        ),
        (
            """
int[] values = new int[]{2 + SHIFT, 15 + SHIFT};
int index = flag.booleanValue() ? 1 : 0;
return values[index];
""",
            """
int[] values = new int[]{8 + SHIFT, 1 + SHIFT};
int index = flag.booleanValue() ? 1 : 0;
return values[index];
""",
            "(left > right && delta >= 7)"
            " || (left + right < 0 && delta == 0)",
        ),
        (
            """
Map<String, Integer> values = new HashMap<String, Integer>();
values.put("low", Integer.valueOf(2 + SHIFT));
values.put("high", Integer.valueOf(20 + SHIFT));
return values.get(flag.booleanValue() ? "high" : "low").intValue();
""",
            """
Map<String, Integer> values = new HashMap<String, Integer>();
values.put("low", Integer.valueOf(11 + SHIFT));
values.put("high", Integer.valueOf(4 + SHIFT));
return values.get(flag.booleanValue() ? "high" : "low").intValue();
""",
            "(left > right && delta >= 9)"
            " || (left < 0 && right < 0)",
        ),
        (
            """
Mixed mixed = new Mixed();
mixed.values[0] = 1 + SHIFT;
mixed.values[1] = 13 + SHIFT;
mixed.extras.put("false", Integer.valueOf(0));
mixed.extras.put("true", Integer.valueOf(2));
int index = flag.booleanValue() ? 1 : 0;
String key = flag.booleanValue() ? "true" : "false";
mixed.nested.inner.value = mixed.values[index]
        + mixed.extras.get(key).intValue();
return mixed.nested.inner.value;
""",
            """
Mixed mixed = new Mixed();
mixed.values[0] = 9 + SHIFT;
mixed.values[1] = 4 + SHIFT;
mixed.nested.inner.value =
        mixed.values[flag.booleanValue() ? 1 : 0];
return mixed.nested.inner.value;
""",
            "(left > right && delta >= 6)"
            " || (left == right && left < 0)",
        ),
        (
            """
Box box = new Box();
box.value = flag.booleanValue() ? 8 + SHIFT : 4 + SHIFT;
return box.value;
""",
            """
Box box = new Box();
box.value = flag.booleanValue() ? 14 + SHIFT : 10 + SHIFT;
return box.value;
""",
            "(left > right && delta >= 1)"
            " || (left == right && left < 0)",
        ),
        (
            """
int[] values = new int[]{2 + SHIFT, 6 + SHIFT};
return values[flag.booleanValue() ? 1 : 0];
""",
            """
int[] values = new int[]{4 + SHIFT, 8 + SHIFT};
return values[flag.booleanValue() ? 1 : 0];
""",
            "(left + right == 2 * SHIFT + 7)"
            " && (left != right || left == right)",
        ),
        (
            """
int value = flag.booleanValue() ? 18 + SHIFT : 3 + SHIFT;
for (int index = 0; index < 4; index++) {
    if (index == 2 && flag.booleanValue()) {
        value = value + 1;
    }
}
return value;
""",
            """
Nested nested = new Nested();
nested.inner.value = flag.booleanValue()
        ? 5 + SHIFT : 12 + SHIFT;
return nested.inner.value;
""",
            "(left > right && left + 3 <= right)"
            " || (left < right && left - 3 >= right)",
        ),
        (
            """
Nested outer = new Nested();
outer.inner.value = flag.booleanValue()
        ? 9 + SHIFT : 5 + SHIFT;
return outer.inner.value;
""",
            """
Nested outer = new Nested();
outer.inner.value = flag.booleanValue()
        ? 3 + SHIFT : 1 + SHIFT;
return outer.inner.value;
""",
            "(left < right && delta < 0)"
            " || (left == right && left < 0)",
        ),
        (
            """
int[] values = new int[]{2 + SHIFT, 4 + SHIFT};
return values[flag.booleanValue() ? 1 : 0];
""",
            """
int[] values = new int[]{8 + SHIFT, 10 + SHIFT};
return values[flag.booleanValue() ? 1 : 0];
""",
            "(left >= right && delta > -100)"
            " || (left == right && left < 0)",
        ),
        (
            """
Map<String, Integer> values = new HashMap<String, Integer>();
values.put("a", Integer.valueOf(10 + SHIFT));
values.put("b", Integer.valueOf(12 + SHIFT));
return values.get(flag.booleanValue() ? "b" : "a").intValue();
""",
            """
Map<String, Integer> values = new HashMap<String, Integer>();
values.put("a", Integer.valueOf(0 + SHIFT));
values.put("b", Integer.valueOf(2 + SHIFT));
return values.get(flag.booleanValue() ? "b" : "a").intValue();
""",
            "(left < right && delta < 0)"
            " || (left == right && left < 0)",
        ),
        (
            """
Mixed mixed = new Mixed();
mixed.values[0] = 5 + SHIFT;
mixed.values[1] = 7 + SHIFT;
mixed.nested.inner.value =
        mixed.values[flag.booleanValue() ? 1 : 0];
return mixed.nested.inner.value;
""",
            """
Mixed mixed = new Mixed();
mixed.values[0] = 4 + SHIFT;
mixed.values[1] = 8 + SHIFT;
mixed.nested.inner.value =
        mixed.values[flag.booleanValue() ? 1 : 0];
return mixed.nested.inner.value;
""",
            "(left == right) || (left < 0 && right > 0)",
        ),
    ]


def workflow(root, class_name, target_id, case_index):
    case_root = root / ("case-%02d" % case_index)
    work = case_root / "work"
    fqcn = PACKAGE + "." + class_name
    scope = target_id.replace("-", "_")
    lines = {
        "workflow_path_base": "project",
        "fixture_class": fqcn,
        "trace_test": class_name,
        "custom_jdk_docker_image": "causynth-openjdk8-build:ubuntu18",
        "graphchecker_jar":
            "target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar",
        "graphchecker_pom": "pom.xml",
        "graphchecker_work_dir": ".",
        "java_bin": "java",
        "maven_bin": "mvn",
        "build_maven_args": "package -DskipTests",
        "project_repo": ".",
        "project_module_dir": ".",
        "project_classes_dir": str(work / "original-classes"),
        "project_test_classes_dir": str(root / "classes"),
        "project_classpath":
            str(work / "original-classes") + ":target/classes",
        "analysis_classes_dir": str(work / "instrumented-classes"),
        "causynth_output_dir": str(work / "analysis"),
        "causynth_target_spec": str(case_root / "target.yaml"),
        "causynth_analysis_scope": scope,
        "causynth_process_dirs": str(work / "original-classes"),
        "custom_jdk_home":
            "third_party/OpenJDK-Concolic-Execution-Engine/build/"
            "linux-x86_64-normal-zero-release/images/j2sdk-image",
        "z3_bin": "z3",
        "solver_timeout_ms": "20000",
        "workload_work_dir": ".",
        "workload_command":
            "java -Dcausynth.trace.output.dir=" + str(work / "runtime")
            + " -Dcausynth.static.graph=" + str(
                work / "analysis/static_dataflow_edges.jsonl")
            + " -Dcausynth.symbolic.regions=" + str(
                work / "analysis/symbolic_regions.jsonl")
            + " -Dcausynth.symbolic.region.edges=" + str(
                work / "analysis/symbolic_region_edges.jsonl")
            + " -Dcausynth.trace.test=" + class_name
            + " -cp " + str(work / "instrumented-classes")
            + ":target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar "
            + fqcn + " false false",
        "static_regions": str(work / "analysis/symbolic_regions.jsonl"),
        "static_graph": str(work / "analysis/static_dataflow_edges.jsonl"),
        "runtime_region_plan":
            str(work / "runtime/concolic_region_plan.jsonl"),
        "runtime_edge_validations":
            str(work / "runtime/runtime_region_edge_validation.jsonl"),
        "schedule_output_dir": str(work / "schedule"),
        "raw_concolic_results":
            str(work / "schedule/concolic_region_results.jsonl"),
        "import_task_plan":
            str(work / "schedule/execution_task_plan.jsonl"),
        "imported_summaries":
            str(work / "schedule/concolic_region_summaries.jsonl"),
        "merged_summaries":
            str(work / "schedule/merged_region_summaries.jsonl"),
        "fatal_queries": str(work / "schedule/branch_queries.jsonl"),
        "compose_summary_inputs":
            str(work / "schedule/merged_region_summaries.jsonl"),
        "composed_smt": str(work / "schedule/composed_fatal.smt2"),
    }
    return "\n".join(key + "=" + value for key, value in lines.items()) + "\n"


def main():
    if len(sys.argv) != 3:
        raise SystemExit("usage: generate_regression_round.py ROUND ROOT")
    round_number = int(sys.argv[1])
    if round_number < 1 or round_number > 10:
        raise SystemExit("ROUND must be between 1 and 10")
    root = Path(sys.argv[2])
    root.mkdir(parents=True, exist_ok=False)
    source_dir = root / "src" / Path(PACKAGE.replace(".", "/"))
    source_dir.mkdir(parents=True)
    cases = []
    for index, (left, right, target) in enumerate(programs()):
        class_name = "GeneratedR%02dC%02dWorkload" % (round_number, index)
        target_id = "generated-r%02d-c%02d" % (round_number, index)
        shift = round_number * 20 + index * 2
        source = JAVA_TEMPLATE
        replacements = {
            "@PACKAGE@": PACKAGE,
            "@CLASS@": class_name,
            "@SHIFT@": str(shift),
            "@LEFT_BODY@": indented(left),
            "@RIGHT_BODY@": indented(right),
            "@TARGET@": target,
            "@TARGET_ID@": target_id,
        }
        for marker, value in replacements.items():
            source = source.replace(marker, value)
        (source_dir / (class_name + ".java")).write_text(
            source, encoding="utf-8")
        case_root = root / ("case-%02d" % index)
        case_root.mkdir()
        (case_root / "target.yaml").write_text(
            "exception_target_id: " + target_id + "\n", encoding="utf-8")
        (case_root / "workflow.properties").write_text(
            workflow(root, class_name, target_id, index), encoding="utf-8")
        cases.append({
            "case": index,
            "class": PACKAGE + "." + class_name,
            "targetId": target_id,
            "expected": EXPECTED[index],
            "shape": (
                "scalar", "fixed-loop", "nested-object", "array", "map",
                "mixed-container", "bounded-fields", "parity", "contradiction",
                "nested-order", "array-order", "map-order", "disjoint-values",
            )[index],
        })
    (root / "manifest.json").write_text(json.dumps({
        "schemaVersion": 1,
        "kind": "GENERATED_RPC_REGRESSION_ROUND",
        "round": round_number,
        "cases": cases,
    }, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

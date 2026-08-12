#!/usr/bin/env python3
"""Offline acceptance check for the HDFS-17960 candidate artifacts."""

import argparse
import json
import re
import subprocess
from pathlib import Path


CONFIG_NAME = re.compile(
    r"snapshotDeletionOrdered|isSnapshotDeletionOrdered|"
    r"DFS_NAMENODE_SNAPSHOT_DELETION_ORDERED|"
    r"dfs\.namenode\.snapshot\.deletion\.ordered",
    re.IGNORECASE,
)
CONFIG_CALL = re.compile(
    r"Configuration.*getBoolean|getBoolean.*Configuration",
    re.IGNORECASE,
)
SOLVER_COMMANDS = (
    "(check-sat",
    "(get-model",
    "(get-value",
    "(get-unsat-core",
    "(exit",
)


def fail(message):
    raise SystemExit("[hdfs-17960] verification failed: " + message)


def require(condition, message):
    if not condition:
        fail(message)


def read_json(path):
    require(path.is_file(), "artifact not found: {}".format(path))
    with path.open(encoding="utf-8") as stream:
        return json.load(stream)


def read_jsonl(path):
    require(path.is_file(), "artifact not found: {}".format(path))
    with path.open(encoding="utf-8") as stream:
        return [json.loads(line) for line in stream if line.strip()]


def resolve_artifact(repo_root, value):
    path = Path(value)
    return path.resolve() if path.is_absolute() else (repo_root / path).resolve()


def is_false(value):
    return value is False or (
        isinstance(value, str) and value.lower() == "false"
    )


def is_boolean_type(value):
    return str(value) in (
        "boolean",
        "java.lang.Boolean",
        "Z",
        "Ljava/lang/Boolean;",
    )


def describes_ordered_deletion(candidate):
    materializations = candidate.get("materializations", [])
    text = json.dumps(materializations, sort_keys=True)
    return bool(CONFIG_NAME.search(text)) or (
        "SnapshotManager" in text and bool(CONFIG_CALL.search(text))
    )


def selected_config_candidates(audits):
    selected = []
    for audit in audits:
        if audit.get("status") != "SELECTED":
            continue
        selected_ids = set(audit.get("selectedCandidateIds", []))
        selected_symbols = set(audit.get("selectedSymbols", []))
        for candidate in audit.get("request", {}).get("candidates", []):
            if (
                candidate.get("candidateId") in selected_ids
                and candidate.get("symbol") in selected_symbols
                and describes_ordered_deletion(candidate)
            ):
                selected.append((audit, candidate))
    return selected


def join_config_root(selected, plans, composition, report):
    roots = report.get("roots", {}).get("booleanInputs", [])
    occurrences = composition.get("canonicalPortOccurrences", [])
    supplied = set(composition.get("suppliedInputs", []))
    joined = []

    for audit, candidate in selected:
        symbol = candidate["symbol"]
        for root in roots:
            if root.get("portId") != symbol:
                continue
            if root.get("javaTypeDescriptor") != "Z":
                continue
            instance = root.get("regionInstanceId")
            solver_term = root.get("solverTerm")
            matching_occurrences = [
                row
                for row in occurrences
                if row.get("portId") == symbol
                and row.get("regionInstanceId") == instance
                and row.get("sort") == "BOOL"
                and row.get("solverTerm") == solver_term
            ]
            actions = [
                (task, action)
                for task in plans
                if task.get("regionInstanceId") == instance
                for action in task.get("inputActions", [])
                if action.get("symbol") == symbol
            ]
            symbolic_false = [
                (task, action)
                for task, action in actions
                if action.get("mode") == "SYMBOLIC"
                and is_boolean_type(action.get("javaType"))
                and is_false(action.get("primitiveValue"))
            ]
            contradictory = [
                action
                for _, action in actions
                if action.get("mode") != "SYMBOLIC"
            ]
            if (
                len(matching_occurrences) == 1
                and symbolic_false
                and not contradictory
                and symbol not in supplied
            ):
                joined.append((audit, candidate, root, symbolic_false))

    require(
        len(joined) == 1,
        "expected one ordered-deletion selector-to-root chain; found {}"
        .format(len(joined)),
    )
    return joined[0]


def verify_valuation_table(report, config_root):
    roots = report.get("roots", {}).get("booleanInputs", [])
    indices = [index for index, root in enumerate(roots) if root == config_root]
    require(len(indices) == 1, "ordered-deletion root is not unique")
    index = indices[0]
    valuations = report.get("valuations", [])
    require(valuations, "Boolean valuation table is empty")
    require(
        all(len(row.get("values", [])) == len(roots) for row in valuations),
        "Boolean valuation width does not match the root catalog",
    )
    require(
        all(row.get("status") in ("sat", "unsat") for row in valuations),
        "Boolean valuation table contains an unknown solver result",
    )
    require(
        all(isinstance(row["values"][index], bool) for row in valuations),
        "ordered-deletion valuation is not Boolean",
    )
    false_sat = [
        row
        for row in valuations
        if row["values"][index] is False and row["status"] == "sat"
    ]
    true_rows = [
        row for row in valuations if row["values"][index] is True
    ]
    require(false_sat, "ordered deletion false has no SAT valuation")
    require(
        true_rows and all(row["status"] == "unsat" for row in true_rows),
        "ordered deletion true is not unreachable for every valuation",
    )


def direct_solver_check(smt_path, report, solver_override, root, value):
    with smt_path.open(encoding="utf-8") as stream:
        base = "\n".join(
            line
            for line in stream.read().splitlines()
            if not line.strip().startswith(SOLVER_COMMANDS)
        )
    query = "{}\n(assert (= {} {}))\n(check-sat)\n".format(
        base, root["solverTerm"], value
    )
    solver = solver_override or report.get("solverArtifact", {}).get(
        "path", "z3"
    )
    try:
        result = subprocess.run(
            [solver, "-in"],
            input=query,
            text=True,
            capture_output=True,
            timeout=180,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        fail("could not run Z3: {}".format(error))
    require(result.returncode == 0, "Z3 failed: {}".format(result.stderr.strip()))
    require("(error" not in result.stdout, "Z3 rejected the SMT query")
    statuses = [
        line.strip()
        for line in result.stdout.splitlines()
        if line.strip() in ("sat", "unsat", "unknown")
    ]
    require(len(statuses) == 1, "Z3 did not return one solver status")
    return statuses[0]


def verify(repo_root, work_root, solver_override):
    summary = read_json(work_root / "candidates" / "sat-result.json")
    require(summary.get("reachability") == "REACHABLE", "result is not REACHABLE")
    require(
        summary.get("degeneracyCheck") == "CONSTRAINED_ROOT_SPACE",
        "result does not constrain the root space",
    )
    artifacts = summary.get("artifacts", {})
    z3_path = resolve_artifact(repo_root, artifacts.get("z3Result", ""))
    smt_path = resolve_artifact(repo_root, artifacts.get("smt", ""))
    require(z3_path.parent == smt_path.parent, "SMT and report campaigns differ")
    campaign = z3_path.parent
    composition = read_json(campaign / "composition.json")
    report = read_json(z3_path)

    require(composition.get("state") == "CANDIDATE_READY", "composition is incomplete")
    require(composition.get("trustState") == "CANDIDATE_ONLY", "unexpected composition trust state")
    require(
        composition.get("compositionMode") == "CLOSED_PATH_SET"
        and composition.get("pathSetComplete") is True,
        "composition is not a closed path set",
    )
    require(composition.get("gaps") == [], "composition contains gaps")
    fatal_site = composition.get("fatalSite", "")
    require(
        "FSImageFormatPBSnapshot" in fatal_site
        and "serializeSnapshotSection" in fatal_site,
        "composition names the wrong fatal site",
    )
    require(report.get("state") == "CANDIDATE_READY", "reach report is incomplete")
    require(report.get("trustState") == "CANDIDATE_ONLY", "unexpected reach-report trust state")
    require(report.get("gaps") == [], "reach report contains gaps")
    reach = report.get("reachCondition", {})
    require(reach.get("reachability") == "REACHABLE", "reach report is not REACHABLE")
    require(
        reach.get("degeneracyCheck") == "CONSTRAINED_ROOT_SPACE",
        "reach report does not constrain the root space",
    )

    audits = read_jsonl(work_root / "schedule" / "symbolic_input_selections.jsonl")
    plans = read_jsonl(work_root / "schedule" / "execution_task_plan.jsonl")
    selected = selected_config_candidates(audits)
    require(
        selected,
        "LLM did not explicitly select the ordered-deletion Boolean",
    )
    audit, candidate, config_root, actions = join_config_root(
        selected, plans, composition, report
    )
    verify_valuation_table(report, config_root)
    require(
        direct_solver_check(smt_path, report, solver_override, config_root, "false")
        == "sat",
        "direct SMT check for ordered deletion false is not SAT",
    )
    require(
        direct_solver_check(smt_path, report, solver_override, config_root, "true")
        == "unsat",
        "direct SMT check for ordered deletion true is not UNSAT",
    )

    evidence = {
        "status": "PASS",
        "campaign": campaign.name,
        "selectorDecisionId": audit["decisionId"],
        "candidateId": candidate["candidateId"],
        "configPortId": config_root["portId"],
        "regionInstanceId": config_root["regionInstanceId"],
        "solverTerm": config_root["solverTerm"],
        "taskIds": sorted(set(task["taskId"] for task, _ in actions)),
        "orderedDeletionFalse": "sat",
        "orderedDeletionTrue": "unsat",
        "reachability": reach["reachability"],
        "degeneracyCheck": reach["degeneracyCheck"],
    }
    print(json.dumps(evidence, indent=2, sort_keys=True))


def main():
    repo_root = Path(__file__).resolve().parents[3]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--work-root",
        type=Path,
        default=repo_root / "experiments-output" / "hdfs-17960",
    )
    parser.add_argument("--z3", help="override the solver recorded in z3-result.json")
    arguments = parser.parse_args()
    work_root = arguments.work_root
    if not work_root.is_absolute():
        work_root = repo_root / work_root
    verify(repo_root, work_root.resolve(), arguments.z3)


if __name__ == "__main__":
    main()

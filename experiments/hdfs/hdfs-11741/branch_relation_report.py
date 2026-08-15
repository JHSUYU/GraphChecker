#!/usr/bin/env python3
"""Show concrete expiry/T_recv relations in an HDFS-11741 path flip."""

import argparse
import importlib.util
import json
import os
import re
import subprocess
import sys
import tempfile


HERE = os.path.dirname(os.path.abspath(__file__))


def load_sibling(name):
    path = os.path.join(HERE, name + ".py")
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


AUDIT = load_sibling("solver_binding_audit")
SMT = load_sibling("smt_realizability_refine")

DECL = re.compile(r"^\(declare-const (\S+) (.+)\)$")
NAMED = re.compile(r":named\s+([^\s()]+)")
CLOCK_NAME = re.compile(r"^environment__.*currentTimeMills_\d+__\S+$")
ORDER_OPS = {"<", "<=", ">", ">=", "="}
REVERSE_OP = {"<": ">", "<=": ">=", ">": "<", ">=": "<=", "=": "="}
COMPLEMENT_OP = {
    "<": ">=", "<=": ">", ">": "<=", ">=": "<", "=": "!=",
}


def integer_value(value):
    if isinstance(value, str) and re.fullmatch(r"-?\d+", value):
        return int(value)
    if (isinstance(value, list) and len(value) == 2
            and value[0] == "-" and str(value[1]).isdigit()):
        return -int(value[1])
    return None


def readable_value(value):
    parsed = SMT.parse_sexpr(value)
    if len(parsed) == 1:
        integer = integer_value(parsed[0])
        if integer is not None:
            return str(integer)
    return value


def decode_long_compare(value):
    """Decode ite(left<right,-1,ite(left>right,1,0))."""
    if not isinstance(value, list) or len(value) != 4 or value[0] != "ite":
        return None
    less, negative, fallback = value[1:]
    if (not isinstance(less, list) or len(less) != 3 or less[0] != "<"
            or integer_value(negative) != -1):
        return None
    if (not isinstance(fallback, list) or len(fallback) != 4
            or fallback[0] != "ite"):
        return None
    greater, positive, equal = fallback[1:]
    if (not isinstance(greater, list) or len(greater) != 3
            or greater[0] != ">" or integer_value(positive) != 1
            or integer_value(equal) != 0 or less[1:] != greater[1:]):
        return None
    if not isinstance(less[1], str) or not isinstance(less[2], str):
        return None
    return less[1], less[2]


def normalize(operator, left, right, clocks, declared):
    if left in clocks and right in declared and right not in clocks:
        return {"expiryTerm": right, "recvTerm": left,
                "operator": REVERSE_OP[operator]}
    if right in clocks and left in declared and left not in clocks:
        return {"expiryTerm": left, "recvTerm": right,
                "operator": operator}
    return None


def decode_relation(node, clocks, declared):
    if isinstance(node, list) and len(node) == 2 and node[0] == "not":
        decoded = decode_relation(node[1], clocks, declared)
        if decoded:
            decoded["operator"] = COMPLEMENT_OP[decoded["operator"]]
        return decoded
    if not isinstance(node, list) or len(node) != 3 or node[0] not in ORDER_OPS:
        return None
    operator, left, right = node
    left_compare = decode_long_compare(left)
    right_compare = decode_long_compare(right)
    if left_compare and integer_value(right) == 0:
        return normalize(operator, *left_compare, clocks, declared)
    if right_compare and integer_value(left) == 0:
        return normalize(REVERSE_OP[operator], *right_compare,
                         clocks, declared)
    if isinstance(left, str) and isinstance(right, str):
        return normalize(operator, left, right, clocks, declared)
    return None


def relations_in(node, clocks, declared):
    """Stop below a decoded long comparison to avoid reporting it twice."""
    decoded = decode_relation(node, clocks, declared)
    if decoded:
        return [decoded]
    found = []
    if isinstance(node, list):
        for child in node:
            found.extend(relations_in(child, clocks, declared))
    return found


def discover_relations(text):
    declared = {}
    for line in text.splitlines():
        match = DECL.match(line.strip())
        if match:
            declared[match.group(1)] = match.group(2)
    clocks = {name for name, sort in declared.items()
              if sort == "Int" and CLOCK_NAME.match(name)}
    relations = []
    for _start, _end, form in AUDIT.top_level_forms(text):
        if AUDIT.form_head(form) != "assert":
            continue
        parsed = SMT.parse_sexpr(form)
        body = parsed[0][1]
        if isinstance(body, list) and body and body[0] == "!":
            body = body[1]
        name_match = NAMED.search(form)
        name = name_match.group(1) if name_match else "unnamed"
        for relation in relations_in(body, clocks, declared):
            relation["assertion"] = name
            relations.append(relation)
    if relations:
        for relation in relations[:-1]:
            relation["role"] = "prefix"
        relations[-1]["role"] = "flipped_target"
    return relations


def solver_query(text, relations, include_values):
    definitions = []
    aliases = []
    if include_values:
        for index, relation in enumerate(relations):
            alias = "hdfs11741_branch_relation_%d" % index
            relation["valueAlias"] = alias
            definitions.append("(define-fun %s () Bool (%s %s %s))" % (
                alias, relation["operator"], relation["expiryTerm"],
                relation["recvTerm"]))
            aliases.append(alias)
    query = AUDIT.build_query(text, additions=definitions)
    if include_values:
        terms = []
        for relation in relations:
            for term in (relation["expiryTerm"], relation["recvTerm"]):
                if term not in terms:
                    terms.append(term)
        query += "(get-value (%s))\n" % " ".join(terms + aliases)
    return query


def run_z3(binary, query, timeout_ms):
    seconds = max(1, int((timeout_ms + 999) / 1000))
    path = None
    try:
        with tempfile.NamedTemporaryFile(
                mode="w", encoding="utf-8", newline="\n",
                prefix="hdfs11741-branch-", suffix=".smt2",
                delete=False) as handle:
            path = handle.name
            handle.write(query)
        completed = subprocess.run(
            [binary, "-T:%d" % seconds, path],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=seconds + 5, check=False)
    except subprocess.TimeoutExpired as error:
        raise ValueError("solver timed out") from error
    finally:
        if path and os.path.exists(path):
            os.unlink(path)
    output = completed.stdout.decode("utf-8", errors="replace")
    answers = [line.strip() for line in output.splitlines()
               if line.strip() in ("sat", "unsat", "unknown")]
    if (completed.returncode != 0 or len(answers) != 1
            or "(error " in output):
        raise ValueError("solver did not return one clean verdict")
    return answers[0], output


def analyze(smt_path, z3, timeout_ms):
    with open(smt_path, encoding="utf-8") as handle:
        text = handle.read()
    relations = discover_relations(text)
    if not relations:
        raise ValueError(
            "no expiry/current-time branch relation found in SMT query")
    status, _output = run_z3(
        z3, solver_query(text, relations, False), timeout_ms)
    values = {}
    if status == "sat":
        value_status, value_output = run_z3(
            z3, solver_query(text, relations, True), timeout_ms)
        if value_status != "sat":
            raise ValueError("model query changed solver verdict")
        terms = [term for relation in relations for term in (
            relation["expiryTerm"], relation["recvTerm"],
            relation["valueAlias"])]
        values = SMT.parse_get_value(value_output, terms)
    report = {"status": status, "branchRelations": []}
    prefix_number = 0
    for relation in relations:
        if relation["role"] == "prefix":
            prefix_number += 1
            expiry_label = "expiry[%d]" % prefix_number
        else:
            expiry_label = "expiry"
        entry = {
            "role": relation["role"],
            "assertion": relation["assertion"],
            "relation": "%s %s T_recv" % (
                expiry_label, relation["operator"]),
        }
        if relation["role"] == "flipped_target":
            entry["observedRelation"] = "expiry %s T_recv" % (
                COMPLEMENT_OP[relation["operator"]])
        if status == "sat":
            entry.update({
                "expiryValue": readable_value(values.get(
                    relation["expiryTerm"], "?")),
                "recvValue": readable_value(values.get(
                    relation["recvTerm"], "?")),
                "evaluatesTo": values.get(relation["valueAlias"]) == "true",
            })
        report["branchRelations"].append(entry)
    return report


def render_text(report):
    lines = ["solver: %s" % report["status"],
             "DataNode expiry branch relations:"]
    for branch in report["branchRelations"]:
        role = ("flipped target" if branch["role"] == "flipped_target"
                else "required prefix")
        lines.append("  %s (%s): %s" % (
            role, branch["assertion"], branch["relation"]))
        if report["status"] == "sat":
            lines.append("    expiry = %s, T_recv = %s, evaluates to %s" % (
                branch["expiryValue"], branch["recvValue"],
                str(branch["evaluatesTo"]).lower()))
    target = report["branchRelations"][-1]
    lines.append("branch flip: %s  ->  %s" % (
        target["observedRelation"], target["relation"]))
    return "\n".join(lines)


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Show concrete expiry/T_recv relations in a SAT "
                    "HDFS-11741 path-flip query.")
    parser.add_argument("--smt", required=True)
    parser.add_argument("--z3", default="z3")
    parser.add_argument("--solver-timeout-ms", type=int, default=30000)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = analyze(os.path.abspath(args.smt),
                         AUDIT.resolve_solver(args.z3),
                         args.solver_timeout_ms)
    except (OSError, ValueError) as error:
        print("error: %s" % error, file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2, sort_keys=True)
          if args.json else render_text(report))
    return 0


if __name__ == "__main__":
    sys.exit(main())

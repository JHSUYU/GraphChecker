#!/usr/bin/env python3
"""Solver-native fatal-operand pin and edge-ablation audit.

The composer manifest supplies an application-independent ledger containing
the exact SMT terms, sorts, producer-version terms, edge assertion names, and
fatal-path assertion.  This tool never reconstructs expressions from source
names and never adds application formulas.

The important baseline is the relation-only query: every assertion the
composer ledger marks as fatal-dependent is removed while every producer
relation remains.  It must be SAT before any pin result is interpreted.  Each
operand's own path prefix must also be SAT before its pin and edge ablations
run, so neither an UNSAT final query nor an impossible sibling path can make a
binding check pass vacuously.
"""

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time


AUDIT_VERSION = "solver-pin-ablation-v2-exact-lineage"
SOLVER_COMMANDS = {
    "check-sat", "check-sat-assuming", "get-model", "get-value",
    "get-unsat-core", "get-assignment", "get-proof", "exit",
}
HEAD = re.compile(r"^\s*\(\s*([^\s()]+)")
NAMED = re.compile(r":named\s+([^\s()]+)")


def sha256_bytes(value):
    return hashlib.sha256(value).hexdigest()


def sha256_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def artifact(path):
    return {"path": os.path.abspath(path), "sha256": sha256_file(path)}


def top_level_forms(text):
    """Return (start, end, form) for every top-level SMT-LIB form."""
    forms = []
    depth = 0
    start = None
    in_string = False
    in_bar = False
    in_comment = False
    index = 0
    while index < len(text):
        char = text[index]
        if in_comment:
            if char == "\n":
                in_comment = False
            index += 1
            continue
        if in_string:
            if char == '"':
                if index + 1 < len(text) and text[index + 1] == '"':
                    index += 2
                    continue
                in_string = False
            index += 1
            continue
        if in_bar:
            if char == "|":
                in_bar = False
            index += 1
            continue
        if char == ";":
            in_comment = True
        elif char == '"':
            in_string = True
        elif char == "|":
            in_bar = True
        elif char == "(":
            if depth == 0:
                start = index
            depth += 1
        elif char == ")":
            depth -= 1
            if depth < 0:
                raise ValueError("unbalanced ')' in SMT input")
            if depth == 0 and start is not None:
                end = index + 1
                forms.append((start, end, text[start:end]))
                start = None
        index += 1
    if depth != 0 or in_string or in_bar:
        raise ValueError("unterminated SMT-LIB form or quoted token")
    return forms


def form_head(form):
    match = HEAD.match(form)
    return match.group(1) if match else ""


def named_assertion(form):
    if form_head(form) != "assert":
        return ""
    matches = NAMED.findall(form)
    if len(matches) > 1:
        raise ValueError("one assertion contains multiple :named attributes")
    return matches[0] if matches else ""


def named_assertions(text):
    result = {}
    for _start, _end, form in top_level_forms(text):
        name = named_assertion(form)
        if not name:
            continue
        if name in result:
            raise ValueError("duplicate named assertion: %s" % name)
        result[name] = form
    return result


def build_query(text, removed=(), additions=()):
    """Remove exact named assertions and solver commands, then append checks."""
    removed = set(removed)
    found = set()
    output = []
    cursor = 0
    for start, end, form in top_level_forms(text):
        output.append(text[cursor:start])
        head = form_head(form)
        name = named_assertion(form)
        if name in removed:
            found.add(name)
        elif head not in SOLVER_COMMANDS:
            output.append(form)
        cursor = end
    output.append(text[cursor:])
    missing = removed - found
    if missing:
        raise ValueError("named assertions not found: %s" %
                         ", ".join(sorted(missing)))
    base = "".join(output).rstrip() + "\n"
    if additions:
        base += "; ---- %s derived assertions ----\n" % AUDIT_VERSION
        for addition in additions:
            base += addition.rstrip() + "\n"
    return base + "(check-sat)\n"


def safe_label(value):
    readable = re.sub(r"[^A-Za-z0-9_.-]+", "_", value).strip("_.-")
    readable = readable[:48] or "item"
    suffix = hashlib.sha256(value.encode("utf-8")).hexdigest()[:10]
    return "%s-%s" % (readable, suffix)


def write_text(path, value):
    directory = os.path.dirname(os.path.abspath(path))
    os.makedirs(directory, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(
                mode="w", encoding="utf-8", newline="\n",
                prefix=".%s." % os.path.basename(path), suffix=".tmp",
                dir=directory, delete=False) as handle:
            temporary = handle.name
            handle.write(value)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if temporary and os.path.exists(temporary):
            os.unlink(temporary)


def write_json(path, value):
    write_text(path, json.dumps(value, indent=2, sort_keys=True) + "\n")


def resolve_solver(binary):
    selected = shutil.which(binary) if not os.path.isabs(binary) else binary
    if not selected or not os.path.isfile(selected):
        raise ValueError("solver executable not found: %s" % binary)
    return os.path.realpath(selected)


def solver_identity(binary):
    path = resolve_solver(binary)
    completed = subprocess.run(
        [path, "-version"], stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False)
    version = completed.stdout.decode("utf-8", errors="replace").strip()
    return {
        "requestedBinary": binary,
        "resolvedBinary": path,
        "binarySha256": sha256_file(path),
        "version": version,
        "versionOutputSha256": sha256_bytes(completed.stdout),
    }


def run_solver(binary, query_path, timeout_ms):
    seconds = max(1, int((timeout_ms + 999) / 1000))
    started = time.monotonic()
    timed_out = False
    try:
        completed = subprocess.run(
            [binary, "-T:%d" % seconds, query_path],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=max(1.0, timeout_ms / 1000.0 + 2.0), check=False)
        output = completed.stdout
        return_code = completed.returncode
    except subprocess.TimeoutExpired as timeout:
        timed_out = True
        output = (timeout.stdout or b"") + (timeout.stderr or b"")
        return_code = None
    elapsed_ms = int(round((time.monotonic() - started) * 1000))
    decoded = output.decode("utf-8", errors="replace")
    answers = [line.strip() for line in decoded.splitlines()
               if line.strip() in ("sat", "unsat", "unknown")]
    solver_error = return_code not in (0, None) or bool(re.search(
        r"(?im)^\s*(?:\(error\b|error:)", decoded))
    if timed_out:
        status = "timeout"
    elif solver_error or len(answers) != 1:
        status = "solver_error"
    else:
        status = answers[0]
    return {
        "status": status,
        "elapsedMs": elapsed_ms,
        "solverExitCode": return_code,
        "answerCount": len(answers),
        "solverOutputSha256": sha256_bytes(output),
        "diagnostic": decoded[:2000],
    }


def solve_derived(binary, timeout_ms, directory, filename, query):
    path = os.path.join(directory, filename)
    write_text(path, query)
    result = run_solver(binary, path, timeout_ms)
    result["queryArtifact"] = artifact(path)
    return result


def pin_assertion(operand):
    versions = []
    seen = set()
    pin_sort = operand.get("pinSort", "")
    for version in operand.get("producerVersions", []):
        term = version.get("solverTerm", "")
        if (version.get("solverSort") != pin_sort or not term or term in seen):
            continue
        seen.add(term)
        versions.append(term)
    if not versions:
        return "", []
    pin_term = operand.get("pinTerm", "")
    if not pin_term:
        raise ValueError("operand %s has no pinTerm" %
                         operand.get("operandId", "<unknown>"))
    distinct = ["(distinct %s %s)" % (pin_term, term)
                for term in versions]
    formula = distinct[0] if len(distinct) == 1 else \
        "(and %s)" % " ".join(distinct)
    name = "audit_pin_%s" % safe_label(operand["operandId"])
    return "(assert (! %s :named %s))" % (formula, name), versions


def path_prefix_assertion(operand):
    """Select the exact fatal path whose operand is being audited."""
    term = operand.get("pathPrefixTerm", "")
    if not term:
        raise ValueError("operand %s has no pathPrefixTerm" %
                         operand.get("operandId", "<unknown>"))
    ordinal = operand.get("pathOrdinal")
    name = "audit_path_prefix_%s" % safe_label(str(ordinal))
    return "(assert (! %s :named %s))" % (term, name)


def edge_evidence_summary(operand_result):
    """Require a solver-demonstrated load-bearing edge for every bound leaf."""
    if operand_result.get("bindingStatus") != \
            "BOUND_TO_RECORDED_PRODUCER_VERSIONS":
        return "NOT_APPLICABLE", False, False
    classifications = [row.get("classification") for row in
                       operand_result.get("edgeAblations", [])]
    if "LOAD_BEARING" in classifications:
        return "LOAD_BEARING_EDGE_FOUND", False, False
    if "INCONCLUSIVE" in classifications:
        return "INCONCLUSIVE", False, True
    return "NO_LOAD_BEARING_EDGE", True, False


def validate_manifest(manifest, smt_path, assertions):
    if manifest.get("kind") != "CONCOLIC_COMPOSED_SMT":
        raise ValueError("not a CONCOLIC_COMPOSED_SMT manifest")
    if manifest.get("state") != "CANDIDATE_READY":
        raise ValueError("composition is not CANDIDATE_READY")
    expected = manifest.get("composedSmtArtifact", {}).get("sha256", "")
    actual = sha256_file(smt_path)
    if not re.fullmatch(r"[0-9a-f]{64}", expected):
        raise ValueError("composition manifest has no valid SMT sha256")
    if expected != actual:
        raise ValueError("SMT hash does not match composition manifest")
    ledger = manifest.get("operandBindingLedger", {})
    if ledger.get("kind") != "FATAL_OPERAND_BINDING_LEDGER" \
            or ledger.get("schemaVersion") != 2:
        raise ValueError("composition has no supported operand binding ledger")
    fatal = ledger.get("fatalPathAssertion", {}).get("name", "")
    if not fatal or fatal not in assertions:
        raise ValueError("fatal-path assertion is absent from SMT")
    fatal_dependent = ledger.get("fatalDependentAssertionNames")
    if not isinstance(fatal_dependent, list) or not fatal_dependent \
            or fatal not in fatal_dependent \
            or len(fatal_dependent) != len(set(fatal_dependent)):
        raise ValueError("invalid fatal-dependent assertion ledger")
    for name in fatal_dependent:
        if not isinstance(name, str) or name not in assertions:
            raise ValueError("fatal-dependent assertion absent from SMT: %s"
                             % name)
    retained_prefix = ledger.get(
        "retainedPathPrefixAssertion", {}).get("name", "")
    if not retained_prefix or retained_prefix not in assertions:
        raise ValueError("retained path-prefix assertion is absent from SMT")
    edge_catalog = {
        row.get("edgeId"): set(row.get("assertionNames", []))
        for row in ledger.get("edgeAssertions", []) if row.get("edgeId")
    }
    operands = ledger.get("operands")
    if not isinstance(operands, list):
        raise ValueError("operand binding ledger operands must be an array")
    paths = ledger.get("paths")
    if not isinstance(paths, list) or not paths:
        raise ValueError("operand binding ledger paths must be non-empty")
    path_prefixes = {}
    for path in paths:
        ordinal = path.get("pathOrdinal")
        prefix = path.get("pathPrefixTerm", "")
        if not isinstance(ordinal, int) or ordinal in path_prefixes \
                or not prefix:
            raise ValueError("invalid or duplicate fatal path ledger row")
        path_prefixes[ordinal] = prefix
    operand_ids = set()
    actual_path_counts = {ordinal: 0 for ordinal in path_prefixes}
    for operand in operands:
        operand_id = operand.get("operandId", "")
        if not operand_id or operand_id in operand_ids:
            raise ValueError("missing or duplicate operandId")
        if not operand.get("pathPrefixTerm", ""):
            raise ValueError("operand %s has no pathPrefixTerm" % operand_id)
        ordinal = operand.get("pathOrdinal")
        if ordinal not in path_prefixes or operand["pathPrefixTerm"] != \
                path_prefixes[ordinal]:
            raise ValueError("operand/path prefix ledger mismatch: %s" %
                             operand_id)
        actual_path_counts[ordinal] += 1
        operand_ids.add(operand_id)
        lineage = operand.get("producerLineageStatus", "")
        if lineage not in ("EXACT_TARGET_PORT_OCCURRENCE",
                           "UNAUDITABLE_NO_EXACT_PRODUCER_LINEAGE"):
            raise ValueError("operand has no supported producer lineage: %s" %
                             operand_id)
        exact_port = operand.get("portId", "")
        exact_instance = operand.get("regionInstanceId", "")
        versions = operand.get("producerVersions", [])
        if lineage == "UNAUDITABLE_NO_EXACT_PRODUCER_LINEAGE":
            if exact_port or exact_instance or versions:
                raise ValueError("unauditable operand carries producer evidence: "
                                 "%s" % operand_id)
        else:
            if not exact_port or not exact_instance:
                raise ValueError("exact producer lineage lacks target occurrence: "
                                 "%s" % operand_id)
            if operand.get("pinTerm") != operand.get("solverTerm") or \
                    operand.get("pinSort") != operand.get("solverSort"):
                raise ValueError("exact operand pin is not solver-native: %s" %
                                 operand_id)
        for version in versions:
            edge_id = version.get("edgeId", "")
            name = version.get("assertionName", "")
            if name not in assertions:
                raise ValueError("edge assertion absent from SMT: %s" % name)
            if name not in edge_catalog.get(edge_id, set()):
                raise ValueError("edge/assertion ledger cross-link mismatch")
            if version.get("targetPortId") != exact_port or \
                    version.get("targetRegionInstanceId") != exact_instance:
                raise ValueError("producer version targets another operand "
                                 "occurrence: %s" % operand_id)
            if version.get("solverSort") != operand.get("pinSort"):
                raise ValueError("producer version sort differs from exact "
                                 "operand pin: %s" % operand_id)
    for path in paths:
        ordinal = path["pathOrdinal"]
        if path.get("operandCount") != actual_path_counts[ordinal]:
            raise ValueError("fatal path operandCount mismatch: %s" % ordinal)
    return ledger


def execute(args):
    os.makedirs(args.output_dir, exist_ok=True)
    with open(args.smt, "r", encoding="utf-8") as handle:
        smt = handle.read()
    with open(args.manifest, "r", encoding="utf-8") as handle:
        manifest = json.load(handle)
    assertions = named_assertions(smt)
    ledger = validate_manifest(manifest, args.smt, assertions)
    identity = solver_identity(args.z3)
    solver = identity["resolvedBinary"]

    final_query = build_query(smt)
    final_result = solve_derived(solver, args.solver_timeout_ms,
                                 args.output_dir, "final-query.smt2",
                                 final_query)
    fatal_name = ledger["fatalPathAssertion"]["name"]
    fatal_dependent = ledger["fatalDependentAssertionNames"]
    relation_query = build_query(smt, removed=fatal_dependent)
    relation_result = solve_derived(
        solver, args.solver_timeout_ms, args.output_dir,
        "relation-only.smt2", relation_query)

    report = {
        "schemaVersion": 1,
        "kind": "SOLVER_OPERAND_PIN_ABLATION_AUDIT",
        "algorithmVersion": AUDIT_VERSION,
        "input": {
            "smt": artifact(args.smt),
            "compositionManifest": artifact(args.manifest),
        },
        "solver": dict(identity, timeoutMs=args.solver_timeout_ms),
        "finalQuery": final_result,
        "relationOnlyBaseline": relation_result,
        "vacuityGuard": {
            "basis": "ALL_FATAL_DEPENDENT_ASSERTIONS_REMOVED",
            "fatalPathAssertion": fatal_name,
            "removedFatalDependentAssertions": fatal_dependent,
            "retainedPathPrefixAssertion": ledger[
                "retainedPathPrefixAssertion"]["name"],
            "status": "PASSED" if relation_result["status"] == "sat"
            else "FAILED",
        },
        "findings": [],
        "operands": [],
    }
    if relation_result["status"] != "sat":
        report["state"] = "NON_AUDITABLE_RELATION_BASELINE"
        report["reason"] = "relation-only baseline must be SAT"
        return report, 2

    ledger_operands = ledger.get("operands", [])
    final_decided = final_result["status"] in ("sat", "unsat")
    unknown = not final_decided
    findings = not ledger_operands
    if not final_decided:
        report["findings"].append("FINAL_QUERY_NOT_DECIDED:%s" %
                                  final_result["status"])
    if not ledger_operands:
        report["findings"].append("NO_FATAL_OPERANDS_CAPTURED")
    for path in ledger.get("paths", []):
        if path.get("operandCount") == 0:
            findings = True
            report["findings"].append(
                "NO_FATAL_OPERANDS_FOR_PATH:%s" % path.get("pathOrdinal"))
    for operand in ledger_operands:
        operand_id = operand["operandId"]
        row = {
            "operandId": operand_id,
            "pathOrdinal": operand.get("pathOrdinal"),
            "solverTerm": operand.get("solverTerm"),
            "solverSort": operand.get("solverSort"),
            "pinTerm": operand.get("pinTerm"),
            "pinSort": operand.get("pinSort"),
            "portId": operand.get("portId"),
            "regionInstanceId": operand.get("regionInstanceId"),
            "producerLineageStatus": operand.get("producerLineageStatus"),
            "producerVersions": operand.get("producerVersions", []),
            "edgeAblations": [],
        }
        if operand.get("producerLineageStatus") == \
                "UNAUDITABLE_NO_EXACT_PRODUCER_LINEAGE":
            row["bindingStatus"] = \
                "UNAUDITABLE_NO_EXACT_PRODUCER_LINEAGE"
            row["edgeEvidenceStatus"] = "INCONCLUSIVE"
            report["findings"].append(
                "UNAUDITABLE_FATAL_OPERAND:%s" % operand_id)
            unknown = True
            report["operands"].append(row)
            continue
        pin, version_terms = pin_assertion(operand)
        if not pin:
            row["bindingStatus"] = "NO_PRODUCER_VERSIONS"
            row["edgeEvidenceStatus"] = "NOT_APPLICABLE"
            findings = True
            report["operands"].append(row)
            continue
        label = safe_label(operand_id)
        selected_path = path_prefix_assertion(operand)
        path_query = build_query(relation_query,
                                 additions=[selected_path])
        path_result = solve_derived(
            solver, args.solver_timeout_ms, args.output_dir,
            "path-%s.smt2" % label, path_query)
        row["pathRelationBaseline"] = path_result
        if path_result["status"] != "sat":
            row["bindingStatus"] = "INCONCLUSIVE_PATH_BASELINE"
            row["edgeEvidenceStatus"] = "NOT_APPLICABLE"
            unknown = True
            report["operands"].append(row)
            continue
        pin_query = build_query(path_query, additions=[pin])
        pin_result = solve_derived(
            solver, args.solver_timeout_ms, args.output_dir,
            "pin-%s.smt2" % label, pin_query)
        row["producerVersionTerms"] = version_terms
        row["pinResult"] = pin_result
        if pin_result["status"] == "unsat":
            row["bindingStatus"] = "BOUND_TO_RECORDED_PRODUCER_VERSIONS"
        elif pin_result["status"] == "sat":
            row["bindingStatus"] = "NOT_BOUND_TO_RECORDED_PRODUCER_VERSIONS"
            findings = True
        else:
            row["bindingStatus"] = "INCONCLUSIVE"
            unknown = True

        assertions_by_edge = {}
        for version in operand.get("producerVersions", []):
            assertions_by_edge.setdefault(version["edgeId"], set()).add(
                version["assertionName"])
        for edge_id in sorted(assertions_by_edge):
            removed = sorted(assertions_by_edge[edge_id])
            ablated = build_query(path_query, removed=removed,
                                  additions=[pin])
            ablation_result = solve_derived(
                solver, args.solver_timeout_ms, args.output_dir,
                "ablate-%s-%s.smt2" %
                (label, safe_label(edge_id)), ablated)
            status = ablation_result["status"]
            if status == "sat":
                classification = "LOAD_BEARING"
            elif status == "unsat":
                classification = "REDUNDANT_OR_NOT_LOAD_BEARING"
            else:
                classification = "INCONCLUSIVE"
                unknown = True
            row["edgeAblations"].append({
                "edgeId": edge_id,
                "removedAssertionNames": removed,
                "classification": classification,
                "result": ablation_result,
            })
        edge_status, edge_finding, edge_unknown = edge_evidence_summary(row)
        row["edgeEvidenceStatus"] = edge_status
        findings = findings or edge_finding
        unknown = unknown or edge_unknown
        report["operands"].append(row)

    report["state"] = "INCONCLUSIVE" if unknown else \
        "AUDITED_WITH_FINDINGS" if findings else "AUDITED"
    exit_code = 0 if report["state"] == "AUDITED" else \
        1 if report["state"] == "AUDITED_WITH_FINDINGS" else 2
    return report, exit_code


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Audit fatal operand bindings with solver pins and "
                    "exact named-edge ablations.")
    parser.add_argument("--smt", required=True,
                        help="composed candidate SMT")
    parser.add_argument("--manifest", required=True,
                        help="matching composition manifest")
    parser.add_argument("--output-dir", default=None,
                        help="default: <candidate>/solver-binding-audit")
    parser.add_argument("--z3", default="z3")
    parser.add_argument("--solver-timeout-ms", type=int, default=180000)
    args = parser.parse_args(argv)
    args.smt = os.path.abspath(args.smt)
    args.manifest = os.path.abspath(args.manifest)
    if args.output_dir is None:
        args.output_dir = os.path.join(os.path.dirname(args.smt),
                                       "solver-binding-audit")
    args.output_dir = os.path.abspath(args.output_dir)

    try:
        report, exit_code = execute(args)
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print("solver binding audit: %s" % error, file=sys.stderr)
        return 2
    report_path = os.path.join(args.output_dir,
                               "solver-binding-audit.json")
    try:
        write_json(report_path, report)
    except OSError as error:
        # Publication is part of the audit contract.  In particular, do not
        # let an I/O failure use exit code 1, which is reserved for a durable
        # AUDITED_WITH_FINDINGS report.  The atomic writer leaves any prior
        # report intact, and this explicit diagnostic tells callers not to
        # mistake it for the current invocation.
        print("solver binding audit report was not published: %s" % error,
              file=sys.stderr)
        return 2
    print(report_path)
    return exit_code


if __name__ == "__main__":
    sys.exit(main())

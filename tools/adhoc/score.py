#!/usr/bin/env python3
"""score.py <static-dir> : whether the engine can move a check's fatal
condition, read off the check's own static slice, the static half of SEED
(run_engine.sh `slice`): <static-dir>/candidate_dataflow_edges.jsonl.gz,
static_scope_map.jsonl, region_skeletons.jsonl.gz and scope_frontier.jsonl.
Writes <static-dir>/score.json and prints its counts.

The fatal operands are what the throw's branches read: the from-cell of the
exception_guard edge and of every guard_dependency edge of a branch of the
TARGET_SITE row -- a guard, a chain guard, or the helper branch that decides
one (a helper whose return is a constant its own branch chose).  Their
closure walks the data edges backward (every kind but the guard and throw
kinds), a field to every store of it, up to DEPTH edges; a cell remembers its
depth, whether its path crossed a field or a wire (mediated), and whether it
entered through a store's guard (control): the operands of a store's own
branches enter the closure one edge deeper, since a root that decides whether
a store runs moves the value the check later reads, and exploration flips a
writer at its own guards.

What the closure reaches, by the kinds of roots the engine moves:
  clock         DECLARED_SITE inputKind=CLOCK rows whose cell it holds
  fault         DECLARED_SITE inputKind=FAULT rows whose cell it holds, and
                every door (a FAULT row's method) that a store or export in
                it reaches within DOOR_CALLS calls of the edge set (caller
                to callee): the door's fault skips the rest of its callers.
                Every map carries every door's FAULT rows, declared whatever
                the slice, so a row alone says nothing.
  read          DECLARED_SITE inputKind=READ rows whose cell it holds
  crossRegion   (field, writer region) pairs of a field it holds that a
                region other than the check's own stores
  crossProcess  cells a wire delivers that it holds: a wire_handoff edge's
                consumer, or an IN port's attach cell
and, for the R1 engine work, `unrooted`: the tracked reads (READ_SITE) it
holds whose own closure reaches none of these, and `truncated`: whether it
stops where the scope cut the slice (scope_frontier.jsonl: a callee or formal
it holds, or a field it holds that nothing in scope stores).  `roots` lists
each root found: its kind, site, depth, and whether its path was mediated (a
field or wire store is itself one) or control.

  keep  = a root at most KEEP_DEPTH edges from the fatal operands
  score = 4[clock] + 4[fault] + 3 min(3, crossProcess) + 2 min(3, crossRegion)
          + read + 2[a root reached through a mediated path]
          - (depth of the nearest root) / 8

KEEP_DEPTH is calibrated on the 260 finished verdicts of sweeps h4 and q2-q13
(2026-09-30): 195 of them saw the anchor decided concretely.  A slice reaches
some root for 234 of the 260; one within 4 edges for 153, of which 66% were
decided concretely, against 88% of the 107 it drops -- which keep 52 of the
65 symbolic anchors and every accepted target of either system (nearest root at
1-3 edges).  A longer chain is one a propagation hole breaks more often.
"""
import collections
import gzip
import json
import os
import sys

DEPTH = 16
KEEP_DEPTH = 4
DOOR_CALLS = 3
KINDS = ("clock", "fault", "read", "crossRegion", "crossProcess")
NOT_DATA = {"guard_dependency", "exception_guard", "exception_throw",
            "throw_dependency"}


def method_of(cell):
    """The method a cell of a method belongs to; "" for a field."""
    end = cell.find(")>")
    return cell[:end + 2] if cell.startswith("<") and end > 0 else ""


def is_field(cell):
    return cell.startswith("<") and cell.endswith(">") and not method_of(cell)


def rows(path):
    opener = gzip.open if path.endswith(".gz") else open
    with opener(path, "rt") as source:
        for line in source:
            if line.strip():
                yield json.loads(line)


def branches(site):
    """The branch sites a scope-map row runs under: its guards, its chain,
    and the helper branch deciding any of them."""
    found = list(site.get("guards", []))
    for decider in site.get("guardDeciders", {}).values():
        found.append(decider["siteId"])
    for guard in site.get("chain", []):
        while guard:
            found.append(guard["siteId"])
            guard = guard.get("decider")
    return found


class Slice:
    def __init__(self, directory):
        self.into = collections.defaultdict(list)   # to-cell -> data edges
        self.operands = collections.defaultdict(set)  # branch -> cells
        self.calls = collections.defaultdict(set)   # caller -> callees
        self.consumers = set()                      # wire-delivered cells
        fatal = set()
        for edge in rows(os.path.join(directory,
                                      "candidate_dataflow_edges.jsonl.gz")):
            kind, source, target = edge["kind"], edge["fromCell"], edge["toCell"]
            if kind == "exception_guard":
                fatal.add(source)
            elif kind == "guard_dependency":
                self.operands[edge["siteId"]].add(source)
            if kind not in NOT_DATA:
                self.into[target].append(edge)
            if kind == "wire_handoff":
                self.consumers.add(target)
            elif "invoke" in edge:
                caller = edge["method"]
                callee = method_of(target if method_of(source) == caller
                                   else source)
                if callee and callee != caller:
                    self.calls[caller].add(callee)
        self.sites = collections.defaultdict(list)  # role -> rows
        for row in rows(os.path.join(directory, "static_scope_map.jsonl")):
            # A CONFIG_KEY row (a configuration root's reads) is no site.
            if row["kind"] == "STATIC_SCOPE_SITE":
                self.sites[row["role"]].append(row)
        targets = self.sites["TARGET_SITE"]
        if len(targets) != 1:
            sys.exit("%s: %d TARGET_SITE rows" % (directory, len(targets)))
        self.target = targets[0]
        for branch in branches(self.target):
            fatal.update(self.operands.get(branch, ()))
        self.fatal = fatal
        self.writes = collections.defaultdict(list)  # field -> WRITE_SITE rows
        for row in self.sites["WRITE_SITE"]:
            for field in {row["cell"], row.get("carrier") or row["cell"]}:
                self.writes[field].append(row)
        self.doors = {method_of(row["siteId"]): row["siteId"]
                      for row in self.sites["DECLARED_SITE"]
                      if row.get("inputKind") == "FAULT"}
        self.frontier = list(rows(os.path.join(directory, "scope_frontier.jsonl")))
        self.attach = {}  # an IN port's attach cell (a formal's prefix) -> port
        for region in rows(os.path.join(directory, "region_skeletons.jsonl.gz")):
            for port in region.get("communicationPorts", []):
                if port.get("regionPortSide") != "IN":
                    continue
                if port.get("outputCaptureKind") == "CALL_RETURN":
                    cell = port.get("declaredCallee", "") + ".return"
                else:
                    cell = "%s.param%s:" % (port.get("definitionMethod", ""),
                                            port.get("argumentIndex", ""))
                self.attach[cell] = port["portId"]

    def closure(self, start):
        """cell -> (depth, mediated, control)."""
        reached = {}
        queue = collections.deque()

        def visit(cell, depth, mediated, control):
            if cell not in reached and depth <= DEPTH:
                reached[cell] = (depth, mediated, control)
                queue.append(cell)

        for cell in start:
            visit(cell, 0, False, False)
        while queue:
            cell = queue.popleft()
            depth, mediated, control = reached[cell]
            for edge in self.into.get(cell, ()):
                visit(edge["fromCell"], depth + 1,
                      mediated or is_field(cell) or edge["kind"] == "wire_handoff",
                      control)
            for write in self.writes.get(cell, ()):
                for branch in branches(write):
                    for operand in self.operands.get(branch, ()):
                        visit(operand, depth + 1, True, True)
        return reached

    def doors_called(self, method):
        """The doors <method> reaches within DOOR_CALLS calls."""
        seen, frontier = {method}, [method]
        for _ in range(DOOR_CALLS):
            frontier = [callee for caller in frontier
                        for callee in self.calls.get(caller, ())
                        if callee not in seen]
            seen.update(frontier)
        return [self.doors[m] for m in seen if m in self.doors]

    def roots(self, reached):
        """Every root the closure holds, one row each."""
        found = []

        def root(kind, site, state):
            found.append({"kind": kind, "site": site, "depth": state[0],
                          "mediated": state[1], "control": state[2]})

        for row in self.sites["DECLARED_SITE"]:
            state = reached.get(row.get("dependencyCell", ""))
            if row.get("inputKind") and state:
                root(row["inputKind"].lower(), row["siteId"], state)
        region = self.target.get("regionId", "")
        for field, writes in self.writes.items():
            state = reached.get(field)
            for write in writes if state else ():
                writer = write.get("regionId", "")
                if writer and writer != region:
                    root("crossRegion", field + " @" + writer,
                         (state[0], True, state[2]))
                for door in self.doors_called(method_of(write["siteId"])):
                    root("fault", door, (state[0] + 1, True, state[2]))
        delivered = {}  # port -> the state of its attach cell
        for cell, state in reached.items():
            port = self.port_of(cell)
            if port:
                delivered.setdefault(port, state)
            if cell in self.consumers or port:
                root("crossProcess", port or cell, (state[0], True, state[2]))
        for row in self.sites["EXPORT_SITE"]:
            state = delivered.get(row.get("portId"))
            for door in self.doors_called(method_of(row["siteId"])) if state else ():
                root("fault", door, (state[0] + 1, True, state[2]))
        return found

    def port_of(self, cell):
        """The IN port a cell attaches, if any: a formal's attach names its
        method and index, the edge set's cell adds `:<type>`."""
        if ".param" in cell:
            return self.attach.get(cell.rsplit(":", 1)[0] + ":")
        return self.attach.get(cell)

    def truncated(self, reached):
        for row in self.frontier:
            signature = row.get("signature", "")
            if row["kind"] == "CALLEE" and signature + ".return" in reached:
                return True
            if row["kind"] == "FORMAL" and any(
                    method_of(cell) == signature and ".param" in cell
                    for cell in reached):
                return True
            if row["kind"] == "FIELD" and signature in reached \
                    and not self.writes.get(signature):
                return True
        return False


def score(directory):
    piece = Slice(directory)
    reached = piece.closure(piece.fatal)
    roots = piece.roots(reached)
    names = collections.defaultdict(set)
    for row in roots:
        names[row["kind"]].add(row["site"])
    count = {kind: len(names[kind]) for kind in KINDS}
    cross = {site.split(" @")[0] for site in names["crossRegion"]}
    unrooted = sorted({row["siteId"] for row in piece.sites["READ_SITE"]
                       if row.get("cell") in reached and row["cell"] not in cross
                       and not piece.roots(piece.closure([row["cell"]]))})
    nearest = min((row["depth"] for row in roots), default=None)
    mediated = any(row["mediated"] for row in roots)
    value = (4 * bool(count["clock"]) + 4 * bool(count["fault"])
             + 3 * min(3, count["crossProcess"])
             + 2 * min(3, count["crossRegion"]) + count["read"]
             + 2 * mediated - (nearest or 0) / 8.0)
    result = dict(count)
    result.update({
        "keep": nearest is not None and nearest <= KEEP_DEPTH,
        "score": round(value, 3),
        "target": piece.target["siteId"],
        "fatalOperands": len(piece.fatal),
        "closure": len(reached),
        "control": sum(1 for state in reached.values() if state[2]),
        "nearestRootDepth": nearest,
        "mediated": mediated,
        "truncated": piece.truncated(reached),
        "roots": sorted(roots, key=lambda row: (row["kind"], row["site"],
                                                row["depth"])),
        "unrooted": unrooted,
    })
    return result


if __name__ == "__main__":
    directory = sys.argv[1]
    result = score(directory)
    path = os.path.join(directory, "score.json")
    with open(path + ".partial", "w") as out:
        json.dump(result, out, indent=1, sort_keys=True)
        out.write("\n")
    os.replace(path + ".partial", path)
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ("roots", "unrooted")}, sort_keys=True))

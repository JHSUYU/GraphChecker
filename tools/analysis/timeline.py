#!/usr/bin/env python3
"""timeline.py DIR... : where one campaign's wall time went, from its own files.

DIR is an accept directory (DIR/out/<case>/schedule), a case output directory
(DIR/schedule) or a campaign root (DIR/stage_metrics.tsv).  Nothing is re-run;
the sources are the files the campaign wrote:

  stage walls        schedule/stage_metrics.tsv (campaign_stage), a stage still
                     running from the log's last "[campaign] stage" line
  SEED split         .seed-started, the static artifacts' and runtime/'s mtimes,
                     the weave's "GraphChecker started/ran for" log lines
  EXPLORE per round  obligations-NNNN/: in_flight.jsonl (written as the planner
                     starts) to explore_manifest.json; the dispatch to
                     its last obligation's end (a GROW re-run's included)
  EXPLORE gates      landings/NNNN: the list of sessions one gate landed (written
                     as it starts) to its summary NNNN.json
  witness attempts   witness-attempts/NNNN/: the directory's creation to its
                     compose.log, and witness_attempts.jsonl's claims
  one obligation     host.txt (claimed) -> the solver's files -> replay.log
                     (the replay's end) -> stdout.log (the worker's end)
  a replay's outcome its obligation_result.jsonl: ADMITTED = flipped; NOT_ADMITTED
                     = refused, an error when the replay was killed on its bound
                     (a timed-out-sessions/ directory) or stated no verdict
  CONFIRM            final/confirm/worker/replay.log

It prints each campaign's stages, its planner rounds and replays, and its top
time sinks (the phases that took longest, the replays grouped by outcome).
"""
import calendar, glob, json, os, re, statistics, sys, time


def mtime(path):
    try:
        return os.stat(path).st_mtime
    except OSError:
        return None


def dur(seconds):
    if seconds is None:
        return "-"
    seconds = int(round(seconds))
    h, rest = divmod(seconds, 3600)
    m, s = divmod(rest, 60)
    return "%dh%02dm" % (h, m) if h else ("%dm%02ds" % (m, s) if m else "%ds" % s)


def clock(t):
    return time.strftime("%H:%M:%S", time.localtime(t)) if t else "-"


def read_json(path):
    try:
        with open(path, errors="replace") as handle:
            return json.loads(handle.read() or "null")
    except (OSError, ValueError):
        return None


def campaign_roots(arg):
    if os.path.isfile(os.path.join(arg, "stage_metrics.tsv")):
        return [arg]
    if os.path.isdir(os.path.join(arg, "schedule")):
        return [os.path.join(arg, "schedule")]
    return sorted(glob.glob(os.path.join(arg, "out", "*", "schedule")))


def stage_metrics(root):
    stages = []
    try:
        for line in open(os.path.join(root, "stage_metrics.tsv")):
            name, _, ms = line.rstrip("\n").partition("\t")
            if name and ms.isdigit() and "[" not in name:
                stages.append((name, int(ms) / 1000.0))
    except OSError:
        pass
    return stages


def campaign_log(root):
    """The campaign's log: <accept>/logs/<case>.log beside out/<case>/schedule."""
    case_dir = os.path.dirname(os.path.abspath(root))
    accept = os.path.dirname(os.path.dirname(case_dir))
    path = os.path.join(accept, "logs", os.path.basename(case_dir) + ".log")
    return path if os.path.isfile(path) else None


def seed_split(root, log_text):
    """SEED as static pass, weave, recording and aggregation, or None."""
    case_dir = os.path.dirname(os.path.abspath(root))
    start = mtime(os.path.join(root, ".seed-started"))
    static_end = mtime(os.path.join(case_dir, "static_scope_map.jsonl"))
    trace_end = mtime(os.path.join(case_dir, "runtime", "runtime_trace.jsonl"))
    plan_end = mtime(os.path.join(case_dir, "runtime", "concolic_region_plan.jsonl"))
    if None in (start, static_end, trace_end, plan_end):
        return None
    section = log_text.split("[campaign] stage SEED", 1)[-1].split("[campaign] stage PLAN", 1)[0]
    runs = re.findall(r"GraphChecker ran for (\d+) ms", section)
    weave = int(runs[-1]) / 1000.0 if len(runs) >= 2 else None
    split = [("static", static_end - start)]
    if weave is not None:
        split += [("weave", weave), ("recording", max(0.0, trace_end - static_end - weave))]
    else:
        split += [("weave+recording", trace_end - static_end)]
    split.append(("aggregation", plan_end - trace_end))
    return split


def worker_times(worker):
    """(start, solve_end, replay_end, end) of one obligation worker."""
    start = mtime(os.path.join(worker, "host.txt"))
    solver = [mtime(os.path.join(worker, name)) for name in
              ("obligation.jsonl", "obligation_query.smt2", "gaps.jsonl",
               "focused_task.jsonl", "schedule_prefix.jsonl", "schedule_suffix.jsonl")]
    solver = [t for t in solver if t]
    replay_end = mtime(os.path.join(worker, "replay.log"))
    end = mtime(os.path.join(worker, "stdout.log")) or replay_end
    return start, (max(solver) if solver else end), replay_end, end


def replay_outcome(worker, result):
    if os.path.isdir(os.path.join(worker, "timed-out-sessions")):
        return "error"
    verdict = (result or {}).get("verdict", "")
    if verdict == "ADMITTED":
        return "flipped"
    if verdict in ("NOT_ADMITTED", "UNSAT"):
        return "refused"
    return "error"


EARLY_END = re.compile(r"^Causynth (\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d)(\.\d+)?Z: the replay ends (AT_\w+)", re.M)


def early_end(worker, replay_end):
    """(reason, seconds from the end's line, a UTC instant, to the replay log's
    last write) when the replay ended early (ConcolicResultPublisher#conclude),
    else None."""
    try:
        text = open(os.path.join(worker, "replay.log"), errors="replace").read()
    except OSError:
        return None
    found = EARLY_END.search(text)
    if not found or not replay_end:
        return None
    said = calendar.timegm(time.strptime(found.group(1), "%Y-%m-%dT%H:%M:%S")) \
        + float(found.group(2) or 0)
    return found.group(3), replay_end - said


def round_rows(iteration):
    rows = []
    previous_end = mtime(os.path.join(iteration, "import_gate.json"))
    for wave in sorted(glob.glob(os.path.join(iteration, "obligations-[0-9]*"))):
        name = os.path.basename(wave)
        plan_start = mtime(os.path.join(wave, "in_flight.jsonl")) or previous_end
        plan_end = mtime(os.path.join(wave, "explore_manifest.json"))
        obligations = []
        for worker in sorted(glob.glob(os.path.join(wave, "*", ""))):
            worker = worker.rstrip("/")
            if not os.path.isfile(os.path.join(worker, "host.txt")):
                continue
            result = read_json(os.path.join(worker, "obligation_result.jsonl"))
            focused = os.path.join(worker, "focused_task.jsonl")
            replayed = os.path.isfile(focused) and os.path.getsize(focused) > 0
            start, solve_end, replay_end, end = worker_times(worker)
            try:
                failed = "obligation solver failed" in open(os.path.join(worker, "stdout.log"), errors="replace").read()
            except OSError:
                failed = False
            obligations.append({
                "id": os.path.basename(worker),
                "host": open(os.path.join(worker, "host.txt")).read().strip(),
                "verdict": (result or {}).get("verdict", "?"),
                "replayed": replayed,
                "solver_failed": failed,
                "outcome": replay_outcome(worker, result) if replayed else None,
                "early": early_end(worker, replay_end) if replayed else None,
                "solve": (solve_end - start) if start and solve_end else None,
                "replay": (replay_end - solve_end) if replayed and replay_end and solve_end else None,
                "wall": (end - start) if start and end else None,
                "rerun": bool(glob.glob(os.path.join(worker, "before-*"))),
            })
        ends = [t for t in (worker_times(os.path.join(wave, o["id"]))[3] for o in obligations) if t]
        dispatch_end = max(ends) if ends else plan_end
        rows.append({"wave": name[-4:], "plan": (plan_end - plan_start) if plan_start and plan_end else None,
                     "dispatch": (dispatch_end - plan_end) if plan_end and dispatch_end else None,
                     "obligations": obligations})
        previous_end = plan_end
    return rows


def landing_rows(iteration):
    """(seconds, sessions) of each gate that landed sessions."""
    rows = []
    for listed in sorted(glob.glob(os.path.join(iteration, "landings", "*.sessions"))):
        started = mtime(listed)
        ended = mtime(listed[:-len(".sessions")] + ".json")
        count = len([l for l in open(listed).read().splitlines() if l.strip()])
        rows.append(((ended - started) if started and ended else None, count))
    return rows


def attempt_rows(iteration):
    """(seconds, claim, accepted) of each COMPOSE attempt at a witness."""
    rows = []
    try:
        lines = open(os.path.join(iteration, "witness_attempts.jsonl")).read().splitlines()
    except OSError:
        return rows
    for line in lines:
        attempt = json.loads(line)
        started = mtime(attempt["dir"])
        ended = mtime(os.path.join(attempt["dir"], "compose.log"))
        rows.append(((ended - started) if started and ended else None,
                     "%s %s" % (attempt.get("claim") or "nothing", attempt.get("findingKind", "")),
                     attempt.get("accepted")))
    return rows


def spread(values):
    values = sorted(v for v in values if v is not None)
    if not values:
        return "-"
    return "%s/%s/%s" % (dur(values[0]), dur(statistics.median(values)), dur(values[-1]))


def report(root, label):
    log_path = campaign_log(root)
    log_text = open(log_path, errors="replace").read() if log_path else ""
    stages = stage_metrics(root)
    done = [name for name, _ in stages]
    running = re.findall(r"^\[campaign\] stage (\S+)", log_text, re.M)
    summary = {}
    summary_path = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(root)))), "summary.tsv")
    if os.path.isfile(summary_path):
        lines = [l.rstrip("\n").split("\t") for l in open(summary_path) if l.strip()]
        if len(lines) >= 2 and len(lines[0]) == len(lines[-1]) and lines[-1][0] != lines[0][0]:
            summary = dict(zip(lines[0], lines[-1]))
    running = running[-1] if running and running[-1] not in done and not summary else None
    seed_start = mtime(os.path.join(root, ".seed-started"))
    # The stages before SEED: all that finished, while SEED runs.
    before_seed = sum(w for n, w in stages[:done.index("SEED") if "SEED" in done else len(done)])
    at = (seed_start - before_seed) if seed_start else None
    # A campaign with no summary row is running or was stopped: its last
    # log line is the last thing it did.
    last = max([t for t in [mtime(log_path) if log_path else None, mtime(root)]
                + [mtime(p) for p in glob.glob(os.path.join(root, "iteration-0000", "*"))]
                if t] or [None])
    total = float(summary["elapsed"]) if summary.get("elapsed") else (
        last - at if last and at else sum(w for _, w in stages))
    print("== %s  %s" % (label, os.path.abspath(root)))
    print("   total %s%s%s" % (dur(total),
                              "  %s %s" % (summary.get("verdict", ""), summary.get("claim", "")) if summary else "",
                              "  (no summary: running or stopped in %s, last log line %s)" % (running, clock(last))
                              if running else ""))
    sinks = []
    for name, wall in stages:
        detail = ""
        if name == "SEED":
            split = seed_split(root, log_text)
            if split:
                detail = ", ".join("%s %s" % (part, dur(t)) for part, t in split)
                sinks += [("SEED " + part, t) for part, t in split]
        elif name == "REPLAY":
            detail = "the seed replay"
        if name not in ("SEED", "EXPLORE"):
            sinks.append((name, wall))
        print("   %-11s %s %9s  %s" % (name, clock(at), dur(wall), detail))
        at = at + wall if at else None
    if running:
        print("   %-11s %s %9s  (no end)" % (running, clock(at), dur(last - at if last and at else None)))
    iteration = os.path.join(root, "iteration-0000")
    waves = round_rows(iteration) if os.path.isdir(iteration) else []
    replays = [o for w in waves for o in w["obligations"] if o["replayed"]]
    if waves:
        print("   round plan     dispatch  oblig  UNSAT  NOT_ADM  solver-err  replays  replay min/med/max     refused/flipped/error  longest")
        for w in waves:
            obl = w["obligations"]
            rep = [o for o in obl if o["replayed"]]
            count = lambda key: sum(1 for o in rep if o["outcome"] == key)
            longest = max((o["wall"] or 0 for o in obl), default=0)
            print("   %-5s %-8s %-9s %-6d %-6d %-8d %-11d %-8d %-22s %-22s %s" % (
                w["wave"], dur(w["plan"]), dur(w["dispatch"]), len(obl),
                sum(1 for o in obl if o["verdict"] == "UNSAT" and not o["replayed"]),
                sum(1 for o in obl if o["verdict"] == "NOT_ADMITTED" and not o["replayed"]
                    and not o["solver_failed"]),
                sum(1 for o in obl if o["solver_failed"]), len(rep), spread(o["replay"] for o in rep),
                "%d/%d/%d" % (count("refused"), count("flipped"), count("error")), dur(longest)))
        solves = [o["solve"] for w in waves for o in w["obligations"]]
        failed = [o["solve"] or 0 for w in waves for o in w["obligations"] if o["solver_failed"]]
        print("   solver min/med/max %s, %s of slot time%s; replays %d, %s of slot time" % (
            spread(solves), dur(sum(s or 0 for s in solves)),
            " (%d failed JVMs: %s)" % (len(failed), dur(sum(failed))) if failed else "",
            len(replays), dur(sum(o["replay"] or 0 for o in replays))))
        for outcome in ("refused", "flipped", "error"):
            chosen = [o for o in replays if o["outcome"] == outcome]
            if not chosen:
                continue
            ended = {}
            for o in chosen:
                if o["early"]:
                    ended.setdefault(o["early"][0], []).append(o["early"][1])
            print("     %-8s %3d replays, %s of slot time%s" % (
                outcome, len(chosen), dur(sum(o["replay"] or 0 for o in chosen)),
                "".join("; %d ended %s (exit took %s)" % (len(v), k, spread(v))
                        for k, v in sorted(ended.items()))))
        reruns = sum(1 for w in waves for o in w["obligations"] if o["rerun"])
        if reruns:
            print("   GROW re-ran %d exposing replay(s)" % reruns)
        attempts = attempt_rows(iteration)
        if attempts:
            print("   witness attempts: " + "; ".join("%s %s%s" % (dur(t), claim, " (ended EXPLORE)" if accepted else "")
                                                   for t, claim, accepted in attempts))
        landings = landing_rows(iteration)
        if landings:
            print("   landings: %d gate(s) over %d session(s), %s each" % (
                len(landings), sum(n for _, n in landings), spread(t for t, _ in landings)))
        head = [("EXPLORE planning (%d rounds)" % len(waves), sum(w["plan"] or 0 for w in waves)),
                ("EXPLORE import gates", sum(t or 0 for t, _ in landings)),
                ("EXPLORE witness attempts", sum(t or 0 for t, _, _ in attempts))]
        explore = dict(stages).get("EXPLORE")
        if explore is not None:
            head.append(("EXPLORE waiting on the pool", explore - sum(t for _, t in head)))
        sinks += head
    confirm = os.path.join(root, "final", "confirm", "worker", "replay.log")
    if os.path.isfile(confirm):
        started = mtime(os.path.join(root, "final", "confirm", "worker", "focused_task.jsonl"))
        print("   CONFIRM replay %s" % dur(mtime(confirm) - started if started else None))
    waits = len(re.findall(r"^\[campaign\] waiting for memory on localhost", log_text, re.M))
    if waits:
        print("   the head waited for memory %d time(s) (inside the stage or gate that started the JVM)" % waits)
    sinks.sort(key=lambda s: -s[1])
    print("   top sinks: " + "; ".join("%s %s" % (name, dur(t)) for name, t in sinks[:5]))
    print()


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    for arg in sys.argv[1:]:
        roots = campaign_roots(arg)
        if not roots:
            print("== %s: no campaign root under it" % arg)
        for root in roots:
            report(root, os.path.basename(os.path.dirname(os.path.abspath(root))))


if __name__ == "__main__":
    main()

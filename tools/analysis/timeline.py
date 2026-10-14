#!/usr/bin/env python3
"""timeline.py DIR... : where one campaign's wall time went, from its own files.

DIR is an accept directory (DIR/out/<case>/schedule), a case output directory
(DIR/schedule) or a campaign root (DIR/stage_metrics.tsv).  Nothing is re-run;
the sources are the files the campaign wrote:

  stage walls        schedule/stage_metrics.tsv (campaign_stage), a stage still
                     running from the log's last "[campaign] stage" line
  SEED split         .seed-started, the static artifacts' and runtime/'s mtimes,
                     the weave's "GraphChecker started/ran for" log lines
  EXPLORE per round  obligations-NNNN/: in_flight.jsonl (copied as the planner
                     starts) to explore_manifest.json; the dispatch to
                     its last obligation's answer (a GROW re-run's included);
                     its obligations' wait for a start, from the round's
                     obligations.jsonl to each one's start; the planner's
                     wait for memory, off its stderr.log
                     (campaign_head_place: "waiting for memory for a head
                     step", then "room ... after waiting <s> s")
  EXPLORE head steps steps/NNNN/: its inputs (gate, witnesses, confirms;
                     written as it starts) to its last output -- the gate's
                     import_gate.json, an attempt's compose.log; one step
                     runs at a time, beside the pool and the round planning
                     (an attempt's confirmation replay is a job of the pool,
                     witness-confirm/NNNN/)
  witness attempts   witness_attempts.jsonl: its step's witnesses (written as
                     the step starts) to its compose.log, and its claim
  one obligation     obligations-NNNN/<id>/ with an obligation_result.jsonl:
                     host.txt (its solve started; in a run pruned before
                     host.txt was kept, its logs' earliest last write) ->
                     the solver's files (a solve asked again in a solver JVM
                     of its own: alone-host.txt, an ALONE start; hard-host.txt,
                     the hard lane's) ->
                     replay-host.txt (its REPLAY started, a start of its own;
                     replay-stderr.log when pruned; a run before the split
                     replayed as its solve ended) -> replay.log (the replay's
                     end) -> obligation_result.jsonl (its answer)
  a replay's outcome its obligation_result.jsonl: ADMITTED = flipped; NOT_ADMITTED
                     = refused, an error when the replay was killed on its bound
                     (a timed-out-sessions/ directory) or stated no verdict
  CONFIRM            every confirmation replay's worker/replay.log: the final
                     claim's (final/confirm/), the refuted ones' before it
                     (final/refuted/NNNN/confirm/) and the witness attempts'
                     (witness-confirm/NNNN/)
  COMPOSE split      final/compose.log: ComposeMain's composeSeconds= (corpus read and
                     lowering) and solveSeconds= (SOLVE and DECIDE)

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
    """(start, solve_end, replay_start, replay_end, end) of one obligation
    worker (the docstring's "one obligation"); None where it states none."""
    def first(*names):
        for name in names:
            stamp = mtime(os.path.join(worker, name))
            if stamp:
                return stamp
        return None
    replay_start = first("replay-host.txt", "replay-stderr.log")
    replay_end = mtime(os.path.join(worker, "replay.log"))
    end = mtime(os.path.join(worker, "obligation_result.jsonl"))
    # A run pruned before host.txt was kept states its logs' last writes
    # only: the earliest of them, never past its answer, is the nearest.
    start = mtime(os.path.join(worker, "host.txt")) or min(
        [t for t in (mtime(os.path.join(worker, "stderr.log")),
                     mtime(os.path.join(worker, "stdout.log")), end) if t] or [None])
    solver = [t for t in (mtime(os.path.join(worker, name)) for name in
              ("obligation.jsonl", "obligation_query.smt2", "gaps.jsonl",
               "focused_task.jsonl", "schedule_prefix.jsonl", "schedule_suffix.jsonl"))
              if t]
    solve_end = max(solver) if solver else (replay_start if replay_end else end)
    return start, solve_end, replay_start, replay_end, end


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


COMPOSE_SPLIT = re.compile(r"composeSeconds=(\d+) solveSeconds=(\d+)")


def compose_split(log):
    """(lowering, solving) seconds of one COMPOSE, off ComposeMain's summary line, or None."""
    try:
        found = COMPOSE_SPLIT.search(open(log, errors="replace").read())
    except OSError:
        return None
    return (int(found.group(1)), int(found.group(2))) if found else None


HEAD_WAIT = re.compile(r"^\[campaign\] waiting for memory for a head step", re.M)
HEAD_ROOM = re.compile(r"^\[campaign\] room for a head step of \d+ MB on \S+ after waiting (\d+) s", re.M)


def head_wait(log):
    """None when the head step whose stderr <log> is never waited for memory;
    else the seconds it waited, or -1 when the run did not state how long."""
    try:
        text = open(log, errors="replace").read()
    except OSError:
        return None
    if not HEAD_WAIT.search(text):
        return None
    waited = HEAD_ROOM.findall(text)
    return sum(int(s) for s in waited) if waited else -1


SOLVER_FAILED = "its host's solver did not answer"


def round_rows(iteration):
    rows = []
    for wave in sorted(glob.glob(os.path.join(iteration, "obligations-[0-9]*"))):
        name = os.path.basename(wave)
        stderr = os.path.join(wave, "stderr.log")
        plan_start = mtime(os.path.join(wave, "in_flight.jsonl"))
        plan_end = mtime(os.path.join(wave, "explore_manifest.json"))
        queued = mtime(os.path.join(wave, "obligations.jsonl"))
        obligations = []
        for worker in sorted(glob.glob(os.path.join(wave, "*", ""))):
            worker = worker.rstrip("/")
            result = read_json(os.path.join(worker, "obligation_result.jsonl"))
            if result is None:
                continue
            start, solve_end, replay_start, replay_end, end = worker_times(worker)
            replayed = replay_end is not None
            said = ""
            for log in ("stdout.log", "stderr.log", "alone-stdout.log",
                        "alone-stderr.log", "hard-stdout.log", "hard-stderr.log"):
                try:
                    said += open(os.path.join(worker, log), errors="replace").read()
                except OSError:
                    pass
            try:
                host = open(os.path.join(worker, "host.txt")).read().strip()
            except OSError:
                host = "-"
            obligations.append({
                "id": os.path.basename(worker),
                "host": host,
                "verdict": result.get("verdict", "?"),
                "replayed": replayed,
                "solver_failed": SOLVER_FAILED in said,
                "outcome": replay_outcome(worker, result) if replayed else None,
                "early": early_end(worker, replay_end) if replayed else None,
                "waited": (start - queued) if start and queued else None,
                "solve": (solve_end - start) if start and solve_end else None,
                "queued": (replay_start - solve_end) if replay_start and solve_end else None,
                "replay": (replay_end - (replay_start or solve_end or start))
                          if replayed and (replay_start or solve_end or start) else None,
                "wall": (end - start) if start and end else None,
                "end": end,
                "rerun": bool(glob.glob(os.path.join(worker, "before-*"))),
                "alone": os.path.exists(os.path.join(worker, "alone-host.txt")),
                "hard": os.path.exists(os.path.join(worker, "hard-host.txt")),
            })
        ends = [o["end"] for o in obligations if o["end"]]
        dispatch_end = max(ends) if ends else plan_end
        rows.append({"wave": name[-4:], "plan": (plan_end - plan_start) if plan_start and plan_end else None,
                     "wait": head_wait(stderr),
                     "dispatch": (dispatch_end - plan_end) if plan_end and dispatch_end else None,
                     "obligations": obligations})
    return rows


def step_rows(iteration):
    """Each head step: (its seconds, its gate's seconds, the sessions it gated)."""
    attempts = {}
    try:
        for line in open(os.path.join(iteration, "witness_attempts.jsonl")).read().splitlines():
            attempt = json.loads(line)
            attempts.setdefault(attempt.get("step"), []).append(os.path.join(attempt["dir"], "compose.log"))
    except OSError:
        pass
    rows = []
    for step in sorted(glob.glob(os.path.join(iteration, "steps", "[0-9]*"))):
        started = min([t for t in (mtime(os.path.join(step, n))
                                   for n in ("gate", "witnesses", "confirms")) if t]
                      or [None])
        gate = os.path.join(step, "gate")
        gated = mtime(os.path.join(step, "import_gate.json"))
        outputs = [gated] + [mtime(p) for p in attempts.get(os.path.basename(step), [])]
        ended = max([t for t in outputs if t] or [None])
        count = len([l for l in open(gate).read().splitlines() if l.strip()]) if os.path.isfile(gate) else 0
        rows.append(((ended - started) if started and ended else None,
                     (gated - started) if started and gated else None, count))
    return rows


def attempt_rows(iteration):
    """(seconds, claim, accepted) of each COMPOSE attempt at a witness: from
    its step's start (steps/NNNN/witnesses) to its compose.log."""
    rows = []
    try:
        lines = open(os.path.join(iteration, "witness_attempts.jsonl")).read().splitlines()
    except OSError:
        return rows
    for line in lines:
        attempt = json.loads(line)
        started = mtime(os.path.join(iteration, "steps", attempt.get("step", ""), "witnesses"))
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
        elif name == "COMPOSE":
            split = compose_split(os.path.join(root, "final", "compose.log"))
            if split:
                detail = "lowering %s, solving %s" % (dur(split[0]), dur(split[1]))
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
        print("   round plan     dispatch  oblig  waited min/med/max     UNSAT  NOT_ADM  solver-err  replays  replay min/med/max     refused/flipped/error  longest")
        for w in waves:
            obl = w["obligations"]
            rep = [o for o in obl if o["replayed"]]
            count = lambda key: sum(1 for o in rep if o["outcome"] == key)
            longest = max((o["wall"] or 0 for o in obl), default=0)
            print("   %-5s %-8s %-9s %-6d %-22s %-6d %-8d %-11d %-8d %-22s %-22s %s" % (
                w["wave"], dur(w["plan"]), dur(w["dispatch"]), len(obl),
                spread(o["waited"] for o in obl),
                sum(1 for o in obl if o["verdict"] == "UNSAT" and not o["replayed"]),
                sum(1 for o in obl if o["verdict"] == "NOT_ADMITTED" and not o["replayed"]
                    and not o["solver_failed"]),
                sum(1 for o in obl if o["solver_failed"]), len(rep), spread(o["replay"] for o in rep),
                "%d/%d/%d" % (count("refused"), count("flipped"), count("error")), dur(longest)))
        for w in waves:
            if w["wait"] is not None:
                print("   round %s's planner waited for memory %s of its %s" % (
                    w["wave"], dur(w["wait"]) if w["wait"] >= 0 else "(how long: not stated by this run)",
                    dur(w["plan"])))
        solves = [o["solve"] for w in waves for o in w["obligations"]]
        failed = [o["solve"] or 0 for w in waves for o in w["obligations"] if o["solver_failed"]]
        queued = [o["queued"] for o in replays if o["queued"] is not None]
        print("   solver min/med/max %s, %s of slot time%s; replays %d, %s of slot time%s" % (
            spread(solves), dur(sum(s or 0 for s in solves)),
            " (%d failed JVMs: %s)" % (len(failed), dur(sum(failed))) if failed else "",
            len(replays), dur(sum(o["replay"] or 0 for o in replays)),
            ", queued after their solve min/med/max %s" % spread(queued) if queued else ""))
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
        alone = sum(1 for w in waves for o in w["obligations"] if o["alone"])
        hard = sum(1 for w in waves for o in w["obligations"] if o["hard"])
        if alone or hard:
            print("   solves asked again in a solver JVM of their own: %d ALONE, %d HARD"
                  % (alone, hard))
        attempts = attempt_rows(iteration)
        if attempts:
            print("   witness attempts: " + "; ".join("%s %s%s" % (dur(t), claim, " (ended EXPLORE)" if accepted else "")
                                                   for t, claim, accepted in attempts))
        steps = step_rows(iteration)
        gates = [(g, n) for _, g, n in steps if n]
        if steps:
            print("   head steps: %d, %s each; %d gate(s) over %d session(s), %s each" % (
                len(steps), spread(t for t, _, _ in steps), len(gates), sum(n for _, n in gates),
                spread(g for g, _ in gates)))
        planner_waits = sum(max(w["wait"] or 0, 0) for w in waves)
        head = [("EXPLORE planning (%d rounds)" % len(waves), sum(w["plan"] or 0 for w in waves) - planner_waits),
                ("EXPLORE planners waiting for memory", planner_waits),
                ("EXPLORE import gates", sum(g or 0 for g, _ in gates)),
                ("EXPLORE witness attempts", sum(t or 0 for t, _, _ in attempts))]
        # The head's JVM time: its steps, which run beside the pool.
        busy = sum(t or 0 for t, _, _ in steps)
        explore = dict(stages).get("EXPLORE")
        if explore is not None:
            head.append(("EXPLORE with no head JVM running", explore - busy))
        sinks += head
    for confirm in sorted(glob.glob(os.path.join(root, "final", "confirm", "worker", "replay.log"))
                          + glob.glob(os.path.join(root, "final", "refuted", "*", "confirm", "worker",
                                                   "replay.log"))
                          + glob.glob(os.path.join(root, "witness-confirm", "*", "worker", "replay.log"))):
        worker = os.path.dirname(confirm)
        started = mtime(os.path.join(worker, "focused_task.jsonl"))
        print("   CONFIRM replay %s (%s)" % (dur(mtime(confirm) - started if started else None),
                                         os.path.relpath(worker, root)))
    waits = len(HEAD_WAIT.findall(log_text)) + sum(1 for w in waves if w["wait"] is not None)
    if waits:
        stated = sum(int(s) for s in HEAD_ROOM.findall(log_text)) + sum(max(w["wait"] or 0, 0) for w in waves)
        print("   the head waited for memory %d time(s), %s stated (inside the stage or gate that started the JVM)"
              % (waits, dur(stated)))
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

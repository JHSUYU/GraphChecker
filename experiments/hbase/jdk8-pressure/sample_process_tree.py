#!/usr/bin/env python3
"""Sample a campaign launcher and all of its JVM descendants once per second.

The process tree is identified by Linux PID plus /proc start time, so PID reuse
cannot attach an unrelated process. Previously observed children remain tracked
if their parent exits and Linux reparents them before the next sample.
"""

import argparse
import csv
import datetime
import json
import os
import signal
import time
from pathlib import Path


STOP = False


def request_stop(_signal, _frame):
    global STOP
    STOP = True


def processes():
    """Return pid -> (ppid, start_ticks) for live, non-zombie processes."""
    result = {}
    for proc in Path("/proc").iterdir():
        if not proc.name.isdigit():
            continue
        try:
            stat = (proc / "stat").read_text()
            # The parenthesized command may itself contain spaces or ')'.
            fields = stat[stat.rfind(")") + 2:].split()
            if fields[0] in ("Z", "X"):
                continue
            result[int(proc.name)] = (int(fields[1]), int(fields[19]))
        except (OSError, IndexError, ValueError):
            # Processes can exit at any point in a /proc scan.
            continue
    return result


def tree_members(rows, root_pid, root_birth, known):
    """Find current descendants plus previously observed, reparented children."""
    active = {}
    root = rows.get(root_pid)
    if root is not None and root[1] == root_birth:
        active[root_pid] = root_birth
    for pid, birth in known.items():
        row = rows.get(pid)
        if row is not None and row[1] == birth:
            active[pid] = birth

    # New descendants may be multiple generations deep. Walk the parent graph
    # until no more descendants are found, retaining start times for next time.
    changed = True
    while changed:
        changed = False
        for pid, (ppid, birth) in rows.items():
            if pid not in active and ppid in active:
                active[pid] = birth
                changed = True
    return active


def process_usage(pid, expected_birth):
    proc = Path("/proc") / str(pid)
    try:
        status = (proc / "status").read_text()
        values = {}
        for line in status.splitlines():
            if line.startswith(("VmRSS:", "Threads:")):
                key, value = line.split(":", 1)
                values[key] = int(value.strip().split()[0])
        exe = os.readlink(str(proc / "exe"))
        stat = (proc / "stat").read_text()
        fields = stat[stat.rfind(")") + 2:].split()
        if int(fields[19]) != expected_birth or fields[0] in ("Z", "X"):
            return None
        if exe.endswith(" (deleted)"):
            exe = exe[:-10]
        is_java = Path(exe).name == "java"
        return (values.get("VmRSS", 0), values.get("Threads", 0), is_java)
    except (OSError, IndexError, ValueError):
        return None


def host_memory():
    values = {}
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith(("MemAvailable:", "SwapTotal:", "SwapFree:")):
            key, value = line.split(":", 1)
            values[key] = int(value.strip().split()[0])
    return values["MemAvailable"], values["SwapTotal"] - values["SwapFree"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root-pid", type=int, required=True,
                        help="PID of a campaign launcher that is already running")
    parser.add_argument("--output", type=Path, required=True, help="CSV sample path")
    parser.add_argument("--summary", type=Path,
                        help="JSON summary path (default: <output>.summary.json)")
    parser.add_argument("--interval", type=float, default=1.0,
                        help="sample period in seconds (default: 1)")
    parser.add_argument("--max-samples", type=int, default=0,
                        help="optional sample cap; zero means until tree exits")
    args = parser.parse_args()
    if args.root_pid <= 0 or args.interval <= 0 or args.max_samples < 0:
        parser.error("root PID and interval must be positive; max-samples must be nonnegative")
    summary_path = args.summary or Path(str(args.output) + ".summary.json")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    summary_path.parent.mkdir(parents=True, exist_ok=True)
    signal.signal(signal.SIGTERM, request_stop)
    signal.signal(signal.SIGINT, request_stop)

    initial_rows = processes()
    root_birth = initial_rows.get(args.root_pid, (None, None))[1]
    known = {}
    start = time.monotonic()
    start_utc = datetime.datetime.now(datetime.timezone.utc).isoformat()
    summary = {
        "root_pid": args.root_pid,
        "root_start_ticks": root_birth,
        "start_utc": start_utc,
        "sample_count": 0,
        "peak_java_processes": 0,
        "peak_java_rss_kib": 0,
        "peak_java_threads": 0,
        "peak_tree_rss_kib": 0,
        "minimum_mem_available_kib": None,
        "initial_swap_used_kib": None,
        "peak_swap_used_kib": 0,
        "final_swap_used_kib": 0,
    }
    with args.output.open("w", newline="") as output:
        writer = csv.writer(output)
        writer.writerow(("utc", "elapsed_s", "root_pid", "tree_processes",
                         "java_processes", "java_pids", "java_rss_kib",
                         "java_threads", "tree_rss_kib", "mem_available_kib",
                         "swap_used_kib"))
        while not STOP:
            tick = time.monotonic()
            rows = processes()
            active = tree_members(rows, args.root_pid, root_birth, known)
            known = active
            java_pids = []
            java_rss = java_threads = tree_rss = live_processes = 0
            for pid, birth in sorted(active.items()):
                usage = process_usage(pid, birth)
                if usage is None:
                    continue
                rss, threads, is_java = usage
                live_processes += 1
                tree_rss += rss
                if is_java:
                    java_pids.append(pid)
                    java_rss += rss
                    java_threads += threads
            available, swap = host_memory()
            writer.writerow((datetime.datetime.now(datetime.timezone.utc).isoformat(),
                             round(tick - start, 3), args.root_pid,
                             live_processes, len(java_pids), ";".join(map(str, java_pids)),
                             java_rss, java_threads, tree_rss, available, swap))
            output.flush()

            summary["sample_count"] += 1
            summary["peak_java_processes"] = max(summary["peak_java_processes"], len(java_pids))
            summary["peak_java_rss_kib"] = max(summary["peak_java_rss_kib"], java_rss)
            summary["peak_java_threads"] = max(summary["peak_java_threads"], java_threads)
            summary["peak_tree_rss_kib"] = max(summary["peak_tree_rss_kib"], tree_rss)
            previous_min = summary["minimum_mem_available_kib"]
            summary["minimum_mem_available_kib"] = available if previous_min is None else min(previous_min, available)
            if summary["initial_swap_used_kib"] is None:
                summary["initial_swap_used_kib"] = swap
            summary["peak_swap_used_kib"] = max(summary["peak_swap_used_kib"], swap)
            summary["final_swap_used_kib"] = swap
            if not active or (args.max_samples and summary["sample_count"] >= args.max_samples):
                break
            time.sleep(max(0, args.interval - (time.monotonic() - tick)))

    summary["end_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    summary["elapsed_s"] = round(time.monotonic() - start, 3)
    summary["peak_swap_growth_kib"] = max(0, summary["peak_swap_used_kib"] - (summary["initial_swap_used_kib"] or 0))
    summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Sample one launched JVM and host memory without adding load to the JVM."""

import argparse
import csv
import datetime
import os
import signal
import time
from pathlib import Path


running = True


def stop(_signum, _frame):
    global running
    running = False


def proc_rows():
    rows = {}
    for proc in Path("/proc").iterdir():
        if not proc.name.isdigit():
            continue
        try:
            status = (proc / "status").read_text()
            values = {}
            for line in status.splitlines():
                if line.startswith(("PPid:", "VmRSS:", "Threads:")):
                    key, value = line.split(":", 1)
                    values[key] = int(value.strip().split()[0])
            executable = (proc / "exe").resolve()
            rows[int(proc.name)] = (values, executable.name)
        except (FileNotFoundError, PermissionError, ProcessLookupError):
            continue
    return rows


def descendant(pid, root, rows):
    seen = set()
    while pid != root and pid not in seen:
        seen.add(pid)
        row = rows.get(pid)
        if row is None:
            return False
        pid = row[0].get("PPid", 0)
    return pid == root


def memory():
    data = {}
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith(("MemAvailable:", "SwapTotal:", "SwapFree:")):
            key, value = line.split(":", 1)
            data[key] = int(value.strip().split()[0])
    return (data.get("MemAvailable", 0),
            data.get("SwapTotal", 0) - data.get("SwapFree", 0))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root-pid", type=int, required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    signal.signal(signal.SIGTERM, stop)
    start = time.monotonic()
    with open(args.output, "w", newline="") as output:
        writer = csv.writer(output)
        writer.writerow(("utc", "elapsed_s", "jvm_pid", "jvm_rss_kib",
                         "jvm_threads", "mem_available_kib", "swap_used_kib"))
        while running:
            rows = proc_rows()
            matches = [(pid, values) for pid, (values, executable) in rows.items()
                       if executable == "java"
                       and descendant(pid, args.root_pid, rows)]
            matches.sort()
            pid, values = matches[0] if matches else ("", {})
            available, swap = memory()
            writer.writerow((datetime.datetime.now(datetime.timezone.utc).isoformat(),
                             round(time.monotonic() - start, 3), pid,
                             values.get("VmRSS", ""), values.get("Threads", ""),
                             available, swap))
            output.flush()
            if args.root_pid not in rows:
                break
            time.sleep(1)


if __name__ == "__main__":
    main()

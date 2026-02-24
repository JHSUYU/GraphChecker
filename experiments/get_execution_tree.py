#!/usr/bin/env python3
"""
Trace Tree Builder
Fetch /opt/trace.txt from multiple servers, parse SPAN_RELATION lines, build call trees and display via DFS
"""

import subprocess
from collections import defaultdict
from dataclasses import dataclass
from typing import Dict, List, Optional, Set

# Configuration
SERVERS = ["node0", "node1", "node2"]
TRACE_FILE = "/opt/pilottrace.txt"

# Filter: only this trace_id will be processed
PILOT_TRACE_ID = "6617d8ae962ce21488ca1c968e2bd3fd"

# Method display limits (method name -> max count)
METHOD_LIMITS = {
    "httpservletrequest": 10,
    "root": 1,
}


@dataclass
class SpanNode:
    span_id: str
    host: str
    thread_id: int
    timestamp: int
    method: str
    children: List['SpanNode'] = None

    def __post_init__(self):
        if self.children is None:
            self.children = []


def fetch_trace_from_server(server: str) -> List[str]:
    """Fetch trace.txt content from server via SSH"""
    try:
        result = subprocess.run(
            ["ssh", "-o", "StrictHostKeyChecking=no", "-o", "ConnectTimeout=5",
             server, f"cat {TRACE_FILE} 2>/dev/null || echo ''"],
            capture_output=True,
            text=True,
            timeout=10
        )
        lines = result.stdout.strip().split('\n')
        return [l for l in lines if l.strip()]
    except Exception:
        return []


def parse_line(line: str, target_trace_id: str = None) -> Optional[dict]:
    """Parse SPAN_RELATION line"""
    parts = line.strip().split('|')
    if len(parts) < 9 or parts[1] != "SPAN_RELATION":
        return None

    trace_id = parts[0]
    if target_trace_id and trace_id != target_trace_id:
        return None

    try:
        return {
            'trace_id': trace_id,
            'parent_span_id': parts[2],
            'child_span_id': parts[3],
            'method': parts[4],
            'host': parts[5],
            'thread_name': parts[6],
            'thread_id': int(parts[7]),
            'timestamp': int(parts[8])
        }
    except (ValueError, IndexError):
        return None


def count_subtree_size(node: SpanNode) -> int:
    """Count total nodes in subtree"""
    if not node:
        return 0
    count = 0
    stack = [node]
    while stack:
        n = stack.pop()
        count += 1
        stack.extend(n.children)
    return count


def build_trees(records: List[dict]) -> List[SpanNode]:
    """Build call trees, returns list of all root nodes"""
    by_trace: Dict[str, List[dict]] = defaultdict(list)
    for r in records:
        by_trace[r['trace_id']].append(r)

    all_roots = []

    for trace_id, trace_records in by_trace.items():
        trace_records_sorted = sorted(trace_records, key=lambda r: (r['timestamp'], r['child_span_id']))

        nodes: Dict[str, SpanNode] = {}
        parent_map: Dict[str, str] = {}

        # First pass: create all child nodes
        for r in trace_records_sorted:
            child_id = r['child_span_id']
            parent_id = r['parent_span_id']

            if child_id not in nodes:
                nodes[child_id] = SpanNode(
                    span_id=child_id,
                    host=r['host'],
                    thread_id=r['thread_id'],
                    timestamp=r['timestamp'],
                    method=r['method']
                )

            parent_map[child_id] = parent_id

        # Second pass: create parent nodes only if they don't exist as children
        for r in trace_records_sorted:
            parent_id = r['parent_span_id']
            if parent_id and parent_id not in nodes:
                nodes[parent_id] = SpanNode(
                    span_id=parent_id,
                    host="pilotexecution",
                    thread_id=0,
                    timestamp=0,
                    method=f"PARENT_{parent_id[:8]}"
                )

        # Build parent-child relationships
        for child_id in sorted(parent_map.keys()):
            parent_id = parent_map[child_id]
            if parent_id and parent_id in nodes:
                nodes[parent_id].children.append(nodes[child_id])

        for node in nodes.values():
            node.children.sort(key=lambda n: (n.timestamp, n.span_id))

        # Find all root nodes
        child_ids = set(parent_map.keys())
        parent_ids = set(parent_map.values())
        root_ids = parent_ids - child_ids

        for root_id in root_ids:
            if root_id in nodes:
                all_roots.append(nodes[root_id])

    return all_roots


def find_largest_tree(roots: List[SpanNode]) -> tuple:
    """Find the tree with the most nodes"""
    if not roots:
        return None, 0

    largest_root = None
    largest_size = 0

    for root in roots:
        size = count_subtree_size(root)
        if size > largest_size or (size == largest_size and largest_root and root.span_id < largest_root.span_id):
            largest_size = size
            largest_root = root

    return largest_root, largest_size


def select_nodes_with_limits(root: SpanNode, max_nodes: int, method_limits: Dict[str, int] = None) -> Set[str]:
    """Select nodes respecting method limits"""
    if not root:
        return set()

    if method_limits is None:
        method_limits = {}

    all_nodes: Dict[str, SpanNode] = {}

    def collect_all_nodes(node: SpanNode):
        if node:
            all_nodes[node.span_id] = node
            for child in node.children:
                collect_all_nodes(child)

    collect_all_nodes(root)

    method_counts: Dict[str, int] = defaultdict(int)

    def get_short_method(node: SpanNode) -> str:
        return node.method.split('.')[-1] if '.' in node.method else node.method

    def matches_limited_method(short_method: str) -> Optional[str]:
        short_method_lower = short_method.lower()
        for limited_method in method_limits.keys():
            if limited_method in short_method_lower or short_method_lower in limited_method:
                return limited_method
        return None

    def is_method_limit_exceeded(node: SpanNode) -> bool:
        short_method = get_short_method(node)
        matched = matches_limited_method(short_method)
        if matched and method_counts[matched] >= method_limits[matched]:
            return True
        return False

    def update_method_count(node: SpanNode):
        short_method = get_short_method(node)
        matched = matches_limited_method(short_method)
        if matched:
            method_counts[matched] += 1

    selected_span_ids: Set[str] = set()
    sorted_nodes = sorted(all_nodes.values(), key=lambda n: (n.timestamp, n.span_id))

    # Always include root first
    selected_span_ids.add(root.span_id)
    update_method_count(root)

    for node in sorted_nodes:
        if len(selected_span_ids) >= max_nodes:
            break
        if node.span_id in selected_span_ids:
            continue
        if is_method_limit_exceeded(node):
            continue
        selected_span_ids.add(node.span_id)
        update_method_count(node)

    return selected_span_ids


def print_tree(node: SpanNode, selected_nodes: Set[str], prefix: str = "", is_last: bool = True, is_root: bool = False):
    """DFS traversal and print tree"""
    if not node or node.span_id not in selected_nodes:
        return

    if prefix == "" and is_last:
        branch = ""
    else:
        branch = "└── " if is_last else "├── "

    short_method = node.method.split('.')[-1] if '.' in node.method else node.method
    if is_root and short_method.startswith("PARENT_"):
        short_method = "ROOT"
    short_host = node.host.split('.')[0] if '.' in node.host else node.host

    print(f"{prefix}{branch}[{short_host}] {short_method} (tid={node.thread_id}, ts={node.timestamp})")

    if prefix == "" and branch == "":
        new_prefix = ""
    else:
        new_prefix = prefix + ("    " if is_last else "│   ")

    def get_selected_descendants(n: SpanNode) -> List[SpanNode]:
        result = []
        for child in n.children:
            if child.span_id in selected_nodes:
                result.append(child)
            else:
                result.extend(get_selected_descendants(child))
        return result

    visible_children = get_selected_descendants(node)

    def count_all_descendants(n: SpanNode) -> int:
        count = len(n.children)
        for child in n.children:
            count += count_all_descendants(child)
        return count

    def count_selected_descendants(n: SpanNode) -> int:
        count = 0
        for child in n.children:
            if child.span_id in selected_nodes:
                count += 1
            count += count_selected_descendants(child)
        return count

    total_descendants = count_all_descendants(node)
    selected_descendant_count = count_selected_descendants(node)
    hidden_count = total_descendants - selected_descendant_count

    for i, child in enumerate(visible_children):
        is_last_item = (i == len(visible_children) - 1) and hidden_count == 0
        print_tree(child, selected_nodes, new_prefix, is_last_item, is_root=False)

    if hidden_count > 0:
        print(f"{new_prefix}└── [...{hidden_count} more descendants hidden]")


def main():
    all_lines = []

    for server in SERVERS:
        lines = fetch_trace_from_server(server)
        if lines:
            all_lines.extend(lines)

    if not all_lines:
        return

    records = []
    for line in all_lines:
        parsed = parse_line(line, target_trace_id=PILOT_TRACE_ID)
        if parsed:
            records.append(parsed)

    if not records:
        return

    all_roots = build_trees(records)

    if not all_roots:
        return

    largest_root, largest_size = find_largest_tree(all_roots)

    if not largest_root:
        return

    max_display_nodes = 50

    selected = select_nodes_with_limits(largest_root, max_display_nodes, METHOD_LIMITS)

    print(f"Tree size: {largest_size}, Displaying: {len(selected)} nodes")
    print_tree(largest_root, selected, is_root=True)


if __name__ == "__main__":
    main()
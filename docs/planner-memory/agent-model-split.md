---
name: agent-model-split
description: User wants the main agent (Fable 5.1) to only plan/delegate; all concrete code reading and writing goes to Opus 5 subagents
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 99c84a54-86ac-44a4-a030-760f664ae2a1
  modified: 2026-09-12T03:11:46.750Z
---

Only the main agent runs on Fable 5.1. All concrete code reading, code writing, and test execution must be delegated to subagents with `model: "opus"`. The main agent acts as designer and requirement owner: it plans, writes precise implementation specs for subagents, and verifies their reports.

**Why:** The user stated this explicitly on 2026-09-11 when setting the GraphChecker refactor goal ("只有你的主agent能用fable5.1... 具体的代码阅读，写都用opus5. 你是设计者和需求委托者").

**How to apply:** Before reading or editing source in /opt/GraphChecker, spawn an Agent with `model: "opus"` and give it concrete file paths, acceptance criteria, and what to report back. Light orientation (ls, git log, file sizes) by the main agent is acceptable; deep reading is not. See [[graphchecker-refactor-goal]].

**Temporary relaxation (2026-09-13 00:15):** user said "我允许你现在暂时全部用fable5.1来做" — for now subagents may run on Fable 5.1 too (omit `model: "opus"` / use default or fork). Revert to the Opus-only rule when the user says so.

**Relaxation ended (2026-09-13 07:50):** user: "继续使用fable5.1作为主agent, opus5作为子agent. 分工和之前一样" — back to Opus-only subagents (`model: "opus"`).

**Owner (2026-09-13 15:00): "你不用这么频繁测17960。代码先写完然后再跑"** — do not run a campaign after every chunk; finish the code of a simplification round, validate offline (unit tests, re-driving stages over existing corpora), then run ONE campaign per case at the end.

**Effort (learned 2026-09-13 17:50):** the Agent tool has no effort parameter; `subagent_type: general-purpose` with `model: opus` runs at the default effort. A custom agent definition sets it: `/opt/GraphChecker/.claude/agents/opus-impl.md` (frontmatter `model: opus`, `effort: xhigh` (owner: "opus5你开到xhigh就行")). Use `subagent_type: "opus-impl"` for all new implementation agents.

**Owner (2026-09-14 22:40, takeover session):** subagents are the `opus-impl` agent type (`.claude/agents/opus-impl.md`: Opus 5, effort xhigh). The planner writes no code itself; "写代码具体都是子agent干". See [[takeover-mandate-2026-09-14]].

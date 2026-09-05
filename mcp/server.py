#!/usr/bin/env python3
"""Retrieval MCP, MVP (D-WF-12): a read-only MCP server over the forest registry.

Dependency-free (stdlib only): speaks MCP over stdio as JSON-RPC 2.0 with the
2024-11-05 protocol version. Tools (D-WF-12 MVP list; lexical search only for now,
embeddings and the Lean-environment `type_search` arrive with forest-export at M0/M3):

  search(query, k, filter)      lexical search over node titles, bodies, tags
  get(address)                  full node (metadata + tree source)
  neighbors(address, direction) refs / backlinks / cited decisions
  open_tasks(area, kind)        proposed/stated/failed/blocked tests, open questions,
                                (later) sorry nodes — sorted by number of dependents
  decision(id)                  registry lookup by D-<AREA>-<nn>
  acceptance(id)                registry lookup by AT-<AREA>-<n>

Run:   python3 mcp/server.py            (stdio MCP server)
       python3 mcp/server.py --selftest (exercise every tool, exit non-zero on failure)

Claude Code:  claude mcp add category-madness -- python3 /path/to/mcp/server.py
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FOREST = ROOT / "forest"
REGISTRY = FOREST / "registry.json"

AREAS = {"ch", "kr", "rt", "up", "ft", "sp", "tl", "wf", "fd", "rm"}


class Forest:
    def __init__(self) -> None:
        reg = json.loads(REGISTRY.read_text(encoding="utf-8"))
        self.nodes: dict[str, dict] = reg["nodes"]
        self.by_id: dict[str, str] = reg["id-to-address"]
        self.bodies: dict[str, str] = {}
        for addr, n in self.nodes.items():
            p = ROOT / n["file"]
            self.bodies[addr] = p.read_text(encoding="utf-8") if p.exists() else ""

    # -- helpers
    @staticmethod
    def plain(s: str) -> str:
        prev = None
        while prev != s:
            prev = s
            s = re.sub(r"\\(?:code|strong|em|p|li|ul|ol|subtree|title|table|tr|td|th)\{([^{}]*)\}", r"\1", s)
        s = re.sub(r"\\(?:ref|transclude)\{([^}]+)\}", r"\1", s)
        s = re.sub(r"\\(?:meta|tag|taxon)\{[^}]*\}(\{[^}]*\})?", "", s)
        return re.sub(r"\s+", " ", s).strip()

    def summary(self, addr: str) -> dict:
        n = self.nodes[addr]
        return {"address": addr, "id": n["id"], "taxon": n["taxon"], "title": n["title"], "status": n["status"]}

    def resolve(self, key: str) -> str | None:
        if key in self.nodes:
            return key
        m = re.fullmatch(r"(D|AT|OQ)-([A-Z]{2})-(\d+)", key.strip())
        if m:
            kind, area, n = m.groups()
            norm = f"{kind}-{area}-{int(n):02d}" if kind == "D" else f"{kind}-{area}-{int(n)}"
            return self.by_id.get(norm)
        if key.strip() == "M-F":
            return "ms-foundation"
        m = re.fullmatch(r"M([0-7])", key.strip())
        if m:
            return f"ms-{int(m.group(1)):04d}"
        return None

    def area_of(self, addr: str) -> str | None:
        m = re.match(r"(?:dec|at|oq)-([a-z]{2})-", addr)
        return m.group(1) if m else None

    # -- tools
    def search(self, query: str, k: int = 10, filter: dict | None = None) -> list[dict]:
        terms = [t for t in re.findall(r"\w+", query.lower()) if len(t) > 1]
        filter = filter or {}
        scored = []
        for addr, n in self.nodes.items():
            if n["status"] == "superseded" and filter.get("status") != "superseded":
                continue
            if filter.get("taxon") and n["taxon"] != filter["taxon"]:
                continue
            if filter.get("status") and n["status"] != filter["status"]:
                continue
            if filter.get("area") and self.area_of(addr) != filter["area"].lower():
                continue
            title = n["title"].lower()
            body = self.plain(self.bodies[addr]).lower()
            score = 0.0
            for t in terms:
                score += 5 * title.count(t) + body.count(t)
            if query.lower() in title:
                score += 20
            if score > 0:
                scored.append((score, addr))
        scored.sort(key=lambda x: (-x[0], x[1]))
        return [dict(self.summary(a), score=s) for s, a in scored[:k]]

    def get(self, address: str) -> dict:
        addr = self.resolve(address)
        if not addr:
            raise KeyError(f"unknown node: {address}")
        n = self.nodes[addr]
        return {**self.summary(addr), "meta": n["meta"], "tags": n["tags"], "refs": n["refs"],
                "backlinks": n["backlinks"], "file": n["file"], "source": self.bodies[addr]}

    def neighbors(self, address: str, direction: str = "refs") -> list[dict]:
        addr = self.resolve(address)
        if not addr:
            raise KeyError(f"unknown node: {address}")
        n = self.nodes[addr]
        if direction == "refs":
            targets = n["refs"]
        elif direction == "backlinks":
            targets = n["backlinks"]
        elif direction == "decisions":
            targets = [r for r in n["refs"] if r.startswith("dec-")]
        else:
            raise ValueError("direction must be refs | backlinks | decisions")
        return [self.summary(t) for t in targets if t in self.nodes]

    def open_tasks(self, area: str | None = None, kind: str | None = None) -> list[dict]:
        out = []
        for addr, n in self.nodes.items():
            if area and self.area_of(addr) != area.lower():
                continue
            is_at = n["taxon"] == "Acceptance test" and n["status"] in ("proposed", "stated", "failed", "blocked")
            is_oq = n["taxon"] == "Open question" and n["status"] == "open"
            is_sorry = n["taxon"] not in ("Acceptance test", "Open question") and n["status"] == "sorry"
            if kind == "acceptance" and not is_at:
                continue
            if kind == "question" and not is_oq:
                continue
            if kind == "sorry" and not is_sorry:
                continue
            if not (is_at or is_oq or is_sorry):
                continue
            out.append(dict(self.summary(addr), dependents=len(n["backlinks"])))
        out.sort(key=lambda x: (-x["dependents"], x["address"]))
        return out

    def decision(self, id: str) -> dict:
        addr = self.resolve(id)
        if not addr or self.nodes[addr]["taxon"] != "Decision":
            raise KeyError(f"no decision {id}")
        n = self.nodes[addr]
        return {**self.summary(addr), "status_text": n["meta"].get("status-text"), "acceptance": n.get("acceptance", []),
                "supersedes": n["meta"].get("supersedes"), "superseded_by": n["meta"].get("superseded-by"),
                "origin": n["meta"].get("origin"), "text": self.plain(self.bodies[addr])}

    def acceptance(self, id: str) -> dict:
        addr = self.resolve(id)
        if not addr or self.nodes[addr]["taxon"] != "Acceptance test":
            raise KeyError(f"no acceptance test {id}")
        n = self.nodes[addr]
        return {**self.summary(addr), "named_by": [b for b in n["backlinks"] if b.startswith("dec-")],
                "text": self.plain(self.bodies[addr])}


TOOLS = [
    {"name": "search", "description": "Lexical search over forest nodes (decisions, acceptance tests, open questions, milestones, references, chapters).",
     "inputSchema": {"type": "object", "properties": {"query": {"type": "string"}, "k": {"type": "integer", "default": 10},
                     "filter": {"type": "object", "properties": {"taxon": {"type": "string"}, "status": {"type": "string"}, "area": {"type": "string"}}}},
                     "required": ["query"]}},
    {"name": "get", "description": "Full node by address (dec-rt-0003) or identifier (D-RT-18, AT-KR-2, OQ-SP-1, M3).",
     "inputSchema": {"type": "object", "properties": {"address": {"type": "string"}}, "required": ["address"]}},
    {"name": "neighbors", "description": "Nodes linked from/to a node. direction: refs | backlinks | decisions.",
     "inputSchema": {"type": "object", "properties": {"address": {"type": "string"}, "direction": {"type": "string", "default": "refs"}}, "required": ["address"]}},
    {"name": "open_tasks", "description": "Actionable acceptance tests, open questions and sorry nodes, sorted by number of dependents. kind: acceptance | question | sorry.",
     "inputSchema": {"type": "object", "properties": {"area": {"type": "string"}, "kind": {"type": "string"}}}},
    {"name": "decision", "description": "Decision registry lookup by D-<AREA>-<nn>.",
     "inputSchema": {"type": "object", "properties": {"id": {"type": "string"}}, "required": ["id"]}},
    {"name": "acceptance", "description": "Acceptance-test lookup by AT-<AREA>-<n>.",
     "inputSchema": {"type": "object", "properties": {"id": {"type": "string"}}, "required": ["id"]}},
]


def call(forest: Forest, name: str, args: dict):
    fn = getattr(forest, name, None)
    if fn is None or name not in {t["name"] for t in TOOLS}:
        raise KeyError(f"unknown tool {name}")
    return fn(**args)


def serve() -> None:
    forest = Forest()

    def send(obj: dict) -> None:
        sys.stdout.write(json.dumps(obj) + "\n")
        sys.stdout.flush()

    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        try:
            req = json.loads(line)
        except json.JSONDecodeError:
            continue
        rid, method, params = req.get("id"), req.get("method"), req.get("params") or {}
        if method == "initialize":
            send({"jsonrpc": "2.0", "id": rid, "result": {"protocolVersion": "2024-11-05", "capabilities": {"tools": {}},
                                                          "serverInfo": {"name": "category-madness-forest", "version": "0.1.0"}}})
        elif method == "notifications/initialized":
            continue
        elif method == "tools/list":
            send({"jsonrpc": "2.0", "id": rid, "result": {"tools": TOOLS}})
        elif method == "tools/call":
            try:
                result = call(forest, params.get("name", ""), params.get("arguments") or {})
                send({"jsonrpc": "2.0", "id": rid, "result": {"content": [{"type": "text", "text": json.dumps(result, ensure_ascii=False, indent=1)}]}})
            except Exception as e:  # noqa: BLE001 — report to the client, keep serving
                send({"jsonrpc": "2.0", "id": rid, "result": {"content": [{"type": "text", "text": f"error: {e}"}], "isError": True}})
        elif method == "ping":
            send({"jsonrpc": "2.0", "id": rid, "result": {}})
        elif rid is not None:
            send({"jsonrpc": "2.0", "id": rid, "error": {"code": -32601, "message": f"method not found: {method}"}})


def selftest() -> int:
    f = Forest()
    assert f.search("Segal condition")[0]["address"], "search returns nothing"
    assert f.get("D-RT-16")["address"] == "dec-rt-0016"
    assert f.get("M-F")["address"] == "ms-foundation"
    assert any(n["address"] == "at-fd-0001" for n in f.neighbors("D-FD-01", "refs"))
    assert any(n["address"] == "dec-fd-0001" for n in f.neighbors("AT-FD-1", "backlinks"))
    tasks = f.open_tasks(area="fd", kind="acceptance")
    assert tasks and all(t["taxon"] == "Acceptance test" for t in tasks)
    d = f.decision("D-CH-14")
    assert d["status"] == "frozen" and "Rationale" in d["text"]
    a = f.acceptance("AT-FD-1")
    assert "dec-fd-0001" in a["named_by"]
    print(f"mcp selftest ok: {len(f.nodes)} nodes, {len(f.open_tasks())} open tasks")
    return 0


if __name__ == "__main__":
    sys.exit(selftest() if "--selftest" in sys.argv else serve())

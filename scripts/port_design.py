#!/usr/bin/env python3
"""One-shot port of the phase −1 design documents (design/*.md) into forester trees.

This script implements the porting instructions of design/07-forest-workflow.md
("Porting instructions (phase −1 → M0)") and design/README.md:

  * one tree per decision (D-<AREA>-<nn>), acceptance test (AT-<AREA>-<n>),
    open question (OQ-<AREA>-<n>), milestone (M0…M7, phase −1) and bibliography entry;
  * one handwritten-style chapter tree per design document that transcludes those nodes
    (D-WF-06), so the prose survives without restating the decision text;
  * Rationale and Rejected alternatives are carried over verbatim (markdown inline
    markup is translated, words are not changed);
  * the address mapping of D-WF-07 (below); the registry itself is derived from the
    trees by scripts/build_registry.py, so that later amendments to trees are reflected.

Address scheme (adaptation of D-WF-07, recorded here and in wf-0001):

  D-RT-03  -> dec-rt-0003      AT-KR-2 -> at-kr-0002      OQ-SP-1 -> oq-sp-0001
  M3       -> ms-0003          phase −1 -> ms-design      chapters -> <area>-0000
  bibliography entries -> bib-NNNN (in document order)

The identifiers stay embedded in the address so that agents never need a lookup table
to go from a citation in a PR to the node.

The script is deterministic and idempotent. It was run once at M0; after that the
trees in forest/ are primary (README: "After the port the forest is primary and these
files are frozen as history") and this script is kept as the audit trail of the port.
It is NOT run in CI: provisional nodes are amended in place (D-TL-01), so regenerating
from the frozen markdown would clobber those amendments.
"""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DESIGN = ROOT / "design"
FOREST = ROOT / "forest"

AREA_NAMES = {
    "CH": "charter",
    "KR": "kernel",
    "RT": "root",
    "UP": "universal properties",
    "FT": "formal theory",
    "SP": "spaces and enrichment",
    "TL": "tooling",
    "WF": "forest and workflow",
    "RM": "roadmap",
}

# design document -> chapter address (area prefix + 0000)
CHAPTERS = {
    "00-charter.md": ("ch-0000", "CH"),
    "01-kernel.md": ("krn-0000", "KR"),
    "02-root.md": ("rt-0000", "RT"),
    "03-universal-properties.md": ("up-0000", "UP"),
    "04-formal-theory.md": ("ft-0000", "FT"),
    "05-spaces-enrichment.md": ("sp-0000", "SP"),
    "06-tooling.md": ("tl-0000", "TL"),
    "07-forest-workflow.md": ("wf-0000", "WF"),
    "08-roadmap.md": ("rm-0000", "RM"),
    "09-bibliography.md": ("bib-0000", None),
    "10-adversarial-review.md": ("rev-0000", None),
}
# "→ 04" style cross references to whole documents
DOC_NUMBER_TO_CHAPTER = {name[:2]: addr for name, (addr, _) in CHAPTERS.items()}

FIELD_ORDER = [
    "Decision",
    "Consequence",
    "Note on E1",
    "Theorem targets",
    "Theorem target",
    "Rationale",
    "Rejected",
    "Not viable, and why",
    "Acceptance",
    "Status",
    "Freeze",
    "Exit",
]

# ----------------------------------------------------------------------------- addresses


def dec_addr(area: str, n: int) -> str:
    return f"dec-{area.lower()}-{n:04d}"


def at_addr(area: str, n: int) -> str:
    return f"at-{area.lower()}-{n:04d}"


def oq_addr(area: str, n: int) -> str:
    return f"oq-{area.lower()}-{n:04d}"


def ms_addr(n: int) -> str:
    return f"ms-{n:04d}"


ID_RE = re.compile(r"\b(D|AT|OQ)-([A-Z]{2})-(\d+)\b")


def id_to_addr(kind: str, area: str, n: int) -> str:
    return {"D": dec_addr, "AT": at_addr, "OQ": oq_addr}[kind](area, n)


def id_of(kind: str, area: str, n: int) -> str:
    return f"{kind}-{area}-{n:02d}" if kind == "D" else f"{kind}-{area}-{n}"


# ----------------------------------------------------------------------------- inline markup


def escape_text(s: str) -> str:
    """Escape characters that are syntactically active in forester outside verbatim."""
    out = s.replace("\\", "\\\\")
    out = out.replace("%", "\\%")
    # `#{` would open inline math; the documents contain no '#', assert rather than guess.
    assert "#" not in out, s
    return out


def code_span(s: str) -> str:
    # Braces inside \code{...} must balance; a backslash would be read as a command.
    if s.count("{") != s.count("}"):
        raise ValueError(f"unbalanced braces in code span: {s!r}")
    s = s.replace("\\", "")  # only occurrence: `\transclude` in D-WF-06
    return "\\code{" + s + "}"


KNOWN_IDS: set[str] = set()  # filled before rendering, used to validate references
UNRESOLVED: list[str] = []


def link_ids(s: str) -> str:
    """Turn D-/AT-/OQ-/M- identifiers and → 0N document references into \\ref."""

    def rng(m: re.Match) -> str:
        kind, area, a, b = m.group(1), m.group(2), int(m.group(3)), int(m.group(4))
        return f"{ref(kind, area, a)}…{ref(kind, area, b)}"

    def ref(kind: str, area: str, n: int) -> str:
        addr = id_to_addr(kind, area, n)
        if addr not in KNOWN_IDS:
            UNRESOLVED.append(addr)
            return id_of(kind, area, n)
        return f"\\ref{{{addr}}}"

    def single(m: re.Match) -> str:
        return ref(m.group(1), m.group(2), int(m.group(3)))

    s = re.sub(r"\b(D|AT|OQ)-([A-Z]{2})-(\d+)…(\d+)\b", rng, s)
    s = ID_RE.sub(single, s)
    # milestones: "M3", "M6+", "M0–M1"
    s = re.sub(r"\bM([0-7])\b", lambda m: f"\\ref{{{ms_addr(int(m.group(1)))}}}", s)
    # whole-document references: "→ 04", "→ 07 porting instructions", "(→ 03)"
    s = re.sub(
        r"→ (0\d|10)\b",
        lambda m: f"→ \\ref{{{DOC_NUMBER_TO_CHAPTER[m.group(1)]}}}",
        s,
    )
    return s


def inline(md: str, link: bool = True) -> str:
    """Markdown inline → forester inline.

    Code spans are replaced by placeholders first so that bold/italic markers may span
    them (e.g. **The 2-category `Cat`.**) while `*` inside code (`f_*`) is left alone.
    """
    codes: list[str] = []

    def stash(m: re.Match) -> str:
        codes.append(code_span(m.group(1)))
        return f"\x00{len(codes) - 1}\x00"

    t = re.sub(r"`([^`]*)`", stash, md)
    t = escape_text(t)
    t = re.sub(r"\*\*(.+?)\*\*", r"\\strong{\1}", t)
    t = re.sub(r"(?<![\w*])\*(?!\s)(.+?)(?<!\s)\*(?![\w*])", r"\\em{\1}", t)
    if link:
        t = link_ids(t)
    t = re.sub(r"\x00(\d+)\x00", lambda m: codes[int(m.group(1))], t)
    return t


# ----------------------------------------------------------------------------- block parsing


@dataclass
class Block:
    kind: str  # para | ul | ol | table
    lines: list[str] = field(default_factory=list)  # para: text lines; lists: items
    rows: list[list[str]] = field(default_factory=list)


FIELD_RE = re.compile(r"^\*\*([A-Z][^*]*?\.)\*\*\s?(.*)$")
UL_RE = re.compile(r"^- (.*)$")
OL_RE = re.compile(r"^(\d+)\. (.*)$")


def parse_blocks(lines: list[str]) -> list[Block]:
    """Parse a run of markdown lines (no headings) into blocks."""
    blocks: list[Block] = []
    cur: Block | None = None

    def close() -> None:
        nonlocal cur
        if cur is not None:
            blocks.append(cur)
        cur = None

    for raw in lines:
        line = raw.rstrip("\n")
        if not line.strip():
            close()
            continue
        if line.startswith("|"):
            if cur is None or cur.kind != "table":
                close()
                cur = Block("table")
            cells = [c.strip() for c in line.strip().strip("|").split("|")]
            if all(re.fullmatch(r"-+", c) for c in cells):
                continue
            cur.rows.append(cells)
            continue
        m = UL_RE.match(line)
        if m:
            if cur is None or cur.kind != "ul":
                close()
                cur = Block("ul")
            cur.lines.append(m.group(1))
            continue
        m = OL_RE.match(line)
        if m:
            if cur is None or cur.kind != "ol":
                close()
                cur = Block("ol")
            cur.lines.append(m.group(2))
            continue
        if line.startswith("  ") and cur is not None and cur.kind in ("ul", "ol"):
            cur.lines[-1] += " " + line.strip()
            continue
        if cur is None or cur.kind != "para":
            close()
            cur = Block("para")
        cur.lines.append(line.strip())
    close()
    return blocks


def split_fields(lines: list[str]) -> list[tuple[str | None, list[str]]]:
    """Split a section body into (field name, lines) runs on **Field.** markers."""
    runs: list[tuple[str | None, list[str]]] = []
    name: str | None = None
    buf: list[str] = []
    for line in lines:
        m = FIELD_RE.match(line)
        if m and m.group(1)[:-1] in FIELD_ORDER:
            if buf or name is not None:
                runs.append((name, buf))
            name, buf = m.group(1)[:-1], [m.group(2)] if m.group(2) else []
        else:
            buf.append(line)
    if buf or name is not None:
        runs.append((name, buf))
    # drop a leading empty unnamed run
    return [(n, b) for n, b in runs if n is not None or any(l.strip() for l in b)]


# ----------------------------------------------------------------------------- rendering


def render_blocks(blocks: list[Block], indent: int = 0) -> str:
    pad = " " * indent
    out: list[str] = []
    for b in blocks:
        if b.kind == "para":
            out.append(f"{pad}\\p{{{inline(' '.join(b.lines))}}}")
        elif b.kind in ("ul", "ol"):
            items = "\n".join(f"{pad}  \\li{{{inline(it)}}}" for it in b.lines)
            out.append(f"{pad}\\{b.kind}{{\n{items}\n{pad}}}")
        elif b.kind == "table":
            head, *body = b.rows
            rows = [f"{pad}  \\tr{{" + "".join(f"\\th{{{inline(c)}}}" for c in head) + "}"]
            rows += [f"{pad}  \\tr{{" + "".join(f"\\td{{{inline(c)}}}" for c in r) + "}" for r in body]
            out.append(f"{pad}\\table{{\n" + "\n".join(rows) + f"\n{pad}}}")
    return "\n".join(out)


def render_fields(runs: list[tuple[str | None, list[str]]], indent: int = 0) -> str:
    pad = " " * indent
    out: list[str] = []
    for name, lines in runs:
        blocks = parse_blocks(lines)
        if name is None:
            out.append(render_blocks(blocks, indent))
            continue
        body = render_blocks(blocks, indent + 2)
        out.append(f"{pad}\\subtree{{\n{pad}  \\title{{{name}}}\n{body}\n{pad}}}")
    return "\n".join(out)


def status_level(runs: list[tuple[str | None, list[str]]]) -> str | None:
    for name, lines in runs:
        if name == "Status":
            text = " ".join(lines).strip()
            m = re.match(r"(frozen|provisional|later)", text)
            return m.group(1) if m else text
    return None


def status_text(runs: list[tuple[str | None, list[str]]]) -> str | None:
    for name, lines in runs:
        if name == "Status":
            return " ".join(l.strip() for l in lines).strip()
    return None


def tree(addr: str, title: str, taxon: str, meta: dict[str, str], tags: list[str], body: str) -> str:
    head = [f"\\title{{{title}}}", f"\\taxon{{{taxon}}}"]
    head += [f"\\meta{{{k}}}{{{v}}}" for k, v in meta.items()]
    head += [f"\\tag{{{t}}}" for t in tags]
    text = "\n".join(head) + "\n\n" + body.rstrip() + "\n"
    check_braces(addr, text)
    return text


def check_braces(addr: str, text: str) -> None:
    depth = 0
    for ch in text:
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
        if depth < 0:
            raise ValueError(f"{addr}: unbalanced braces")
    if depth != 0:
        raise ValueError(f"{addr}: unbalanced braces (depth {depth})")


# ----------------------------------------------------------------------------- document model


@dataclass
class Section:
    level: int
    heading: str
    lines: list[str]


def read_sections(path: Path) -> tuple[str, list[Section]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    title = ""
    secs: list[Section] = []
    cur: Section | None = None
    for line in lines:
        m = re.match(r"^(#{1,3}) (.*)$", line)
        if m:
            level, heading = len(m.group(1)), m.group(2).strip()
            if level == 1 and not title:
                title = heading
                cur = Section(1, heading, [])
                secs.append(cur)
                continue
            cur = Section(level, heading, [])
            secs.append(cur)
        elif cur is not None:
            cur.lines.append(line)
    return title, secs


DEC_HEAD = re.compile(r"^D-([A-Z]{2})-(\d+) · (.*)$")
MS_HEAD = re.compile(r"^M([0-7]) · (.*)$")
PHASE_HEAD = re.compile(r"^Phase −1 · (.*)$")
AT_ITEM = re.compile(r"^AT-([A-Z]{2})-(\d+) (.*)$")
OQ_ITEM = re.compile(r"^OQ-([A-Z]{2})-(\d+) (.*)$")


@dataclass
class Node:
    addr: str
    id: str
    title: str
    taxon: str
    area: str | None
    origin: str
    status: str | None = None
    status_text: str | None = None
    body: str = ""
    refs: list[str] = field(default_factory=list)
    acceptance: list[str] = field(default_factory=list)
    informal: str = ""


def main() -> None:
    FOREST.mkdir(exist_ok=True)
    nodes: dict[str, Node] = {}
    chapters: list[tuple[str, str, str]] = []  # (addr, title, body)

    docs = [(name, *read_sections(DESIGN / name)) for name in CHAPTERS]

    # ---- pass 1: discover every identifier so references can be validated ----
    at_informal: dict[str, str] = {}
    oq_informal: dict[str, tuple[str, str]] = {}
    for name, _title, secs in docs:
        chap, _area = CHAPTERS[name]
        for s in secs:
            if s.level == 3:
                m = DEC_HEAD.match(s.heading)
                if m:
                    KNOWN_IDS.add(dec_addr(m.group(1), int(m.group(2))))
                m = MS_HEAD.match(s.heading)
                if m:
                    KNOWN_IDS.add(ms_addr(int(m.group(1))))
            for item in (it for b in parse_blocks(s.lines) if b.kind == "ul" for it in b.lines):
                ma = AT_ITEM.match(item)
                if ma and s.heading.startswith("Acceptance tests"):
                    addr = at_addr(ma.group(1), int(ma.group(2)))
                    KNOWN_IDS.add(addr)
                    at_informal[addr] = ma.group(3)
                mo = OQ_ITEM.match(item)
                if mo and s.heading.startswith("Open questions"):
                    addr = oq_addr(mo.group(1), int(mo.group(2)))
                    KNOWN_IDS.add(addr)
                    oq_informal[addr] = (mo.group(3), chap)
    # acceptance tests that only occur inside decision text (03: AT-UP-1…8, AT-KR-0)
    text_all = "\n".join((DESIGN / n).read_text(encoding="utf-8") for n in CHAPTERS)
    for m in re.finditer(r"\bAT-([A-Z]{2})-(\d+)\b", text_all):
        KNOWN_IDS.add(at_addr(m.group(1), int(m.group(2))))
    for m in re.finditer(r"\bOQ-([A-Z]{2})-(\d+)\b", text_all):
        addr = oq_addr(m.group(1), int(m.group(2)))
        if addr not in KNOWN_IDS:
            raise ValueError(f"open question referenced but never listed: {addr}")
    KNOWN_IDS.update(addr for addr, _ in CHAPTERS.values())
    KNOWN_IDS.add("ms-design")

    # informal statements for ATs not in a summary list: taken from the Acceptance field
    # of the decision that names them ("AT-UP-1: …; AT-UP-2: …").
    for m in re.finditer(r"\*\*Acceptance\.\*\*\s*(.*?)(?=\n\*\*|\n###|\n\n|\Z)", text_all, re.S):
        chunk = " ".join(m.group(1).split())
        for seg in re.split(r";\s*(?=AT-)", chunk):
            ms = re.match(r"AT-([A-Z]{2})-(\d+)[:]?\s*(.*)$", seg)
            if ms:
                addr = at_addr(ms.group(1), int(ms.group(2)))
                at_informal.setdefault(addr, ms.group(3).rstrip("."))
    at_informal.setdefault(at_addr("KR", 0), "Mathlib inventory node exists and is verified (→ D-KR-02).")
    # AT-UP-6 is only ever written "(Čech nerve as above)"; spell out the "above" from D-UP-07.
    at_informal[at_addr("UP", 6)] = (
        "Čech nerve: the Čech nerve of `f : x → s` is `cosk₀` in augmented simplicial objects over `s`; "
        "its `n`-th term is a limit over the appropriate shape; it exists when the relevant limits do; "
        "it is unique up to contractible choice; it is functorial in `f` (→ D-UP-07)"
    )

    # ---- pass 2: build nodes and chapters ----
    bib_counter = 0
    for name, doc_title, secs in docs:
        chap, area = CHAPTERS[name]
        chapter_body: list[str] = []
        current_sub: list[str] | None = None
        sub_title = ""

        def flush_sub() -> None:
            nonlocal current_sub
            if current_sub is not None:
                inner = "\n".join(current_sub)
                chapter_body.append(f"\\subtree{{\n  \\title{{{inline(sub_title)}}}\n{inner}\n}}")
            current_sub = None

        def emit(text: str) -> None:
            (current_sub if current_sub is not None else chapter_body).append(text)

        for s in secs:
            if s.level == 1:
                chapter_body.append(render_blocks(parse_blocks(s.lines)))
                continue
            if s.level == 2:
                flush_sub()
                sub_title = s.heading
                current_sub = []
                if s.heading.startswith("Acceptance tests"):
                    for line in s.lines:
                        m = UL_RE.match(line)
                        ma = AT_ITEM.match(m.group(1)) if m else None
                        if ma:
                            emit(f"  \\transclude{{{at_addr(ma.group(1), int(ma.group(2)))}}}")
                    continue
                if s.heading.startswith("Open questions"):
                    for line in s.lines:
                        m = UL_RE.match(line)
                        mo = OQ_ITEM.match(m.group(1)) if m else None
                        if mo:
                            emit(f"  \\transclude{{{oq_addr(mo.group(1), int(mo.group(2)))}}}")
                    continue
                if name == "09-bibliography.md":
                    for line in s.lines:
                        m = UL_RE.match(line)
                        if not m:
                            continue
                        bib_counter += 1
                        addr = f"bib-{bib_counter:04d}"
                        entry = m.group(1)
                        mt = re.match(r"\*\*(.+?)\*\*\s*—\s*(.*)$", entry)
                        authors = mt.group(1) if mt else entry
                        rest = mt.group(2) if mt else ""
                        titles = re.findall(r"\*([^*]+)\*", rest)
                        title = f"{authors} — {titles[0]}" if titles else authors
                        body = f"\\p{{{inline(entry)}}}"
                        meta = {"origin": f"design/{name}", "section": s.heading}
                        nodes[addr] = Node(addr, addr, title, "Reference", None, f"design/{name}", body=body)
                        (FOREST / f"{addr}.tree").write_text(
                            tree(addr, inline(title), "Reference", meta, ["reference"], body), encoding="utf-8"
                        )
                        emit(f"  \\transclude{{{addr}}}")
                    continue
                emit(render_blocks(parse_blocks(s.lines), 2))
                continue
            # level 3
            m = DEC_HEAD.match(s.heading)
            if m:
                a, n, title = m.group(1), int(m.group(2)), m.group(3)
                addr = dec_addr(a, n)
                ident = f"D-{a}-{n:02d}"
                runs = split_fields(s.lines)
                body = render_fields(runs)
                st = status_level(runs)
                stt = status_text(runs)
                if st is None:
                    # D-RT-02 ("what a VDC∞ is not") carries no Status field in the source.
                    # It is a clarification of D-RT-01 and inherits its freeze; recorded in wf-0001.
                    st, stt = "frozen", "not stated in the source; frozen with D-RT-01 (port judgment call)."
                meta = {
                    "id": ident,
                    "area": AREA_NAMES[a],
                    "origin": f"design/{name}",
                    "status": st or "unspecified",
                }
                if stt:
                    meta["status-text"] = inline(stt, link=False)
                meta["supersedes"] = "none"
                meta["superseded-by"] = "none"
                tags = ["decision", f"area:{a.lower()}", f"status:{st or 'unspecified'}"]
                text = tree(addr, inline(f"{ident} · {title}", link=False), "Decision", meta, tags, body)
                (FOREST / f"{addr}.tree").write_text(text, encoding="utf-8")
                node = Node(addr, ident, title, "Decision", a, f"design/{name}", st, stt, body)
                node.refs = sorted(set(re.findall(r"\\ref\{([^}]+)\}", text)))
                node.acceptance = sorted(set(r for r in node.refs if r.startswith("at-")))
                nodes[addr] = node
                emit(f"  \\transclude{{{addr}}}" if current_sub is not None else f"\\transclude{{{addr}}}")
                continue
            m = MS_HEAD.match(s.heading) or PHASE_HEAD.match(s.heading)
            if m and name == "08-roadmap.md":
                if MS_HEAD.match(s.heading):
                    n = int(m.group(1))
                    addr, ident, title = ms_addr(n), f"M{n}", m.group(2)
                else:
                    addr, ident, title = "ms-design", "Phase −1", m.group(1)
                runs = split_fields(s.lines)
                body = render_fields(runs)
                meta = {"id": ident, "origin": f"design/{name}", "status": "planned"}
                text = tree(addr, inline(f"{ident} · {title}", link=False), "Milestone", meta, ["milestone"], body)
                (FOREST / f"{addr}.tree").write_text(text, encoding="utf-8")
                node = Node(addr, ident, title, "Milestone", None, f"design/{name}", "planned", body=body)
                node.refs = sorted(set(re.findall(r"\\ref\{([^}]+)\}", text)))
                nodes[addr] = node
                emit(f"  \\transclude{{{addr}}}" if current_sub is not None else f"\\transclude{{{addr}}}")
                continue
            # any other ### heading becomes a subtree in the chapter
            body = render_blocks(parse_blocks(s.lines), 4 if current_sub is not None else 2)
            emit(f"  \\subtree{{\n    \\title{{{inline(s.heading)}}}\n{body}\n  }}")
        flush_sub()
        chapters.append((chap, doc_title, "\n".join(chapter_body)))

    # ---- acceptance-test nodes ----
    # Which decisions cite each AT (for the "affected decisions" field).
    for addr, informal in sorted(at_informal.items()):
        m = re.match(r"at-([a-z]{2})-(\d+)", addr)
        a, n = m.group(1).upper(), int(m.group(2))
        ident = f"AT-{a}-{n}"
        citing = sorted(d.addr for d in nodes.values() if d.taxon == "Decision" and addr in d.refs)
        body_lines = [f"\\p{{{inline(informal)}}}"]
        if citing:
            body_lines.append(
                "\\p{Named by: " + ", ".join(f"\\ref{{{c}}}" for c in citing) + ".}"
            )
        body_lines.append("\\p{\\em{Lean declaration(s):} none yet.}")
        body = "\n".join(body_lines)
        meta = {
            "id": ident,
            "area": AREA_NAMES[a],
            "origin": f"design/{[n for n, (c, ar) in CHAPTERS.items() if ar == a][0]}",
            "status": "unstated",
        }
        short = re.split(r"[.;:]", informal, maxsplit=1)[0].strip()
        if len(short) > 90:
            short = short[:87].rsplit(" ", 1)[0] + "…"
        text = tree(addr, inline(f"{ident} · {short}", link=False), "Acceptance test", meta, ["acceptance-test", f"area:{a.lower()}", "status:unstated"], body)
        (FOREST / f"{addr}.tree").write_text(text, encoding="utf-8")
        node = Node(addr, ident, informal, "Acceptance test", a, meta["origin"], "unstated", body=body, informal=informal)
        node.refs = citing
        nodes[addr] = node

    # ---- open-question nodes ----
    for addr, (informal, chap) in sorted(oq_informal.items()):
        m = re.match(r"oq-([a-z]{2})-(\d+)", addr)
        a, n = m.group(1).upper(), int(m.group(2))
        ident = f"OQ-{a}-{n}"
        body = f"\\p{{{inline(informal)}}}\n\\p{{\\em{{Resolution:}} open. Decided by the human; record the answer as a decision node that this node then cites.}}"
        origin = [nm for nm, (c, ar) in CHAPTERS.items() if c == chap][0]
        meta = {"id": ident, "area": AREA_NAMES[a], "origin": f"design/{origin}", "status": "open"}
        text = tree(addr, ident, "Open question", meta, ["open-question", f"area:{a.lower()}", "status:open"], body)
        (FOREST / f"{addr}.tree").write_text(text, encoding="utf-8")
        node = Node(addr, ident, informal, "Open question", a, meta["origin"], "open", body=body, informal=informal)
        node.refs = sorted(set(re.findall(r"\\ref\{([^}]+)\}", text)))
        nodes[addr] = node

    # ---- chapter trees ----
    for chap, title, body in chapters:
        text = tree(chap, inline(title), "Chapter", {"origin": "design/" + [n for n, (c, _) in CHAPTERS.items() if c == chap][0], "layer": "human"}, ["chapter"], body)
        (FOREST / f"{chap}.tree").write_text(text, encoding="utf-8")

    if UNRESOLVED:
        print("UNRESOLVED references (left as plain text):", sorted(set(UNRESOLVED)), file=sys.stderr)
    counts: dict[str, int] = {}
    for n in nodes.values():
        counts[n.taxon] = counts.get(n.taxon, 0) + 1
    print("wrote", len(nodes), "nodes +", len(chapters), "chapters:", counts)


if __name__ == "__main__":
    main()

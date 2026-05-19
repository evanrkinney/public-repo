#!/usr/bin/env python3
"""Convert a Splunk SOAR playbook .py file into an editable draw.io diagram.

Each `@phantom.playbook_block()` function becomes a node in the diagram. Block
type (PLAYBOOK / DECISION / FILTER / CODE / FORMAT / UTILITY / ACTION / START /
END) is inferred from the phantom.* calls inside the function. The ###-banner
comment block at the top of each function becomes a sticky-note attached to
that node. Edges are recovered from `callback=` keyword args and from direct
calls to other block functions (including the `if`/`else` branches of decision
blocks).

Output is a .drawio XML file. Open it in app.diagrams.net, the draw.io desktop
app, or the VS Code "Draw.io Integration" extension to edit. Export to PDF via
File -> Export As -> PDF, or pass --pdf to this script if you have the draw.io
CLI on PATH.

Usage:
    python playbook_to_drawio.py path/to/Playbook.py
    python playbook_to_drawio.py path/to/Playbook.py -o out.drawio --pdf
"""

from __future__ import annotations

import argparse
import ast
import re
import shutil
import subprocess
import sys
import uuid
from dataclasses import dataclass, field
from pathlib import Path
from urllib.parse import quote as _url_quote
from xml.sax.saxutils import escape as _xml_escape


def xml_escape(s: str) -> str:
    """Escape for use inside an XML attribute value (double-quoted)."""
    return _xml_escape(s, {'"': "&quot;"})


# ---------------------------------------------------------------------------
# Block type inference
# ---------------------------------------------------------------------------

PHANTOM_CALL_TO_TYPE = {
    "playbook": "PLAYBOOK",
    "decision": "DECISION",
    "condition": "FILTER",
    "format": "FORMAT",
    "custom_function": "UTILITY",
    "act": "ACTION",
    "comment": "UTILITY",
    "prompt": "PROMPT",
    "prompt2": "PROMPT",
}

# Higher priority wins when a function makes multiple phantom.* calls.
TYPE_PRIORITY = ["DECISION", "PLAYBOOK", "FILTER", "ACTION", "PROMPT", "FORMAT", "UTILITY"]

# Per-type accent — user-supplied Splunk palette, brightened ~15-20% so each
# accent reads punchy against the dark page.
TYPE_ACCENT = {
    "START":    "#6E7079",  # neutral gray (intentionally muted)
    "END":      "#6E7079",
    "PLAYBOOK": "#B043C1",  # vivid magenta/purple
    "DECISION": "#7CD2BB",  # mint (already bright)
    "FILTER":   "#8AA0FF",  # lifted indigo
    "CODE":     "#5066D6",  # vivid mid-blue
    "FORMAT":   "#EE7B92",  # bright rose
    "UTILITY":  "#9D6FF0",  # bright violet
    "ACTION":   "#A8DD9D",  # luminous leaf green
    "PROMPT":   "#FAD476",  # bright amber
    "ES":       "#5FA15B",  # brighter forest
}

# Branch labels coming off DECISION / FILTER blocks ("condition 1" through
# "condition 5") get distinct accent colors so a branch can be traced at a
# glance.  Falls through to the default edge-label chrome for >5.
CONDITION_ACCENT = {
    1: "#9F72E8",
    2: "#71D1BB",
    3: "#D5EF7E",
    4: "#D8657B",
    5: "#F5D191",
}

# Splunk Enterprise Dark — exact token values pulled from
# splunkui.splunk.com/Packages/themes/Variables.
COLOR_BG = "#111215"                  # backgroundColorPage
COLOR_SIDEBAR = "#0b0c0e"             # backgroundColorSidebar (darker bg)
COLOR_BLOCK_BG = "#1a1c20"            # backgroundColorSection (card surface)
COLOR_BLOCK_BG_FLOAT = "#27292e"      # raised surface
COLOR_BLOCK_BORDER = "#3d3e43"        # borderColorWeak
COLOR_BORDER_STRONG = "#717275"       # borderColor
COLOR_EDGE = "#717275"                # borderColor
COLOR_EDGE_LABEL_BG = "#1a1c20"
COLOR_EDGE_LABEL_BORDER = "#3d3e43"
COLOR_EDGE_LABEL_TEXT = "#b5b5b5"     # contentColorDefault
COLOR_TEXT_PRIMARY = "#fafafa"        # contentColorActive
COLOR_TEXT_SECONDARY = "#909090"      # contentColorMuted
COLOR_TEXT_BODY = "#b5b5b5"           # contentColorDefault
COLOR_TEXT_DISABLED = "#6b6b6b"       # contentColorDisabled
COLOR_NOTE_BG = "#FFFFFF"             # pure white description card
COLOR_NOTE_BORDER = "#D1D5DB"
COLOR_NOTE_TEXT = "#1F2937"
COLOR_NOTE_MUTED = "#6B7280"
COLOR_TABLE_HEADER_BG = "#F1F5F9"
COLOR_TABLE_BORDER = "#CBD5E1"
COLOR_CODE_BG = "#F1F5F9"
COLOR_ORPHAN_STROKE = "#505158"       # neutral300 in dark theme
COLOR_DOT_GRID = "#2C2F38"            # soft dot grid matching SOAR canvas
DOT_GRID_SPACING = 18
DOT_GRID_RADIUS = 1.1

COLOR_SECTION_BORDER = "#3d3e43"      # borderColorWeak — for card outlines
SECTION_CARD_RADIUS = 8
PAGE_OUTER_MARGIN = 28                # inset of the outer page border
SECTION_PAD = 24                      # padding inside section borders

# Splunk type system (REMs translated to ~16-base px, rounded for our scale).
SPLUNK_FONT_STACK = (
    "'Splunk Platform Sans', 'Splunk Data Sans', Roboto, Droid, "
    "'Helvetica Neue', Helvetica, Arial, sans-serif"
)
FONT_SIZE_SMALL = 11        # 0.75rem
FONT_SIZE_BODY = 13         # 0.875rem (Splunk default)
FONT_SIZE_LARGE = 14        # 1rem
FONT_SIZE_XL = 17           # 1.25rem
FONT_SIZE_XXL = 22          # 1.5rem
FONT_WEIGHT_NORMAL = 400
FONT_WEIGHT_SEMIBOLD = 500
FONT_WEIGHT_BOLD = 700
FONT_WEIGHT_HEAVY = 800

# Splunk visual chrome
SPLUNK_BORDER_RADIUS = 4    # borderRadius
SPLUNK_EMBOSS_SHADOW = (    # embossShadow — subtle 1px lift
    "0px 1px 5px rgba(0, 0, 0, 0.35), 0px 0px 1px rgba(0, 0, 0, 0.35)"
)


@dataclass
class Block:
    name: str
    type: str
    description: str
    outgoing: list[tuple[str, str]] = field(default_factory=list)
    lineno: int = 0


# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------


def _is_playbook_block_decorator(dec: ast.AST) -> bool:
    target = dec.func if isinstance(dec, ast.Call) else dec
    return (
        isinstance(target, ast.Attribute)
        and isinstance(target.value, ast.Name)
        and target.value.id == "phantom"
        and target.attr == "playbook_block"
    )


_ES_TOKENS = ("splunk_es", "enterprise_security", "es_correlation",
              "notable_event", "splunk-es")


def _detect_block_type(func: ast.FunctionDef) -> str:
    if func.name == "on_start":
        return "START"
    if func.name == "on_finish":
        return "END"

    # Enterprise Security wins over the generic UTILITY / ACTION mapping:
    # any call referencing the splunk_es / enterprise_security app brands
    # the whole block as an ES integration.
    for node in ast.walk(func):
        if isinstance(node, ast.Call):
            for kw in node.keywords:
                if kw.arg in ("custom_function", "connector_id", "action",
                              "app", "name"):
                    v = kw.value
                    if isinstance(v, ast.Constant) and isinstance(v.value, str):
                        lo = v.value.lower()
                        if any(tok in lo for tok in _ES_TOKENS):
                            return "ES"

    seen: list[str] = []
    for node in ast.walk(func):
        if isinstance(node, ast.Call):
            callee = node.func
            if (
                isinstance(callee, ast.Attribute)
                and isinstance(callee.value, ast.Name)
                and callee.value.id == "phantom"
                and callee.attr in PHANTOM_CALL_TO_TYPE
            ):
                seen.append(PHANTOM_CALL_TO_TYPE[callee.attr])

    for t in TYPE_PRIORITY:
        if t in seen:
            return t
    return "CODE"


_SCAFFOLD_LINES = {
    "custom code start",
    "custom code end",
    "write your custom code here...",
    "write your custom code here",
}


def _extract_description(source_lines: list[str], func: ast.FunctionDef) -> str:
    """Return the first non-scaffold ###-banner block inside this function."""
    start = func.lineno
    end = (func.end_lineno or len(source_lines))

    banners: list[list[str]] = []
    current: list[str] | None = None
    for ln in range(start, min(end + 1, len(source_lines))):
        line = source_lines[ln].rstrip()
        stripped = line.strip()
        if re.fullmatch(r"#{20,}", stripped):
            if current is None:
                current = []
            else:
                banners.append(current)
                current = None
            continue
        if current is not None and stripped.startswith("#"):
            current.append(stripped.lstrip("#").strip())
    if current:
        banners.append(current)

    for banner in banners:
        cleaned = [l for l in banner if l]
        if not cleaned:
            continue
        if all(l.lower() in _SCAFFOLD_LINES for l in cleaned):
            continue
        return "\n".join(cleaned)
    return ""


def _bare_call_target(call: ast.Call, block_names: set[str]) -> str | None:
    if isinstance(call.func, ast.Name) and call.func.id in block_names:
        return call.func.id
    return None


def _if_calls_a_block(if_stmt: ast.If, block_names: set[str]) -> bool:
    for stmt in if_stmt.body:
        if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
            if _bare_call_target(stmt.value, block_names):
                return True
    return False


def _find_outgoing(func: ast.FunctionDef, block_names: set[str]) -> list[tuple[str, str]]:
    """Recover edges from this block to others.

    Two patterns:
      * Decision-style: top-level `if` statements each contain a bare call to
        another block. Each branch gets a numbered "condition N" label.
      * Normal: scan for `callback=<block_name>` keyword args and for bare
        calls to known block functions.
    """
    edges: list[tuple[str, str]] = []
    seen: set[str] = set()

    decision_like = any(
        isinstance(s, ast.If) and _if_calls_a_block(s, block_names) for s in func.body
    )

    if decision_like:
        idx = 0
        for stmt in func.body:
            if isinstance(stmt, ast.If):
                idx += 1
                for inner in stmt.body:
                    if isinstance(inner, ast.Expr) and isinstance(inner.value, ast.Call):
                        target = _bare_call_target(inner.value, block_names)
                        if target and target not in seen:
                            edges.append((target, f"condition {idx}"))
                            seen.add(target)
            elif isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
                target = _bare_call_target(stmt.value, block_names)
                if target and target not in seen and target != func.name:
                    idx += 1
                    edges.append((target, f"condition {idx}"))
                    seen.add(target)
    else:
        for node in ast.walk(func):
            if not isinstance(node, ast.Call):
                continue
            for kw in node.keywords:
                if kw.arg == "callback" and isinstance(kw.value, ast.Name):
                    name = kw.value.id
                    if name in block_names and name not in seen:
                        edges.append((name, ""))
                        seen.add(name)
            target = _bare_call_target(node, block_names)
            if target and target not in seen and target != func.name:
                edges.append((target, ""))
                seen.add(target)
    return edges


def parse_playbook(path: Path) -> tuple[dict[str, Block], str]:
    source = path.read_text()
    # 1-indexed source line buffer to match ast lineno values.
    source_lines = [""] + source.splitlines()
    tree = ast.parse(source)

    block_funcs: list[ast.FunctionDef] = []
    for node in tree.body:
        if not isinstance(node, ast.FunctionDef):
            continue
        if node.name in ("on_start", "on_finish") or any(
            _is_playbook_block_decorator(d) for d in node.decorator_list
        ):
            block_funcs.append(node)

    if not block_funcs:
        raise SystemExit(f"no playbook blocks found in {path}")

    block_names = {f.name for f in block_funcs}
    blocks: dict[str, Block] = {}
    for func in block_funcs:
        blocks[func.name] = Block(
            name=func.name,
            type=_detect_block_type(func),
            description=_extract_description(source_lines, func),
            outgoing=_find_outgoing(func, block_names),
            lineno=func.lineno,
        )

    # Connect leaf nodes that are reachable from on_start back to on_finish,
    # so the main flow terminates cleanly. Unreachable blocks (defined in the
    # file but never called) are left disconnected and styled distinctly later.
    if "on_finish" in blocks and "on_start" in blocks:
        reachable = reachable_from(blocks, "on_start")
        for name, b in blocks.items():
            if name == "on_finish" or b.outgoing or name not in reachable:
                continue
            b.outgoing.append(("on_finish", ""))

    # Title comes from the filename ("Active_Directory_Disable_Account_Dispatch.py"
    # → "Active Directory Disable Account Dispatch"). Full description is the
    # module docstring, used as the explanatory paragraph under the title.
    title = path.stem.replace("_", " ").strip()
    title = " ".join(w if w.isupper() else w[:1].upper() + w[1:] for w in title.split())
    description = ast.get_docstring(tree) or ""
    return blocks, title, description


def reachable_from(blocks: dict[str, Block], start: str) -> set[str]:
    """Forward BFS — which blocks can be reached from `start`?"""
    if start not in blocks:
        return set()
    seen = {start}
    queue = [start]
    while queue:
        cur = queue.pop(0)
        for tgt, _ in blocks[cur].outgoing:
            if tgt in blocks and tgt not in seen:
                seen.add(tgt)
                queue.append(tgt)
    return seen


# ---------------------------------------------------------------------------
# Markdown — minimal parser for tables, headings, lists, paragraphs,
# inline bold/italic/code. Enough for SOAR description banners.
# ---------------------------------------------------------------------------


def parse_markdown(text: str) -> list[tuple]:
    """Return a list of block tuples.

    Block kinds:
      ('heading', level:int, text:str)
      ('para',    text:str)
      ('list',    items:list[str])
      ('table',   header:list[str] | None, rows:list[list[str]])
    """
    lines = text.split("\n")
    out: list[tuple] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        if not stripped:
            i += 1
            continue

        # Heading
        if stripped.startswith("#"):
            hashes = len(stripped) - len(stripped.lstrip("#"))
            if 1 <= hashes <= 6 and (len(stripped) == hashes or stripped[hashes] == " "):
                out.append(("heading", hashes, stripped[hashes:].strip()))
                i += 1
                continue

        # Table — consecutive lines starting with `|`
        if stripped.startswith("|"):
            tbl: list[str] = []
            while i < len(lines) and lines[i].strip().startswith("|"):
                tbl.append(lines[i].strip())
                i += 1
            rows = [[c.strip() for c in row.strip("|").split("|")] for row in tbl]
            if len(rows) >= 2 and all(
                re.fullmatch(r":?-{2,}:?", c) for c in rows[1] if c
            ):
                out.append(("table", rows[0], rows[2:]))
            else:
                out.append(("table", None, rows))
            continue

        # Unordered list
        if stripped.startswith(("- ", "* ", "+ ")):
            items: list[str] = []
            while i < len(lines) and lines[i].strip().startswith(("- ", "* ", "+ ")):
                items.append(lines[i].strip()[2:])
                i += 1
            out.append(("list", items))
            continue

        # Paragraph — accumulate until blank or structured line
        para = [stripped]
        i += 1
        while i < len(lines):
            nxt = lines[i].strip()
            if not nxt or nxt.startswith(("|", "- ", "* ", "+ ", "#")):
                break
            para.append(nxt)
            i += 1
        out.append(("para", " ".join(para)))

    return out


_INLINE_BOLD = re.compile(r"\*\*([^*]+)\*\*|__([^_]+)__")
_INLINE_ITALIC = re.compile(r"(?<![\*\w])\*([^*\n]+)\*(?!\*)|(?<![_\w])_([^_\n]+)_(?!_)")
_INLINE_CODE = re.compile(r"`([^`]+)`")


def inline_to_html(text: str) -> str:
    """Render inline markdown into XML-safe HTML."""
    out = _xml_escape(text, {'"': "&quot;"})
    out = _INLINE_BOLD.sub(lambda m: f"<b>{m.group(1) or m.group(2)}</b>", out)
    out = _INLINE_ITALIC.sub(lambda m: f"<i>{m.group(1) or m.group(2)}</i>", out)
    out = _INLINE_CODE.sub(
        lambda m: (
            f'<code style="background:{COLOR_CODE_BG};padding:1px 4px;'
            f'border-radius:3px;font-family:monospace;font-size:9px;">{m.group(1)}</code>'
        ),
        out,
    )
    return out


def inline_to_text(text: str) -> str:
    """Strip inline markdown markers, leaving plain text — used as a fallback."""
    out = _INLINE_BOLD.sub(lambda m: m.group(1) or m.group(2), text)
    out = _INLINE_ITALIC.sub(lambda m: m.group(1) or m.group(2), out)
    out = _INLINE_CODE.sub(lambda m: m.group(1), out)
    return out


def md_to_html(text: str) -> str:
    """Render a description's markdown into draw.io-compatible HTML."""
    out_parts: list[str] = []
    for block in parse_markdown(text):
        kind = block[0]
        if kind == "heading":
            _, level, content = block
            size = max(14 - (level - 1), 11)
            out_parts.append(
                f'<div style="font-size:{size}px;font-weight:{FONT_WEIGHT_BOLD};'
                f'margin-top:6px;color:{COLOR_NOTE_TEXT};">'
                f'{inline_to_html(content)}</div>'
            )
        elif kind == "para":
            out_parts.append(
                f'<div style="margin-top:4px;line-height:1.5;">'
                f'{inline_to_html(block[1])}</div>'
            )
        elif kind == "list":
            items = "".join(f"<li>{inline_to_html(it)}</li>" for it in block[1])
            out_parts.append(
                f'<ul style="margin:4px 0 0 16px;padding:0;line-height:1.5;">'
                f'{items}</ul>'
            )
        elif kind == "table":
            _, header, rows = block
            cells_html = (
                '<table cellspacing="0" cellpadding="4" '
                f'style="border-collapse:collapse;margin-top:6px;width:100%;'
                f'font-size:10px;border:1px solid {COLOR_TABLE_BORDER};">'
            )
            if header:
                cells_html += "<thead><tr>"
                for h in header:
                    cells_html += (
                        f'<th style="border:1px solid {COLOR_TABLE_BORDER};'
                        f'background:{COLOR_TABLE_HEADER_BG};padding:5px 7px;'
                        f'text-align:left;font-weight:{FONT_WEIGHT_BOLD};">'
                        f'{inline_to_html(h)}</th>'
                    )
                cells_html += "</tr></thead>"
            cells_html += "<tbody>"
            for row in rows:
                cells_html += "<tr>"
                for cell in row:
                    cells_html += (
                        f'<td style="border:1px solid {COLOR_TABLE_BORDER};'
                        f'padding:5px 7px;">{inline_to_html(cell)}</td>'
                    )
                cells_html += "</tr>"
            cells_html += "</tbody></table>"
            out_parts.append(cells_html)
    return "".join(out_parts)


def estimate_note_height(text: str, content_width: float) -> float:
    """Approximate pixel height needed to render this markdown in a note.

    Used by both the draw.io and reportlab paths to size sticky notes so
    they don't overflow. Generous — markdown tables in particular render
    taller than a naive line count suggests because of cell padding.
    """
    header_h = 28
    pad_top = 14
    pad_bottom = 18  # bottom breathing room so content never kisses the edge
    line_h = 15
    char_w = 5.5
    total = header_h + pad_top + pad_bottom

    chars_per_line = max(20, int((content_width - 28) / char_w))
    for block in parse_markdown(text):
        kind = block[0]
        if kind == "heading":
            total += 22
        elif kind == "para":
            text_len = len(inline_to_text(block[1]))
            lines = max(1, (text_len + chars_per_line - 1) // chars_per_line)
            total += lines * line_h + 6
        elif kind == "list":
            for item in block[1]:
                text_len = len(inline_to_text(item)) + 2
                lines = max(1, (text_len + chars_per_line - 1) // chars_per_line)
                total += lines * line_h + 2
            total += 6
        elif kind == "table":
            _, header, rows = block
            n_rows = (1 if header else 0) + len(rows)
            # Tables get extra: per-row vertical padding + a top/bottom margin.
            total += n_rows * 24 + 12
    return max(80.0, total)


# ---------------------------------------------------------------------------
# Layout
# ---------------------------------------------------------------------------

NODE_W = 220
NODE_H = 76
SWATCH_W = 0
NOTE_W = 240
NOTE_MIN_H = 80
ROW_H = 150
COL_W = 280
X_ORIGIN = 280
Y_ORIGIN = 140
NOTE_GAP = 20


def _compute_ranks(blocks: dict[str, Block], start: str) -> dict[str, int]:
    """Longest path from start, computed by fixpoint."""
    ranks: dict[str, int] = {start: 0}
    for _ in range(200):
        changed = False
        for name, b in blocks.items():
            if name not in ranks:
                continue
            for tgt, _ in b.outgoing:
                if tgt not in blocks:
                    continue
                new_rank = ranks[name] + 1
                if tgt not in ranks or ranks[tgt] < new_rank:
                    ranks[tgt] = new_rank
                    changed = True
        if not changed:
            break
    for name in blocks:
        ranks.setdefault(name, 0)
    return ranks


def compute_layout(blocks: dict[str, Block]) -> dict[str, tuple[float, float]]:
    start = "on_start" if "on_start" in blocks else next(iter(blocks))
    reach = reachable_from(blocks, start)

    main = {n: b for n, b in blocks.items() if n in reach}
    orphans = [n for n in blocks if n not in reach]

    main_pos = _layout_dag(main, start) if main else {}
    positions: dict[str, tuple[float, float]] = dict(main_pos)

    # Place orphans below the main flow as a vertical list — each on its own
    # row with room for its description note alongside.
    if orphans:
        if main_pos:
            bottom_y = max(p[1] for p in main_pos.values()) + ROW_H + 40
            left_x = min(p[0] for p in main_pos.values())
        else:
            bottom_y = Y_ORIGIN
            left_x = X_ORIGIN
        for i, name in enumerate(orphans):
            positions[name] = (left_x, bottom_y + i * ROW_H)
    return positions


def _layout_dag(blocks: dict[str, Block], start: str) -> dict[str, tuple[float, float]]:
    ranks = _compute_ranks(blocks, start)

    by_rank: dict[int, list[str]] = {}
    for name, r in ranks.items():
        by_rank.setdefault(r, []).append(name)

    parents: dict[str, list[str]] = {n: [] for n in blocks}
    for n, b in blocks.items():
        for t, _ in b.outgoing:
            if t in parents:
                parents[t].append(n)

    x_pos: dict[str, float] = {}
    MIN_SEP = COL_W

    for r in sorted(by_rank.keys()):
        candidates = []
        for name in by_rank[r]:
            placed = [p for p in parents[name] if p in x_pos]
            pref = sum(x_pos[p] for p in placed) / len(placed) if placed else 0.0
            candidates.append((pref, name))
        candidates.sort()
        last_x: float | None = None
        for pref, name in candidates:
            if last_x is not None and pref < last_x + MIN_SEP:
                pref = last_x + MIN_SEP
            x_pos[name] = pref
            last_x = pref

    min_x = min(x_pos.values()) if x_pos else 0.0
    return {
        name: (X_ORIGIN + (x - min_x), Y_ORIGIN + ranks[name] * ROW_H)
        for name, x in x_pos.items()
    }


# ---------------------------------------------------------------------------
# draw.io XML emission
# ---------------------------------------------------------------------------


def _block_style(btype: str, orphan: bool = False) -> str:
    accent = TYPE_ACCENT.get(btype, "#94A3B8")
    stroke = COLOR_ORPHAN_STROKE if orphan else accent
    common = (
        "whiteSpace=wrap;html=1;"
        f"fillColor={COLOR_BLOCK_BG};strokeColor={stroke};strokeWidth=2;"
        f"fontColor={COLOR_TEXT_PRIMARY};fontSize={FONT_SIZE_BODY};"
        "shadow=1;align=center;verticalAlign=middle;"
    )
    if orphan:
        common += "dashed=1;dashPattern=4 4;"
    if btype == "DECISION":
        return "shape=parallelogram;perimeter=parallelogramPerimeter;" + common
    if btype == "FILTER":
        return "shape=trapezoid;perimeter=trapezoidPerimeter;" + common
    if btype in ("START", "END"):
        return "rounded=1;arcSize=50;" + common
    # Standard rounded rect — Splunk's borderRadius=4 in absolute px.
    return f"rounded=1;absoluteArcSize=1;arcSize={SPLUNK_BORDER_RADIUS};" + common


def _block_value_html(btype: str, name: str, is_decision: bool = False) -> str:
    accent = TYPE_ACCENT.get(btype, "#94A3B8")
    title = _xml_escape(name.replace("_", " "), {'"': "&quot;"})
    btype_text = _xml_escape(btype)
    return (
        f'<div style="font-family:{SPLUNK_FONT_STACK};font-size:10px;'
        f'color:{accent};font-weight:{FONT_WEIGHT_BOLD};'
        f'letter-spacing:0.16em;text-transform:uppercase;">{btype_text}</div>'
        f'<div style="font-family:{SPLUNK_FONT_STACK};margin-top:4px;'
        f'font-size:{FONT_SIZE_LARGE}px;font-weight:{FONT_WEIGHT_BOLD};'
        f'color:{COLOR_TEXT_PRIMARY};line-height:1.25;">{title}</div>'
    )


def _note_style(accent: str = None) -> str:
    """Sticky-note card. The accent shows as a thicker top border, applied
    via a left-side strokeColor — to avoid the rounded-corner mismatch that
    an inner HTML strip would cause."""
    stroke = accent or COLOR_NOTE_BORDER
    return (
        "rounded=1;arcSize=6;whiteSpace=wrap;html=1;"
        f"fillColor={COLOR_NOTE_BG};strokeColor={stroke};"
        f"fontColor={COLOR_NOTE_TEXT};fontSize=10;align=left;verticalAlign=top;"
        "spacing=0;shadow=0;strokeWidth=1;"
    )


def _note_value_html(description: str, accent: str) -> str:
    body = md_to_html(description) if description else ""
    return (
        f'<div style="font-family:{SPLUNK_FONT_STACK};padding:12px 14px 14px 14px;">'
        f'<div style="font-size:10px;color:{COLOR_NOTE_MUTED};'
        f'font-weight:{FONT_WEIGHT_BOLD};letter-spacing:0.16em;'
        f'text-transform:uppercase;">Description</div>'
        f'<div style="margin-top:8px;color:{COLOR_NOTE_TEXT};font-size:11px;'
        f'font-weight:{FONT_WEIGHT_NORMAL};line-height:1.5;">{body}</div>'
        f'</div>'
    )


_CONDITION_RE = re.compile(r"condition\s+(\d+)", re.IGNORECASE)


def _condition_color(label: str) -> str | None:
    m = _CONDITION_RE.search(label or "")
    if not m:
        return None
    return CONDITION_ACCENT.get(int(m.group(1)))


def _edge_style(label: str = "", side_route: bool = False) -> str:
    """Edge style — geometry + stroke only. The label is an HTML pill in the
    cell's `value`. `labelBackgroundColor` is set to the page background so
    the edge line is occluded behind the pill (otherwise the line would
    draw through the pill text).

    When `side_route=True` the edge exits the source from its right side and
    enters the target from its right side too — used for multi-rank edges
    so they bend around intervening blocks instead of cutting through them.
    """
    if side_route:
        exit_entry = (
            "exitX=1;exitY=0.5;exitDx=0;exitDy=0;"
            "entryX=1;entryY=0.5;entryDx=0;entryDy=0;"
        )
    else:
        exit_entry = (
            "exitX=0.5;exitY=1;exitDx=0;exitDy=0;"
            "entryX=0.5;entryY=0;entryDx=0;entryDy=0;"
        )
    return (
        "edgeStyle=orthogonalEdgeStyle;rounded=1;orthogonalLoop=1;jettySize=auto;"
        "html=1;endArrow=classic;endFill=1;"
        f"{exit_entry}"
        f"strokeColor={COLOR_EDGE};strokeWidth=1.5;"
        f"fontColor={COLOR_EDGE_LABEL_TEXT};fontSize={FONT_SIZE_SMALL};"
        f"fontFamily={SPLUNK_FONT_STACK};"
        f"labelBackgroundColor={COLOR_BG};labelBorderColor=none;"
    )


def _edge_label_html(label: str) -> str:
    """Return the edge's value markup — a filled pill for condition labels,
    plain text otherwise."""
    if not label:
        return ""
    cond = _condition_color(label)
    if cond:
        return (
            f'<div style="display:inline-block;background:{cond};'
            f'color:#FFFFFF;padding:3px 12px;border-radius:999px;'
            f'font-weight:{FONT_WEIGHT_BOLD};font-size:10px;letter-spacing:0.02em;'
            f'font-family:{SPLUNK_FONT_STACK};">{xml_escape(label)}</div>'
        )
    return xml_escape(label)


def _note_connector_style(side: str = "right") -> str:
    """Dashed connector from block edge to its sticky note.

    `side` is the side of the block the note sits on ("left" or "right"),
    which controls which block face the connector exits from. We use a
    plain (non-orthogonal) line — when block and note are roughly aligned,
    that produces a clean straight or gentle diagonal instead of the kinked
    L-bend that orthogonal routing creates near short vertical offsets.
    """
    if side == "left":
        exit_attrs = "exitX=0;exitY=0.5;exitDx=0;exitDy=0;entryX=1;entryY=0.5;"
    else:
        exit_attrs = "exitX=1;exitY=0.5;exitDx=0;exitDy=0;entryX=0;entryY=0.5;"
    return (
        "endArrow=none;startArrow=none;dashed=1;dashPattern=2 3;html=1;"
        f"{exit_attrs}entryDx=0;entryDy=0;"
        f"strokeColor={COLOR_TEXT_SECONDARY};strokeWidth=1;opacity=50;"
    )


def _compute_note_positions(
    blocks: dict[str, Block],
    positions: dict[str, tuple[float, float]],
    left_x: float,
    right_x: float,
    main_names: set[str],
) -> dict[str, tuple[float, float, float, str]]:
    """For each block with a description, return (x, y, height, side).

    Notes go to the same side of the workflow as their block, so the dashed
    connector never crosses through another column of the main flow. Center-
    column blocks (those at the workflow centerline) alternate left/right
    so both sides stay populated.
    """
    described = sorted(
        (n for n, b in blocks.items() if b.description and n in main_names),
        key=lambda n: positions[n][1],
    )
    if not described:
        return {}

    # --- Classify each main-flow block as left-branch / right-branch / spine.
    # A block is branched if another block exists at the same y-rank (i.e.
    # they're siblings of a decision). Descendants of a branched block
    # inherit its side, so the dashed connector to its note never crosses
    # the sibling column. Multi-parent merges become "spine".
    block_side: dict[str, str] = {}
    by_y: dict[float, list[str]] = {}
    for n in main_names:
        by_y.setdefault(positions[n][1], []).append(n)
    for y, names in by_y.items():
        if len(names) == 1:
            block_side[names[0]] = "spine"
        else:
            ordered = sorted(names, key=lambda n: positions[n][0])
            for i, n in enumerate(ordered):
                if i == 0:
                    block_side[n] = "left"
                elif i == len(ordered) - 1:
                    block_side[n] = "right"
                else:
                    block_side[n] = "spine"
    # Propagate: a single-rank descendant inherits its parent's side unless
    # parents disagree (then spine).
    parent_of: dict[str, list[str]] = {n: [] for n in main_names}
    for n in main_names:
        for tgt, _ in blocks[n].outgoing:
            if tgt in main_names:
                parent_of[tgt].append(n)
    # Walk in y-order so parents are settled before children.
    for n in sorted(main_names, key=lambda n: positions[n][1]):
        if block_side[n] != "spine":
            continue
        parent_sides = {block_side[p] for p in parent_of[n]}
        parent_sides.discard("spine")
        if len(parent_sides) == 1:
            block_side[n] = parent_sides.pop()

    placed: dict[str, tuple[float, float, float, str]] = {}
    cursor_right = -1e9
    cursor_left = -1e9
    center_alternate_idx = 0

    for name in described:
        block_x, block_y = positions[name]
        height = estimate_note_height(blocks[name].description, NOTE_W)
        ideal_y = block_y + NODE_H / 2 - height / 2

        cls = block_side[name]
        if cls == "left":
            side = "left"
        elif cls == "right":
            side = "right"
        else:
            side = "right" if center_alternate_idx % 2 == 0 else "left"
            center_alternate_idx += 1

        if side == "right":
            y = max(ideal_y, cursor_right + NOTE_GAP)
            placed[name] = (right_x, y, height, "right")
            cursor_right = y + height
        else:
            y = max(ideal_y, cursor_left + NOTE_GAP)
            placed[name] = (left_x, y, height, "left")
            cursor_left = y + height

    # Orphan notes go directly to the right of each orphan block, aligned
    # so the dashed connector is a straight horizontal line.
    for name, b in blocks.items():
        if not b.description or name in main_names:
            continue
        block_x, block_y = positions[name]
        height = estimate_note_height(b.description, NOTE_W)
        note_y = block_y + NODE_H / 2 - height / 2
        placed[name] = (block_x + NODE_W + 30, note_y, height, "right")
    return placed


def emit_drawio(
    blocks: dict[str, Block],
    positions: dict[str, tuple[float, float]],
    title: str,
    description: str = "",
) -> str:
    cells: list[str] = []
    cells.append('<mxCell id="0" />')
    cells.append('<mxCell id="1" parent="0" />')

    id_for = {name: f"b{i}" for i, name in enumerate(blocks)}

    start_name = "on_start" if "on_start" in blocks else next(iter(blocks))
    reach = reachable_from(blocks, start_name)
    orphan_names = set(n for n in blocks if n not in reach and n != start_name)
    main_names = set(n for n in blocks if n in reach or n == start_name)

    # Workflow extent (main flow only — orphans float below)
    main_xs = [positions[n][0] for n in main_names]
    main_min_x = min(main_xs)
    main_max_x = max(x + NODE_W for x in main_xs)
    GUTTER = 60
    left_note_x = main_min_x - NOTE_W - GUTTER

    # Shift everything right so left-side notes don't render off-page.
    DESIRED_LEFT = 60
    if left_note_x < DESIRED_LEFT:
        shift_x = DESIRED_LEFT - left_note_x
        positions = {n: (x + shift_x, y) for n, (x, y) in positions.items()}
        main_xs = [positions[n][0] for n in main_names]
        main_min_x = min(main_xs)
        main_max_x = max(x + NODE_W for x in main_xs)
        left_note_x = main_min_x - NOTE_W - GUTTER
    right_note_x = main_max_x + GUTTER

    # Shift everything DOWN so the title + description header above the
    # workflow sits in positive y space, AND the header card + workflow card
    # borders don't overlap.
    desc_line_count = (len(description) // 80 + description.count("\n") + 1) if description else 0
    header_h = (40 if title else 0) + (desc_line_count * 16) + (24 if description else 0)
    # title sits inside the header card with SECTION_PAD on top
    HEADER_TOP_MARGIN = PAGE_OUTER_MARGIN + 24 + SECTION_PAD
    header_card_bottom = HEADER_TOP_MARGIN + header_h + SECTION_PAD
    CARD_GAP = 20
    # first block sits 40 px below the top of the workflow card border
    workflow_top_target = header_card_bottom + CARD_GAP + 40
    current_top = min(p[1] for p in positions.values())
    if current_top < workflow_top_target:
        shift_y = workflow_top_target - current_top
        positions = {n: (x, y + shift_y) for n, (x, y) in positions.items()}

    note_positions = _compute_note_positions(
        blocks, positions, left_note_x, right_note_x, main_names,
    )

    # Page dimensions — sized to fit content so draw.io doesn't paginate.
    content_right = right_note_x + NOTE_W
    for n in orphan_names:
        nx, ny, nh, _ = note_positions.get(n, (positions[n][0] + NODE_W, 0, 0, "right"))
        content_right = max(content_right, nx + NOTE_W)
    page_w = int(content_right + 60)
    all_ys = [y + NODE_H for _, y in positions.values()] + [
        ny + nh for _, ny, nh, _ in note_positions.values()
    ]
    content_bottom = max(all_ys)
    # Positions are already shifted down to clear the header, so page_h only
    # needs room for the workflow-card bottom padding (40) + page margin (24).
    page_h = int(content_bottom + 64)

    # --- Header card border (around title + description) ---
    if main_names and (title or description):
        header_x = left_note_x - SECTION_PAD
        header_y = HEADER_TOP_MARGIN - SECTION_PAD
        header_w = (right_note_x + NOTE_W) - header_x + SECTION_PAD
        header_h_card = header_h + SECTION_PAD * 2
        cells.append(
            f'<mxCell id="header-card" value="" '
            f'style="rounded=1;absoluteArcSize=1;arcSize={SECTION_CARD_RADIUS};'
            f'fillColor=none;strokeColor={COLOR_SECTION_BORDER};strokeWidth=2;'
            f'rotatable=0;movable=0;resizable=0;deletable=0;editable=0;'
            f'connectable=0;" vertex="1" parent="1">'
            f'<mxGeometry x="{header_x:.0f}" y="{header_y:.0f}" '
            f'width="{header_w:.0f}" height="{header_h_card:.0f}" '
            f'as="geometry" /></mxCell>'
        )

    # --- Workflow card: dot-grid background + bordering rectangle ---
    if main_names:
        dg_top = min(positions[n][1] for n in main_names) - 40
        all_block_ys = [positions[n][1] + NODE_H for n in blocks]
        all_note_bottoms = [ny + nh for _, ny, nh, _ in note_positions.values()]
        dg_bottom = max(all_block_ys + all_note_bottoms) + 40
        # Use the same horizontal padding as the header card so the two card
        # borders line up vertically.
        dg_left = left_note_x - SECTION_PAD
        dg_right = right_note_x + NOTE_W + SECTION_PAD
        dg_w = int(dg_right - dg_left)
        dg_h = int(dg_bottom - dg_top)
        svg = (
            f'<svg xmlns="http://www.w3.org/2000/svg" width="{dg_w}" '
            f'height="{dg_h}">'
            f'<defs><pattern id="dg" x="0" y="0" '
            f'width="{DOT_GRID_SPACING}" height="{DOT_GRID_SPACING}" '
            f'patternUnits="userSpaceOnUse">'
            f'<circle cx="2" cy="2" r="{DOT_GRID_RADIUS}" '
            f'fill="{COLOR_DOT_GRID}"/></pattern></defs>'
            f'<rect width="100%" height="100%" fill="url(#dg)"/></svg>'
        )
        img_uri = "data:image/svg+xml," + _url_quote(svg, safe="")
        cells.append(
            f'<mxCell id="dot-grid-bg" value="" '
            f'style="shape=image;image={img_uri};imageAspect=0;'
            f'strokeColor=none;rotatable=0;movable=0;resizable=0;'
            f'deletable=0;editable=0;connectable=0;" '
            f'vertex="1" parent="1">'
            f'<mxGeometry x="{dg_left:.0f}" y="{dg_top:.0f}" '
            f'width="{dg_w}" height="{dg_h}" as="geometry" /></mxCell>'
        )
        # Border around the workflow card (drawn over the dot grid)
        cells.append(
            f'<mxCell id="workflow-card" value="" '
            f'style="rounded=1;absoluteArcSize=1;arcSize={SECTION_CARD_RADIUS};'
            f'fillColor=none;strokeColor={COLOR_SECTION_BORDER};strokeWidth=2;'
            f'rotatable=0;movable=0;resizable=0;deletable=0;editable=0;'
            f'connectable=0;" vertex="1" parent="1">'
            f'<mxGeometry x="{dg_left:.0f}" y="{dg_top:.0f}" '
            f'width="{dg_w}" height="{dg_h}" as="geometry" /></mxCell>'
        )

    # --- Playbook title + full description (top of the page) ---
    if title or description:
        header_x = left_note_x
        top_y = HEADER_TOP_MARGIN
        title_html = f'<div style="font-family:{SPLUNK_FONT_STACK};">'
        if title:
            title_html += (
                f'<div style="font-size:{FONT_SIZE_SMALL}px;'
                f'color:{COLOR_TEXT_SECONDARY};font-weight:{FONT_WEIGHT_BOLD};'
                f'letter-spacing:0.18em;text-transform:uppercase;">'
                f'Splunk SOAR Playbook</div>'
                f'<div style="margin-top:4px;font-size:{FONT_SIZE_XXL}px;'
                f'font-weight:{FONT_WEIGHT_HEAVY};color:{COLOR_TEXT_PRIMARY};'
                f'letter-spacing:-0.01em;">{xml_escape(title)}</div>'
            )
        if description:
            desc_html = (
                xml_escape(description)
                .replace("\n\n", "<br/><br/>")
                .replace("\n", "<br/>")
            )
            title_html += (
                f'<div style="margin:12px 0 0 0;font-size:{FONT_SIZE_BODY}px;'
                f'font-weight:{FONT_WEIGHT_NORMAL};line-height:1.5;'
                f'color:{COLOR_TEXT_BODY};max-width:760px;">{desc_html}</div>'
            )
        title_html += "</div>"
        header_w = (right_note_x + NOTE_W) - header_x
        cells.append(
            f'<mxCell id="title2" value="{xml_escape(title_html)}" '
            f'style="text;html=1;align=left;verticalAlign=top;" '
            f'vertex="1" parent="1">'
            f'<mxGeometry x="{header_x:.0f}" y="{top_y:.0f}" '
            f'width="{header_w:.0f}" height="{header_h:.0f}" as="geometry" /></mxCell>'
        )

    # --- "Unreachable blocks" subtle label (no container) ---
    if orphan_names:
        oxs = [positions[n][0] for n in orphan_names]
        oys = [positions[n][1] for n in orphan_names]
        label_html = (
            f'<div style="font-family:{SPLUNK_FONT_STACK};'
            f'font-size:{FONT_SIZE_SMALL}px;color:{COLOR_TEXT_SECONDARY};'
            f'font-weight:{FONT_WEIGHT_BOLD};letter-spacing:0.18em;'
            f'text-transform:uppercase;border-top:1px dashed {COLOR_BLOCK_BORDER};'
            f'padding-top:8px;">'
            f'Unreachable Blocks &nbsp;&middot;&nbsp; '
            f'<span style="font-weight:{FONT_WEIGHT_NORMAL};text-transform:none;'
            f'letter-spacing:0;color:{COLOR_TEXT_SECONDARY};">'
            f'defined but not called from on_start</span></div>'
        )
        cells.append(
            f'<mxCell id="orphan-label" value="{xml_escape(label_html)}" '
            f'style="text;html=1;align=left;verticalAlign=middle;" '
            f'vertex="1" parent="1">'
            f'<mxGeometry x="{min(oxs):.0f}" y="{min(oys) - 36:.0f}" '
            f'width="600" height="24" as="geometry" /></mxCell>'
        )

    # --- Blocks ---
    for name, b in blocks.items():
        x, y = positions[name]
        cell_id = id_for[name]
        orphan = name in orphan_names
        is_decision = b.type == "DECISION"
        cells.append(
            f'<mxCell id="{cell_id}" '
            f'value="{xml_escape(_block_value_html(b.type, name, is_decision))}" '
            f'style="{_block_style(b.type, orphan=orphan)}" vertex="1" parent="1">'
            f'<mxGeometry x="{x:.0f}" y="{y:.0f}" '
            f'width="{NODE_W}" height="{NODE_H}" as="geometry" /></mxCell>'
        )

    # --- Notes + dashed connectors ---
    for name, (nx, ny, nh, side) in note_positions.items():
        b = blocks[name]
        accent = TYPE_ACCENT.get(b.type, "#94A3B8")
        cell_id = id_for[name]
        cells.append(
            f'<mxCell id="{cell_id}-note" '
            f'value="{xml_escape(_note_value_html(b.description, accent))}" '
            f'style="{_note_style(accent)}" vertex="1" parent="1">'
            f'<mxGeometry x="{nx:.0f}" y="{ny:.0f}" '
            f'width="{NOTE_W}" height="{nh:.0f}" as="geometry" /></mxCell>'
        )
        cells.append(
            f'<mxCell id="{cell_id}-noteline" '
            f'style="{_note_connector_style(side)}" edge="1" parent="1" '
            f'source="{cell_id}" target="{cell_id}-note">'
            f'<mxGeometry relative="1" as="geometry" /></mxCell>'
        )

    # Edges. Skip edges that originate from unreachable blocks so they
    # don't cut across the main flow with stray labels.
    edge_ranks = _compute_ranks(blocks, start_name)
    edge_idx = 0

    # Count labeled outgoing edges per source so multiple condition pills
    # can be spread horizontally beneath the same block.
    labeled_per_source: dict[str, int] = {}
    for name, b in blocks.items():
        if name in orphan_names:
            continue
        for tgt, lbl in b.outgoing:
            if tgt in blocks and lbl:
                labeled_per_source[name] = labeled_per_source.get(name, 0) + 1

    PILL_W = 78  # nominal — pill cells are sized for ~"condition 1"
    PILL_H = 16
    PILL_GAP = 6  # horizontal gap when multiple pills share a source

    for name, b in blocks.items():
        if name in orphan_names:
            continue
        labeled_seen = 0
        total_labels = labeled_per_source.get(name, 0)
        for target, label in b.outgoing:
            if target not in blocks:
                continue
            edge_idx += 1
            edge_id = f"e{edge_idx}"
            rank_diff = edge_ranks.get(target, 0) - edge_ranks.get(name, 0)
            multi = rank_diff > 1
            # Edge with no embedded label — the line draws on its own.
            cells.append(
                f'<mxCell id="{edge_id}" value="" '
                f'style="{_edge_style("", side_route=multi)}" '
                f'edge="1" parent="1" '
                f'source="{id_for[name]}" target="{id_for[target]}">'
                f'<mxGeometry relative="1" as="geometry" /></mxCell>'
            )
            # Standalone pill vertex at the source's bottom edge — a real
            # cell with its own bounds, fully opaque, guaranteed to occlude
            # the edge line behind it. Multiple pills from one source spread
            # horizontally so they don't overlap each other.
            if label:
                sx, sy = positions[name]
                accent = _condition_color(label) or COLOR_EDGE_LABEL_BG
                if total_labels > 1:
                    span = total_labels * PILL_W + (total_labels - 1) * PILL_GAP
                    px = (sx + NODE_W / 2 - span / 2
                          + labeled_seen * (PILL_W + PILL_GAP))
                else:
                    px = sx + NODE_W / 2 - PILL_W / 2
                py = sy + NODE_H + 8
                pill_style = (
                    "rounded=1;absoluteArcSize=1;arcSize=20;"
                    f"fillColor={accent};strokeColor={accent};"
                    f"fontColor=#FFFFFF;fontStyle=1;fontSize=10;"
                    f"fontFamily={SPLUNK_FONT_STACK};"
                    "html=1;whiteSpace=wrap;align=center;verticalAlign=middle;"
                    "resizable=0;rotatable=0;editable=0;movable=0;"
                    "connectable=0;deletable=0;"
                )
                cells.append(
                    f'<mxCell id="{edge_id}-label" '
                    f'value="{xml_escape(label)}" '
                    f'style="{pill_style}" vertex="1" parent="1">'
                    f'<mxGeometry x="{px:.0f}" y="{py:.0f}" '
                    f'width="{PILL_W}" height="{PILL_H}" as="geometry" />'
                    f'</mxCell>'
                )
                labeled_seen += 1

    body = "\n        ".join(cells)
    diagram_id = uuid.uuid4().hex
    return f"""<mxfile host="app.diagrams.net" type="device">
  <diagram name="Playbook" id="{diagram_id}">
    <mxGraphModel dx="1422" dy="757" grid="1" gridSize="10" guides="1" tooltips="1"
                  connect="1" arrows="1" fold="1" page="1" pageScale="1"
                  pageWidth="{page_w}" pageHeight="{page_h}" math="0" shadow="0"
                  background="{COLOR_BG}">
      <root>
        {body}
      </root>
    </mxGraphModel>
  </diagram>
</mxfile>
"""


# ---------------------------------------------------------------------------
# PDF export — draw.io CLI if available, else self-contained reportlab render
# ---------------------------------------------------------------------------


def _find_drawio_cli() -> str | None:
    cli = shutil.which("drawio")
    if cli:
        return cli
    mac_app = "/Applications/draw.io.app/Contents/MacOS/draw.io"
    if Path(mac_app).exists():
        return mac_app
    return None


def export_pdf_via_drawio(drawio_path: Path, pdf_path: Path) -> bool:
    cli = _find_drawio_cli()
    if not cli:
        return False
    try:
        subprocess.run(
            [cli, "-x", "-f", "pdf", "-o", str(pdf_path), str(drawio_path)],
            check=True,
            capture_output=True,
        )
        return True
    except subprocess.CalledProcessError as exc:
        sys.stderr.write(
            f"drawio CLI failed (exit {exc.returncode}):\n"
            f"{exc.stderr.decode(errors='replace')}\n"
        )
        return False


PAGE_MARGIN = 48
TITLE_HEIGHT = 50


def _wrap_text(canv, text: str, font: str, size: float, max_w: float) -> list[str]:
    """Greedy word-wrap, splitting on whitespace; preserves embedded newlines."""
    lines: list[str] = []
    for paragraph in text.split("\n"):
        if not paragraph:
            lines.append("")
            continue
        words = paragraph.split(" ")
        cur = ""
        for w in words:
            trial = f"{cur} {w}".strip()
            if canv.stringWidth(trial, font, size) <= max_w:
                cur = trial
            else:
                if cur:
                    lines.append(cur)
                cur = w
        if cur:
            lines.append(cur)
    return lines


def _md_inline_to_rl(text: str) -> str:
    """Inline markdown -> reportlab Paragraph markup (<b>, <i>, <font>)."""
    safe = _xml_escape(text)
    safe = _INLINE_BOLD.sub(lambda m: f"<b>{m.group(1) or m.group(2)}</b>", safe)
    safe = _INLINE_ITALIC.sub(lambda m: f"<i>{m.group(1) or m.group(2)}</i>", safe)
    safe = _INLINE_CODE.sub(
        lambda m: (
            f'<font face="Courier" backcolor="{COLOR_CODE_BG}">'
            f' {m.group(1)} </font>'
        ),
        safe,
    )
    return safe


def _draw_note(canv, blocks_module, b: "Block", x: float, y: float, w: float, h: float) -> None:
    """Render one sticky note (cream card with colored top accent + markdown)."""
    from reportlab.lib.colors import HexColor
    from reportlab.lib.styles import ParagraphStyle
    from reportlab.platypus import Paragraph, Table, TableStyle

    accent = HexColor(TYPE_ACCENT.get(b.type, "#94A3B8"))

    # Card body — note border picks up the accent. No inner strip to avoid
    # the rounded-corner mismatch that one would create.
    canv.setFillColor(HexColor(COLOR_NOTE_BG))
    canv.setStrokeColor(accent)
    canv.setLineWidth(1.2)
    canv.roundRect(x, y, w, h, 6, fill=1, stroke=1)

    canv.setFillColor(HexColor(COLOR_NOTE_MUTED))
    canv.setFont("Helvetica-Bold", 7)
    canv.drawString(x + 12, y + h - 18, "DESCRIPTION")

    # Body — render each markdown block in sequence.
    body_style = ParagraphStyle(
        "body",
        fontName="Helvetica",
        fontSize=9,
        leading=12,
        textColor=HexColor(COLOR_NOTE_TEXT),
        spaceAfter=4,
    )
    heading_style = ParagraphStyle(
        "heading",
        fontName="Helvetica-Bold",
        fontSize=10.5,
        leading=14,
        textColor=HexColor(COLOR_NOTE_TEXT),
        spaceAfter=4,
    )
    list_style = ParagraphStyle(
        "list", parent=body_style, leftIndent=12, bulletIndent=2,
    )

    cursor_y = y + h - 30
    body_x = x + 12
    body_w = w - 24
    min_y = y + 12

    for block in parse_markdown(b.description):
        if cursor_y <= min_y:
            break
        kind = block[0]
        if kind == "heading":
            html = _md_inline_to_rl(block[2])
            para = Paragraph(html, heading_style)
            w_used, h_used = para.wrap(body_w, cursor_y - min_y)
            para.drawOn(canv, body_x, cursor_y - h_used)
            cursor_y -= h_used + 2
        elif kind == "para":
            html = _md_inline_to_rl(block[1])
            para = Paragraph(html, body_style)
            w_used, h_used = para.wrap(body_w, cursor_y - min_y)
            para.drawOn(canv, body_x, cursor_y - h_used)
            cursor_y -= h_used + 3
        elif kind == "list":
            for item in block[1]:
                html = "&bull;&nbsp; " + _md_inline_to_rl(item)
                para = Paragraph(html, list_style)
                w_used, h_used = para.wrap(body_w, cursor_y - min_y)
                if h_used > cursor_y - min_y:
                    break
                para.drawOn(canv, body_x, cursor_y - h_used)
                cursor_y -= h_used
            cursor_y -= 3
        elif kind == "table":
            _, header, rows = block
            data: list[list] = []
            if header:
                data.append([Paragraph(_md_inline_to_rl(c), body_style) for c in header])
            for row in rows:
                data.append([Paragraph(_md_inline_to_rl(c), body_style) for c in row])
            if not data:
                continue
            n_cols = max(len(r) for r in data)
            # pad short rows so the table is rectangular
            for r in data:
                while len(r) < n_cols:
                    r.append(Paragraph("", body_style))
            col_w = body_w / n_cols
            tbl = Table(data, colWidths=[col_w] * n_cols, hAlign="LEFT")
            ts = [
                ("GRID", (0, 0), (-1, -1), 0.5, HexColor(COLOR_TABLE_BORDER)),
                ("FONT", (0, 0), (-1, -1), "Helvetica", 9),
                ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
                ("LEFTPADDING", (0, 0), (-1, -1), 5),
                ("RIGHTPADDING", (0, 0), (-1, -1), 5),
                ("TOPPADDING", (0, 0), (-1, -1), 3),
                ("BOTTOMPADDING", (0, 0), (-1, -1), 3),
            ]
            if header:
                ts.extend([
                    ("BACKGROUND", (0, 0), (-1, 0), HexColor(COLOR_TABLE_HEADER_BG)),
                    ("FONT", (0, 0), (-1, 0), "Helvetica-Bold", 9),
                ])
            tbl.setStyle(TableStyle(ts))
            w_used, h_used = tbl.wrap(body_w, cursor_y - min_y)
            if h_used > cursor_y - min_y:
                continue
            tbl.drawOn(canv, body_x, cursor_y - h_used)
            cursor_y -= h_used + 4


def render_pdf(
    blocks: dict[str, Block],
    positions: dict[str, tuple[float, float]],
    title: str,
    pdf_path: Path,
    description: str = "",
) -> bool:
    try:
        from reportlab.lib.colors import HexColor
        from reportlab.pdfgen import canvas as rl_canvas
    except ImportError:
        sys.stderr.write(
            "reportlab not installed. Install with: pip install reportlab\n"
            "Or install draw.io desktop and re-run --pdf to use its export.\n"
        )
        return False

    if not positions:
        return False
    from reportlab.lib.styles import ParagraphStyle
    from reportlab.platypus import Paragraph

    start_name = "on_start" if "on_start" in blocks else next(iter(blocks))
    reach = reachable_from(blocks, start_name)
    orphan_names = set(n for n in blocks if n not in reach and n != start_name)
    main_names = set(n for n in blocks if n in reach or n == start_name)

    main_xs = [positions[n][0] for n in main_names]
    main_min_x = min(main_xs)
    main_max_x = max(x + NODE_W for x in main_xs)

    GUTTER = 60
    left_note_x = main_min_x - NOTE_W - GUTTER
    right_note_x = main_max_x + GUTTER

    note_positions = _compute_note_positions(
        blocks, positions, left_note_x, right_note_x, main_names,
    )

    # Page extent ------------------------------------------------------------
    block_ys = [positions[n][1] for n in blocks]
    content_min_x = left_note_x
    content_max_x = right_note_x + NOTE_W
    note_max_y = max((ny + nh for _, ny, nh, _ in note_positions.values()),
                     default=0)
    block_max_y = max(block_ys) + NODE_H
    content_max_y = max(block_max_y, note_max_y)

    # Header (title + description) needs vertical room.
    header_lines_estimate = 1 + max(0, (len(description) // 80)) if description else 0
    header_h = (40 if title else 0) + (header_lines_estimate * 14) + (16 if description else 0)
    content_min_y = min(block_ys) - 60 - header_h

    page_w = (content_max_x - content_min_x) + 2 * PAGE_MARGIN
    page_h = (content_max_y - content_min_y) + 2 * PAGE_MARGIN

    canv = rl_canvas.Canvas(str(pdf_path), pagesize=(page_w, page_h))

    def to_pdf(mx: float, my: float, h: float = 0.0) -> tuple[float, float]:
        x = PAGE_MARGIN + (mx - content_min_x)
        y = page_h - PAGE_MARGIN - (my - content_min_y) - h
        return x, y

    canv.setFillColor(HexColor(COLOR_BG))
    canv.rect(0, 0, page_w, page_h, fill=1, stroke=0)

    # ----- Header card border (around title + description) -----
    if main_names and (title or description):
        # In reportlab the header text sits at content_min_y .. content_min_y +
        # header_h. The card border just expands by SECTION_PAD on each side.
        header_left_layout = left_note_x - SECTION_PAD
        header_top_layout = content_min_y - SECTION_PAD
        header_bottom_layout = content_min_y + header_h + SECTION_PAD
        hx1, hy1 = to_pdf(header_left_layout, header_bottom_layout)
        hw = (right_note_x + NOTE_W) - header_left_layout + SECTION_PAD
        hh = header_bottom_layout - header_top_layout
        canv.setStrokeColor(HexColor(COLOR_SECTION_BORDER))
        canv.setLineWidth(2)
        canv.roundRect(hx1, hy1, hw, hh, SECTION_CARD_RADIUS,
                       fill=0, stroke=1)

    # ----- Dot grid + workflow card border -----
    if main_names:
        dg_top_layout = min(positions[n][1] for n in main_names) - 40
        all_block_ys = [positions[n][1] + NODE_H for n in blocks]
        all_note_bottoms = [ny + nh for _, ny, nh, _ in note_positions.values()]
        dg_bottom_layout = max(all_block_ys + all_note_bottoms) + 40
        dg_left = left_note_x - SECTION_PAD
        dg_right = right_note_x + NOTE_W + SECTION_PAD
        dx1, dy1 = to_pdf(dg_left, dg_bottom_layout)
        dw = dg_right - dg_left
        dh = dg_bottom_layout - dg_top_layout
        # Dots
        canv.setFillColor(HexColor(COLOR_DOT_GRID))
        canv.setStrokeColor(HexColor(COLOR_DOT_GRID))
        y = dy1 + (DOT_GRID_SPACING / 2)
        while y < dy1 + dh:
            x = dx1 + (DOT_GRID_SPACING / 2)
            while x < dx1 + dw:
                canv.circle(x, y, DOT_GRID_RADIUS, fill=1, stroke=0)
                x += DOT_GRID_SPACING
            y += DOT_GRID_SPACING
        # Workflow card border (on top of dots)
        canv.setStrokeColor(HexColor(COLOR_SECTION_BORDER))
        canv.setLineWidth(2)
        canv.roundRect(dx1, dy1, dw, dh, SECTION_CARD_RADIUS,
                       fill=0, stroke=1)

    # ----- Header (title + full description) -----
    if title or description:
        hx, hy = to_pdf(content_min_x, content_min_y + header_h)
        canv.setFillColor(HexColor(COLOR_TEXT_SECONDARY))
        canv.setFont("Helvetica-Bold", 8)
        canv.drawString(hx, hy + header_h - 18, "SPLUNK SOAR PLAYBOOK")
        if title:
            canv.setFillColor(HexColor(COLOR_TEXT_PRIMARY))
            canv.setFont("Helvetica-Bold", 22)
            t = title
            max_w = page_w - 2 * PAGE_MARGIN
            while canv.stringWidth(t, "Helvetica-Bold", 22) > max_w and len(t) > 12:
                t = t[:-1]
            if t != title:
                t = t.rstrip() + "…"
            canv.drawString(hx, hy + header_h - 44, t)
        if description:
            desc_style = ParagraphStyle(
                "desc", fontName="Helvetica", fontSize=11, leading=15,
                textColor=HexColor(COLOR_TEXT_BODY),
            )
            safe_desc = _xml_escape(description).replace("\n", "<br/>")
            para = Paragraph(safe_desc, desc_style)
            w_max = min(page_w - 2 * PAGE_MARGIN, 720)
            _, h_used = para.wrap(w_max, header_h)
            para.drawOn(canv, hx, hy + header_h - 56 - h_used)

    # ----- "Unreachable blocks" simple label (no container) -----
    if orphan_names:
        oxs = [positions[n][0] for n in orphan_names]
        oys = [positions[n][1] for n in orphan_names]
        ox, oy = to_pdf(min(oxs), min(oys))
        canv.setStrokeColor(HexColor(COLOR_BLOCK_BORDER))
        canv.setDash(4, 4)
        canv.setLineWidth(0.8)
        canv.line(ox, oy + 14, ox + 400, oy + 14)
        canv.setDash()
        canv.setFillColor(HexColor(COLOR_TEXT_SECONDARY))
        canv.setFont("Helvetica-Bold", 8)
        canv.drawString(ox, oy + 18, "UNREACHABLE BLOCKS  ·  defined but not called from on_start")

    # ----- edges with orthogonal/L-bend routing -----
    canv.setLineWidth(1.4)
    for name, b in blocks.items():
        if name in orphan_names:
            continue
        for target, label in b.outgoing:
            if target not in blocks:
                continue
            sx, sy = positions[name]
            ex, ey = positions[target]
            x1, y1 = to_pdf(sx + NODE_W / 2, sy + NODE_H)
            x2, y2 = to_pdf(ex + NODE_W / 2, ey)
            canv.setStrokeColor(HexColor(COLOR_EDGE))
            # L-bend: vertical from src down to midpoint, horizontal across,
            # vertical to target. Skip the elbow if already aligned.
            if abs(x1 - x2) < 1:
                canv.line(x1, y1, x2, y2)
            else:
                mid_y = (y1 + y2) / 2
                p = canv.beginPath()
                p.moveTo(x1, y1)
                p.lineTo(x1, mid_y)
                p.lineTo(x2, mid_y)
                p.lineTo(x2, y2)
                canv.drawPath(p, fill=0, stroke=1)

            # Arrowhead at target (always pointing down).
            ah, aw = 7, 4
            p = canv.beginPath()
            p.moveTo(x2, y2)
            p.lineTo(x2 - aw, y2 + ah)
            p.lineTo(x2 + aw, y2 + ah)
            p.close()
            canv.setFillColor(HexColor(COLOR_EDGE))
            canv.drawPath(p, fill=1, stroke=0)

            if label:
                if abs(x1 - x2) < 1:
                    lx, ly = x1 + 6, (y1 + y2) / 2
                else:
                    lx, ly = (x1 + x2) / 2, (y1 + y2) / 2
                cond = _condition_color(label)
                tw = canv.stringWidth(label, "Helvetica-Bold", 8) + 18
                ph = 16
                if cond:
                    # Filled pill chip — white text on the condition color.
                    canv.setFillColor(HexColor(cond))
                    canv.setStrokeColor(HexColor(cond))
                    canv.roundRect(lx - tw / 2, ly - ph / 2, tw, ph,
                                   ph / 2, fill=1, stroke=0)
                    canv.setFillColor(HexColor("#FFFFFF"))
                    canv.setFont("Helvetica-Bold", 8)
                else:
                    canv.setFillColor(HexColor(COLOR_EDGE_LABEL_BG))
                    canv.setStrokeColor(HexColor(COLOR_EDGE_LABEL_BORDER))
                    canv.setLineWidth(0.8)
                    canv.roundRect(lx - tw / 2, ly - ph / 2, tw, ph,
                                   ph / 2, fill=1, stroke=1)
                    canv.setFillColor(HexColor(COLOR_EDGE_LABEL_TEXT))
                    canv.setFont("Helvetica", 8)
                canv.drawCentredString(lx, ly - 3, label)

    # ----- note connectors (subtle dashed L-bends) -----
    canv.setDash(2, 3)
    canv.setLineWidth(0.8)
    canv.setStrokeColor(HexColor(COLOR_TEXT_SECONDARY))
    canv.setStrokeAlpha(0.55)
    for name, (nx_l, ny_l, nh_l, side) in note_positions.items():
        bx, by = positions[name]
        if side == "left":
            x1, y1 = to_pdf(bx, by + NODE_H / 2)
            x2, y2 = to_pdf(nx_l + NOTE_W, ny_l + nh_l / 2)
        else:
            x1, y1 = to_pdf(bx + NODE_W, by + NODE_H / 2)
            x2, y2 = to_pdf(nx_l, ny_l + nh_l / 2)
        if abs(y1 - y2) < 1:
            canv.line(x1, y1, x2, y2)
        else:
            mid_x = (x1 + x2) / 2
            p = canv.beginPath()
            p.moveTo(x1, y1)
            p.lineTo(mid_x, y1)
            p.lineTo(mid_x, y2)
            p.lineTo(x2, y2)
            canv.drawPath(p, fill=0, stroke=1)
    canv.setDash()
    canv.setStrokeAlpha(1.0)

    # ----- blocks (simple: outlined card, type label + name centered) -----
    for name, b in blocks.items():
        x, y = positions[name]
        bx, by = to_pdf(x, y, NODE_H)
        accent = HexColor(TYPE_ACCENT.get(b.type, "#94A3B8"))
        is_orphan = name in orphan_names
        stroke_color = HexColor(COLOR_ORPHAN_STROKE) if is_orphan else accent

        if is_orphan:
            canv.setDash(4, 4)
        canv.setFillColor(HexColor(COLOR_BLOCK_BG))
        canv.setStrokeColor(stroke_color)
        canv.setLineWidth(2)
        if b.type == "DECISION":
            # Parallelogram — top/bottom edges shift right.
            skew = NODE_H * 0.35
            p = canv.beginPath()
            p.moveTo(bx + skew, by + NODE_H)
            p.lineTo(bx + NODE_W, by + NODE_H)
            p.lineTo(bx + NODE_W - skew, by)
            p.lineTo(bx, by)
            p.close()
            canv.drawPath(p, fill=1, stroke=1)
        elif b.type == "FILTER":
            # Trapezoid (wide top, narrow bottom).
            inset = NODE_W * 0.12
            p = canv.beginPath()
            p.moveTo(bx + inset, by)
            p.lineTo(bx + NODE_W - inset, by)
            p.lineTo(bx + NODE_W, by + NODE_H)
            p.lineTo(bx, by + NODE_H)
            p.close()
            canv.drawPath(p, fill=1, stroke=1)
        else:
            arc = 22 if b.type in ("START", "END") else 10
            canv.roundRect(bx, by, NODE_W, NODE_H, arc, fill=1, stroke=1)
        if is_orphan:
            canv.setDash()

        # Type label (small caps, accent color) + block name (white, bold) centered.
        cx = bx + NODE_W / 2
        label_color = HexColor(COLOR_ORPHAN_STROKE) if is_orphan else accent
        canv.setFillColor(label_color)
        canv.setFont("Helvetica-Bold", 7.5)
        canv.drawCentredString(cx, by + NODE_H / 2 + 6, b.type)

        display_name = name.replace("_", " ")
        canv.setFillColor(HexColor(COLOR_TEXT_PRIMARY))
        canv.setFont("Helvetica-Bold", 12)
        max_name_w = NODE_W - 28
        while canv.stringWidth(display_name, "Helvetica-Bold", 12) > max_name_w and len(display_name) > 6:
            display_name = display_name[:-1]
        if display_name != name.replace("_", " "):
            display_name = display_name.rstrip() + "…"
        canv.drawCentredString(cx, by + NODE_H / 2 - 10, display_name)

    # ----- sticky notes (cream cards on dark canvas) -----
    for name, (nx_l, ny_l, nh_l, _side) in note_positions.items():
        nx, ny = to_pdf(nx_l, ny_l, nh_l)
        _draw_note(canv, None, blocks[name], nx, ny, NOTE_W, nh_l)

    canv.showPage()
    canv.save()
    return True


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _process_one(in_path: Path, out_path: Path, want_pdf: bool) -> int:
    """Convert a single playbook .py to .drawio (+ optional .pdf).

    Returns 0 on success, non-zero on failure. Designed to fail gracefully
    when called in a loop over a folder.
    """
    try:
        blocks, title, description = parse_playbook(in_path)
    except SystemExit as exc:
        sys.stderr.write(f"skip {in_path.name}: {exc}\n")
        return 1
    except Exception as exc:  # noqa: BLE001 — never abort a batch run
        sys.stderr.write(f"skip {in_path.name}: parse error: {exc}\n")
        return 1

    positions = compute_layout(blocks)
    xml = emit_drawio(blocks, positions, title, description)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(xml)
    print(f"wrote {out_path}  ({len(blocks)} blocks)")

    if want_pdf:
        pdf_out = out_path.with_suffix(".pdf")
        if export_pdf_via_drawio(out_path, pdf_out):
            print(f"wrote {pdf_out}  (via draw.io)")
        elif render_pdf(blocks, positions, title, pdf_out, description=description):
            print(f"wrote {pdf_out}  (via reportlab)")
        else:
            sys.stderr.write(
                f"PDF export failed for {in_path.name}. Install draw.io desktop\n"
                "  (brew install --cask drawio) or reportlab (pip install reportlab).\n"
            )
            return 1
    return 0


def _is_playbook_file(path: Path) -> bool:
    """Cheap heuristic — file must mention phantom.playbook_block or on_start."""
    try:
        text = path.read_text(errors="replace")
    except OSError:
        return False
    return "phantom.playbook_block" in text or "def on_start" in text


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        description=(
            "Convert one Splunk SOAR playbook .py file — or a whole directory "
            "of them — into draw.io diagrams (and optionally PDFs)."
        )
    )
    p.add_argument(
        "input", type=Path,
        help="A SOAR playbook .py file, or a directory containing playbook .py files",
    )
    p.add_argument(
        "-o", "--output", type=Path, default=None,
        help=(
            "Output path. For a single-file input, the .drawio file path "
            "(defaults to <input>.drawio next to the input). For a directory "
            "input, an output directory where one .drawio per playbook is "
            "written (defaults to the input directory)."
        ),
    )
    p.add_argument(
        "--pdf", action="store_true",
        help="Also export PDF via draw.io CLI if available, else via reportlab",
    )
    args = p.parse_args(argv)

    if not args.input.exists():
        sys.stderr.write(f"input not found: {args.input}\n")
        return 2

    # ---- Directory mode --------------------------------------------------
    if args.input.is_dir():
        out_dir = args.output or args.input
        if out_dir.exists() and not out_dir.is_dir():
            sys.stderr.write(
                f"--output must be a directory when --input is a directory "
                f"(got {out_dir})\n"
            )
            return 2
        out_dir.mkdir(parents=True, exist_ok=True)

        # Recurse one level by default; include subdirs too.
        candidates = sorted(p for p in args.input.rglob("*.py"))
        playbooks = [p for p in candidates if _is_playbook_file(p)]
        skipped = len(candidates) - len(playbooks)
        if not playbooks:
            sys.stderr.write(
                f"no playbook .py files found in {args.input} "
                f"(checked {len(candidates)} .py files)\n"
            )
            return 1

        print(f"processing {len(playbooks)} playbook(s) "
              f"({skipped} non-playbook .py file(s) skipped)")
        failed = 0
        for pb in playbooks:
            out_path = out_dir / (pb.stem + ".drawio")
            if _process_one(pb, out_path, args.pdf) != 0:
                failed += 1
        if failed:
            sys.stderr.write(f"{failed} playbook(s) failed to convert\n")
            return 1
        return 0

    # ---- Single-file mode (original behavior) ----------------------------
    out = args.output or args.input.with_suffix(".drawio")
    return _process_one(args.input, out, args.pdf)


if __name__ == "__main__":
    raise SystemExit(main())

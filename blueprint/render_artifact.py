#!/usr/bin/env python3
"""Render the RBM2D blueprint as a single self-contained HTML page.

    python3 blueprint/render_artifact.py <repo-root> <out.html>

Reads `blueprint/src/content.tex` for the node graph and the modules imported
by `RBM2D.lean` for the declarations, draws one global graph holding every node, then lays each
\\chapter out on its own with the
graphviz `dot` binary, and inlines the SVG.  Needs only graphviz + python3 — no
plasTeX, no LaTeX, no WebAssembly in the output.

Node status comes from the blueprint itself, never from a hand-kept list:

  done      a \\begin{proof} carrying \\leanok       dark green ellipse
  defn      a definition carrying \\leanok           light green rounded box
  ready     no \\leanok, but every \\uses ancestor is done   blue
  blocked   no \\leanok and an ancestor is missing   plain

A `\\lean{}` tag naming a declaration that does not exist in the Lean sources is
a hard error: the dependency graph must never claim more than the code does.
"""
import re, subprocess, sys, html, pathlib, json, shutil

C = {  # fill, stroke, text
  "done":    ("#1f9d6b", "#177a54", "#ffffff"),
  "defn":    ("#cfe9dc", "#7cbfa4", "#123a2b"),
  "ready":   ("#dbe8f5", "#7ba3cc", "#16354f"),
  "blocked": ("#ffffff", "#b9c1c9", "#55606b"),
  "cited":   ("#fdf3e0", "#d8b877", "#6b4e16"),
}
DECL = re.compile(r"^(?:noncomputable\s+)?(theorem|def|abbrev|lemma|structure)\s+([A-Za-z_][\w.'!?₀-₉]*)")

PILL = {"done": "已证", "defn": "已形式化", "ready": "可开工", "blocked": "待解锁", "cited": "引用论文"}

# Chinese chapter headings, keyed by a distinctive fragment of the \chapter{} title.
CHAPTER = [("Main probabilistic estimates", "第 6 章 · 主定理证明链"),
           ("Loop hierarchy and convolution tree", "第 5 章 · 环层级与卷积树"),
           ("replacement stack", "第 4 章 · 随机层 —— Itô 替代栈"),
           ("Section 8", "第 2 章 · §8 —— Lemma lem_propTH 的证明"),
           ("model and the propagator", "第 1 章 · 模型与传播子 Θ_ξ"),
           ("Delocalization", "第 3 章 · 退局域化"),
           ("Not formalized", "不形式化的部分")]

def chapter_title(raw):
    for frag, zh in CHAPTER:
        if frag in raw:
            return zh
    return clean(raw)

def clean(t):
    t = re.sub(r"\\texorpdfstring\{(.*?)\}\{.*?\}", r"\1", t, flags=re.S)
    t = re.sub(r"\\(eqref|ref|texttt|emph|text|mathrm)\{([^{}]*)\}", r"\2", t)
    return t.replace("\\", "").replace("$", "").replace("{", "").replace("}", "").replace('"', "").strip()

# which work order each not-yet-formalized node belongs to
TASK = {"lem:qcomp": "T2", "lem:latticesum": "T3", "lem:decay-small": "T4",
        "lem:zero-mode": "T14", "lem:shells": "T15", "lem:harmonic": "T16",
        "lem:bd-case2": "T5", "lem:log-integral": "T25", "def:continuum": "T26",
        "lem:contour": "T27", "lem:periodize": "T28", "lem:decay-interface": "T24",
        "lem:cutoff": "T19", "lem:abel": "T20", "lem:symbol-diff": "T21",
        "lem:dyadic": "T22", "lem:dyadic-case1": "T18", "lem:propTH-5": "T30",
        "lem:propTH-6-conditional": "T23", "lem:propTH-6": "T22",
        "lem:dyadic-sums": "T17", "def:block-model": "T7 ★ 最优先",
        "def:model": "S4", "def:stochdom": "S0",
        "lem:envelope": "S1", "lem:stein-scalar": "S2", "lem:stein-product": "S3",
        "lem:stein": "S3/S4", "lem:bootstrap": "S8",
        "lem:generator": "S5", "lem:bridge-prec": "S6", "lem:bridge-moment": "S7",
        "lem:gronwall": "S9", "lem:discharge": "S10",
        "lem:short-time-comparison": "U1", "thm:bulk-univ": "U2"}

def parse(tex):
    chapters, cur = [], None
    env = re.compile(r"\\begin\{(lemma|definition|remark|theorem|corollary|proposition)\}(\[[^\]]*\])?")
    i, nodes_seen = 0, set()
    for m in re.finditer(r"\\chapter\{([^}]*)\}|" + env.pattern, tex):
        pass
    # walk the file linearly so chapter membership is by position
    pos = 0
    marks = []
    for m in re.finditer(r"\\chapter\{", tex):
        i, depth = m.end(), 1
        while i < len(tex) and depth:
            depth += (tex[i] == "{") - (tex[i] == "}")
            i += 1
        marks.append((m.start(), "chapter", tex[m.end():i - 1]))
    marks += [(m.start(), "env", m) for m in env.finditer(tex)]
    marks.sort(key=lambda t: t[0])
    for start, kind, payload in marks:
        if kind == "chapter":
            cur = {"title": chapter_title(payload), "nodes": []}
            chapters.append(cur)
            continue
        m = payload
        kindname = m.group(1)
        title = (m.group(2) or "[]")[1:-1]
        end = tex.index("\\end{%s}" % kindname, start)
        body = tex[start:end]
        lab = re.search(r"\\label\{([^}]*)\}", body)
        if not lab or cur is None:
            continue
        label = lab.group(1)
        if label in nodes_seen:
            continue
        nodes_seen.add(label)
        leans = [n.strip() for g in re.findall(r"\\lean\{([^}]*)\}", body) for n in g.split(",") if n.strip()]
        uses = [n.strip() for g in re.findall(r"\\uses\{([^}]*)\}", body) for n in g.split(",") if n.strip()]
        # the proof block that follows this environment, if any
        nxt = tex.find("\\begin{", end + 1)
        proof_ok = False
        if nxt != -1 and tex.startswith("\\begin{proof}", nxt):
            pend = tex.index("\\end{proof}", nxt)
            proof_ok = "\\leanok" in tex[nxt:pend]
            uses += [n.strip() for g in re.findall(r"\\uses\{([^}]*)\}", tex[nxt:pend]) for n in g.split(",") if n.strip()]
        cur["nodes"].append({"label": label, "kind": kindname, "title": title,
                             "lean": leans, "uses": sorted(set(uses)),
                             "stmt_ok": "\\leanok" in body, "proof_ok": proof_ok})
    return chapters

def classify(nodes):
    by = {n["label"]: n for n in nodes}
    for n in nodes:
        if n["kind"] == "remark":
            n["status"] = "cited"
        elif n["kind"] == "definition":
            n["status"] = "defn" if n["stmt_ok"] else ("ready" if all(by.get(u, {}).get("status") in ("done", "defn", None) for u in n["uses"]) else "blocked")
        elif n["proof_ok"]:
            n["status"] = "done"
        else:
            deps = [by[u] for u in n["uses"] if u in by]
            n["status"] = "ready" if all(d.get("status") in ("done", "defn") for d in deps) else "blocked"
    return by

def short(n):
    t = clean(n["title"] or n["label"].split(":", 1)[-1]).replace("_", " ")
    return t[:46]

def dot_for(ch, by):
    lines = ['digraph G { graph [bgcolor=transparent,rankdir=TB,nodesep=.35,ranksep=.45];',
             ' node [fontname="Helvetica",fontsize=11,penwidth=1.4];',
             ' edge [color="#aeb6bf",penwidth=1.1,arrowsize=.7];']
    here = {n["label"] for n in ch["nodes"]}
    ext = set()
    for n in ch["nodes"]:
        f, s, tc = C[n["status"]]
        shape = 'shape=box,style="rounded,filled"' if n["kind"] == "definition" else 'shape=ellipse,style=filled'
        tag = open_task(n)
        lbl = short(n) + (f"   {tag}" if tag else "")
        lines.append(f' "{n["label"]}" [{shape},fillcolor="{f}",color="{s}",fontcolor="{tc}",label="{lbl}"];')
        for u in n["uses"]:
            if u not in here and u in by:
                ext.add(u)
    for u in sorted(ext):
        lines.append(f' "{u}" [shape=box,style="rounded,filled,dashed",fillcolor="#f1f3f5",color="#b9c1c9",'
                     f'fontcolor="#7d8791",fontsize=10,label="{short(by[u])}  →前章"];')
    for n in ch["nodes"]:
        for u in n["uses"]:
            if u in by:
                style = ',style=dashed' if u in ext else ''
                lines.append(f' "{u}" -> "{n["label"]}" [{style[1:] if style else ""}];')
    lines.append("}")
    return "\n".join(lines)

def gshort(n):
    """Compact label for the global graph: the part of the tag after the colon."""
    s = n["label"].split(":", 1)[-1]
    tag = open_task(n)
    return s + (f"\\n{tag}" if tag else "")

def open_task(n):
    """The work order number, but only while the node is still open."""
    return None if n["status"] in ("done", "defn", "cited") else TASK.get(n["label"])

def cluster_label(t):
    return t.split("——")[0].strip()

def global_dot(chapters, by):
    """One digraph holding EVERY node of EVERY chapter, grouped by chapter.

    No `→前章` stubs here: since every node is present, every `\\uses` edge is
    drawn in full, so this is the only picture that shows the whole proof at once.
    """
    lines = ['digraph G { graph [bgcolor=transparent,rankdir=TB,nodesep=.22,ranksep=.38];',
             ' node [fontname="Helvetica",fontsize=10,penwidth=1.3,margin="0.09,0.05"];',
             ' edge [color="#aeb6bf",penwidth=1.0,arrowsize=.6];']
    for i, ch in enumerate(chapters):
        if not ch["nodes"]:
            continue
        lines.append(f' subgraph cluster_{i} {{')
        lines.append(f'  label="{cluster_label(ch["title"])}"; labelloc="t"; labeljust="l";')
        lines.append('  fontname="Helvetica"; fontsize=11; fontcolor="#6d7883";')
        lines.append('  color="#ccd4dc"; style="rounded"; penwidth=1.1; margin=10;')
        for n in ch["nodes"]:
            f, st, tc = C[n["status"]]
            shape = 'shape=box,style="rounded,filled"' if n["kind"] == "definition" else 'shape=ellipse,style=filled'
            lines.append(f'  "{n["label"]}" [{shape},fillcolor="{f}",color="{st}",'
                         f'fontcolor="{tc}",label="{gshort(n)}"];')
        lines.append(' }')
    for ch in chapters:
        for n in ch["nodes"]:
            for u in n["uses"]:
                if u in by:
                    lines.append(f' "{u}" -> "{n["label"]}";')
    lines.append("}")
    return "\n".join(lines)

def svg_from_dot(src):
    out = subprocess.run(["dot", "-Tsvg"], input=src, capture_output=True, text=True)
    if out.returncode:
        raise SystemExit(out.stderr)
    s = out.stdout[out.stdout.index("<svg"):]
    s = s.replace("<svg ", '<svg class="depgraph" preserveAspectRatio="xMinYMin meet" ', 1)
    s = re.sub(r'width="\d+pt"\s+height="\d+pt"\s*', "", s, count=1)
    w = re.search(r'viewBox="0\.00 0\.00 ([\d.]+)', s)
    return s, float(w.group(1)) if w else 800.0

def svg_for(ch, by):
    return svg_from_dot(dot_for(ch, by)) if shutil.which("dot") else svg_fallback([ch], by, False)

def svg_fallback(chapters, by, global_view):
    """Self-contained SVG layout for hosts without the Graphviz executable."""
    nodes = [n for ch in chapters for n in ch["nodes"]]
    here = {n["label"] for n in nodes}
    positions, boxes = {}, []
    if global_view:
        for i, ch in enumerate(chapters):
            if not ch["nodes"]:
                continue
            x = 20 + i * 290
            boxes.append((x, 46, 268, 50 + len(ch["nodes"]) * 65, ch["title"]))
            for j, n in enumerate(ch["nodes"]):
                positions[n["label"]] = (x + 134, 99 + j * 65)
        width = max(600, 30 + len(chapters) * 290)
        height = max(320, 120 + max((len(c["nodes"]) for c in chapters), default=0) * 65)
    else:
        external = sorted({u for n in nodes for u in n["uses"] if u not in here and u in by})
        order = external + [n["label"] for n in nodes]
        rank, visiting = {}, set()
        def level(label):
            if label in rank:
                return rank[label]
            if label in visiting:
                raise SystemExit("cycle in blueprint dependencies: " + label)
            visiting.add(label)
            deps = [u for u in by[label]["uses"] if u in here or u in external]
            rank[label] = 1 + max((level(u) for u in deps), default=-1)
            visiting.remove(label)
            return rank[label]
        for label in order:
            level(label)
        levels = {}
        for label in order:
            levels.setdefault(rank[label], []).append(label)
        for col, labels in levels.items():
            for row, label in enumerate(labels):
                positions[label] = (148 + col * 280, 83 + row * 68)
        width = max(600, 40 + (max(levels, default=0) + 1) * 280)
        height = max(300, 135 + max((len(v) for v in levels.values()), default=0) * 68)
    marker = "bp-arrow-global" if global_view else "bp-arrow-" + str(abs(hash(chapters[0]["title"])))
    out = [f'<svg class="depgraph" preserveAspectRatio="xMinYMin meet" '
           f'viewBox="0 0 {width} {height}" xmlns="http://www.w3.org/2000/svg">',
           f'<defs><marker id="{marker}" viewBox="0 0 10 10" refX="9" refY="5" '
           'markerWidth="5" markerHeight="5" orient="auto-start-reverse">'
           '<path d="M 0 0 L 10 5 L 0 10 z" fill="#aeb6bf"/></marker></defs>']
    for x, y, w, h, title in boxes:
        out.append(f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="12" '
                   'fill="none" stroke="#cbd4dc" stroke-width="1.2"/>')
        out.append(f'<text x="{x + 12}" y="{y + 20}" fill="#60707d" '
                   f'font-family="sans-serif" font-size="12">{html.escape(title[:32])}</text>')
    for n in nodes:
        target = n["label"]
        if target not in positions:
            continue
        x2, y2 = positions[target]
        for source in n["uses"]:
            if source not in positions:
                continue
            x1, y1 = positions[source]
            if x2 > x1 + 30:
                sx, tx = x1 + 112, x2 - 112
                m = (sx + tx) / 2
                path = f'M {sx} {y1} C {m} {y1}, {m} {y2}, {tx} {y2}'
            elif x2 < x1 - 30:
                sx, tx = x1 - 112, x2 + 112
                m = (sx + tx) / 2
                path = f'M {sx} {y1} C {m} {y1}, {m} {y2}, {tx} {y2}'
            else:
                sx = x1 + 112
                path = f'M {sx} {y1} C {sx + 70} {y1}, {sx + 70} {y2}, {x2 + 112} {y2}'
            out.append(f'<path d="{path}" fill="none" stroke="#aeb6bf" '
                       f'stroke-opacity=".48" stroke-width="1" marker-end="url(#{marker})"/>')
    for label, (x, y) in positions.items():
        n = by[label]
        f, stroke, color = C[n["status"]] if label in here else ("#f1f3f5", "#b9c1c9", "#60707d")
        out.append(f'<g class="node"><title>{html.escape(label)}</title>')
        if n["kind"] == "definition" or label not in here:
            out.append(f'<rect x="{x - 112}" y="{y - 23}" width="224" height="46" rx="9" '
                       f'fill="{f}" stroke="{stroke}" stroke-width="1.4"/>')
        else:
            out.append(f'<ellipse cx="{x}" cy="{y}" rx="112" ry="23" '
                       f'fill="{f}" stroke="{stroke}" stroke-width="1.4"/>')
        title = (gshort(n) if global_view else short(n))[:30]
        tag = open_task(n) if not global_view else None
        out.append(f'<text x="{x}" y="{y + 4}" text-anchor="middle" '
                   f'font-family="sans-serif" font-size="11" fill="{color}">'
                   f'{html.escape(title + (" · " + tag if tag else ""))}</text></g>')
    out.append('</svg>')
    return "".join(out), float(width)

def figure_html(cap, svg, w):
    return (f'<figure class="graph" data-basew="{w:.0f}"><div class="gbar">'
            f'<span class="gcap">{html.escape(cap)}</span>'
            '<div class="gtools"><button type="button" data-act="out" aria-label="缩小">&minus;</button>'
            '<button type="button" data-act="fit">适应宽度</button>'
            '<button type="button" data-act="in" aria-label="放大">+</button>'
            '<span class="gpct" aria-live="polite">100%</span></div></div>'
            f'<div class="plate">{svg}</div></figure>')

def main(root, out):
    root = pathlib.Path(root)
    tex = (root / "blueprint/src/content.tex").read_text(encoding="utf-8")
    # Workers can create untracked Lean files while the coordinator renders the
    # blueprint. Count only modules reachable from the audited root import list.
    def imported_sources():
        todo = [root / "RBM2D.lean"]
        seen = set()
        while todo:
            path = todo.pop()
            if path in seen:
                continue
            seen.add(path)
            for mod in re.findall(r"^import (RBM2D(?:\.[A-Za-z_][\w]*)+)$",
                                  path.read_text(encoding="utf-8"), re.M):
                child = root / (mod.replace(".", "/") + ".lean")
                if child.is_file():
                    todo.append(child)
        return sorted(path for path in seen if path != root / "RBM2D.lean")
    # Fully-qualified declaration names, tracking `namespace`/`end` so that a tag
    # like RBM.Gauss.norm_green_le resolves exactly and a typo still fails.
    def qualified(text):
        stack, out = [], []
        for ln in text.split("\n"):
            if ln.startswith("namespace "):
                stack.append(ln.split()[1].strip())
            elif ln.startswith("end ") and stack and ln.split()[1].strip() == stack[-1]:
                stack.pop()
            else:
                m = DECL.match(ln)
                if m:
                    out.append((m.group(1), ".".join(stack + [m.group(2)])))
        return out
    # The SET validates \lean{} tags and must accept every kind of declaration,
    # since a node may well point at a `def` (RBM.SB, RBM.shellIndex).  The
    # headline COUNT is theorems only -- `def`s are bookkeeping, not mathematics,
    # and counting them inflates the number the reader cares about.
    found = [kn for p in imported_sources()
                for kn in qualified(p.read_text(encoding="utf-8"))]
    decls = {n for _, n in found}
    n_thm = sum(1 for k, _ in found if k in ("theorem", "lemma"))
    chapters = parse(tex)
    allnodes = [n for ch in chapters for n in ch["nodes"]]
    bad = [d for n in allnodes for d in n["lean"] if d not in decls]
    if bad:
        raise SystemExit("\\lean{} tags with no declaration: " + ", ".join(bad))
    by = classify(allnodes)
    counts = {k: sum(1 for n in allnodes if n["status"] == k) for k in C}
    thms = n_thm

    body = []
    gsvg, gw = (svg_from_dot(global_dot(chapters, by)) if shutil.which("dot")
                 else svg_fallback(chapters, by, True))
    # graphviz writes "-" as "&#45;" inside <title>, so unescape before checking
    seen = set(re.findall(r"<title>([^<]*)</title>", gsvg.replace("&#45;", "-")))
    missing = [n["label"] for n in allnodes if n["label"] not in seen]
    if missing:
        raise SystemExit("global graph is missing nodes: " + ", ".join(missing))
    edges = sum(1 for n in allnodes for u in n["uses"] if u in by)
    body.append('<h2>全文依赖图</h2>')
    body.append('<p class="sub">下面各章的每一个节点都在这张图里，按章分组；箭头方向是'
                '“被用到的引理 → 用到它的结论”。节点上的 T□ 是 <code>docs/TASKS.md</code> 里的工单号。</p>')
    body.append(figure_html(f'全局 · {len(allnodes)} 个节点 · {edges} 条依赖', gsvg, gw))
    for ch in chapters:
        if not ch["nodes"]:
            continue
        svg, w = svg_for(ch, by)
        body.append(f'<h2>{html.escape(ch["title"])}</h2>')
        body.append(figure_html(f'{ch["title"]} · {len(ch["nodes"])} 个节点', svg, w))
        rows = []
        for n in ch["nodes"]:
            st = n["status"]
            tag = open_task(n)
            names = " · ".join(d.removeprefix("RBM.") for d in n["lean"][:4]) + (" …" if len(n["lean"]) > 4 else "")
            side = f'<span class="pill {st}">{PILL[st]}</span>'
            side += f'<code>{html.escape(names)}</code>' if names else (f'<code>工单 {tag}</code>' if tag else "")
            rows.append(f'<li class="row"><div class="row-main"><span class="row-name">{html.escape(short(n))}</span>'
                        f'<span class="row-ref">{html.escape(n["label"])}</span></div>'
                        f'<div class="row-side">{side}</div></li>')
        body.append('<ul class="rows">' + "".join(rows) + "</ul>")
    pathlib.Path(out).write_text(TEMPLATE.replace("@@BODY@@", "\n".join(body))
        .replace("@@DONE@@", str(counts["done"] + counts["defn"]))
        .replace("@@READY@@", str(counts["ready"]))
        .replace("@@TODO@@", str(counts["blocked"]))
        .replace("@@THMS@@", str(thms)), encoding="utf-8")
    print(json.dumps(counts), "theorems:", thms, "of", len(found), "declarations")

TEMPLATE = pathlib.Path(__file__).with_name("artifact_template.html").read_text(encoding="utf-8") \
    if pathlib.Path(__file__).with_name("artifact_template.html").exists() else ""

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])

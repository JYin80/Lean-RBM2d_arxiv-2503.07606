#!/usr/bin/env python3
"""Render the RBM2D blueprint as a single self-contained HTML page.

    python3 blueprint/render_artifact.py <repo-root> <out.html>

Reads `blueprint/src/content.tex` for the node graph and `RBM2D/**/*.lean` for
the declarations, draws one global graph holding every node, then lays each
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
import re, subprocess, sys, html, pathlib, json

C = {  # fill, stroke, text
  "done":    ("#1f9d6b", "#177a54", "#ffffff"),
  "defn":    ("#cfe9dc", "#7cbfa4", "#123a2b"),
  "ready":   ("#dbe8f5", "#7ba3cc", "#16354f"),
  "blocked": ("#ffffff", "#b9c1c9", "#55606b"),
  "cited":   ("#fdf3e0", "#d8b877", "#6b4e16"),
}
PILL = {"done": "已证", "defn": "已形式化", "ready": "可开工", "blocked": "待解锁", "cited": "引用论文"}

# Chinese chapter headings, keyed by a distinctive fragment of the \chapter{} title.
CHAPTER = [("Section 8", "第 2 章 · §8 —— Lemma lem_propTH 的证明"),
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
    return t.replace("\\", "").replace("$", "").replace("{", "").replace("}", "").strip()

# which work order each not-yet-formalized node belongs to
TASK = {"lem:qcomp": "T2", "lem:latticesum": "T3", "lem:decay-small": "T4",
        "lem:zero-mode": "T14", "lem:shells": "T15", "lem:harmonic": "T16",
        "lem:bd-case2": "T5", "lem:contour": "T9", "lem:periodize": "T10",
        "lem:dyadic": "T11", "lem:propTH-5": "T4+T10", "lem:propTH-6": "T5+T11",
        "lem:dyadic-sums": "T17"}

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
    return svg_from_dot(dot_for(ch, by))

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
    src = "\n".join(p.read_text(encoding="utf-8") for p in root.glob("RBM2D/**/*.lean"))
    # two different things: the SET is for validating \lean{} tags, the COUNT is
    # every declaration.  Counting len(set) hid 8 declarations whose names repeat
    # across namespaces (DetDom.add and UnifDetDom.add are both real theorems).
    found = re.findall(r"^(?:noncomputable\s+)?(?:theorem|def|abbrev|lemma)\s+([A-Za-z_][\w.'!?₀-₉]*)", src, re.M)
    decls = set(found)
    chapters = parse(tex)
    allnodes = [n for ch in chapters for n in ch["nodes"]]
    bad = [d for n in allnodes for d in n["lean"] if d.removeprefix("RBM.") not in decls]
    if bad:
        raise SystemExit("\\lean{} tags with no declaration: " + ", ".join(bad))
    by = classify(allnodes)
    counts = {k: sum(1 for n in allnodes if n["status"] == k) for k in C}
    thms = len(found)

    body = []
    gsvg, gw = svg_from_dot(global_dot(chapters, by))
    # graphviz writes "-" as "&#45;" inside <title>, so unescape before checking
    seen = set(re.findall(r"<title>([^<]*)</title>", gsvg.replace("&#45;", "-")))
    missing = [n["label"] for n in allnodes if n["label"] not in seen]
    if missing:
        raise SystemExit("global graph is missing nodes: " + ", ".join(missing))
    edges = sum(1 for n in allnodes for u in n["uses"] if u in by)
    body.append('<h2>全局依赖图</h2>')
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
    print(json.dumps(counts), "decls:", thms)

TEMPLATE = pathlib.Path(__file__).with_name("artifact_template.html").read_text(encoding="utf-8") \
    if pathlib.Path(__file__).with_name("artifact_template.html").exists() else ""

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])

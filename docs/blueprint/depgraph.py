#!/usr/bin/env python3
"""Render one dependency figure per chapter from the extracted blueprint nodes.

The script reads the labels in src/content.tex and the \\uses data in the
LeanArchitect output. It writes one PDF and one SVG per chapter to src/figures/.
"""
import glob, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(ROOT, "..", ".."))
CONTENT = os.path.join(ROOT, "src", "content.tex")
ARTIFACTS = os.path.join(REPO, ".lake", "build", "blueprint", "module")
FIGURES = os.path.join(ROOT, "src", "figures")

COLORS = ["#1CAC78", "#4F86C6", "#E0A458"]

def slug(title):
    return re.sub(r"[^a-z0-9]+", "-", title.lower()).strip("-")

# chapter -> ordered labels
chapters, current = [], None
for line in open(CONTENT):
    m = re.match(r"\\chapter\{(.*)\}", line)
    if m:
        current = (m.group(1), [])
        chapters.append(current)
    m = re.match(r"\\inputleannode\{(.*)\}", line)
    if m and current:
        current[1].append(m.group(1))
chapters = [c for c in chapters if c[1]]

# label -> (uses, isDefinition)
nodes = {}
for path in glob.glob(os.path.join(ARTIFACTS, "**", "*.artifacts", "*.tex"), recursive=True):
    text = open(path).read()
    label = re.search(r"\\label\{(.*?)\}", text).group(1)
    uses = set()
    for m in re.finditer(r"\\uses\{(.*?)\}", text):
        uses.update(x.strip() for x in m.group(1).split(","))
    nodes[label] = (uses, text.lstrip().startswith("\\begin{definition}"))

chapter_of = {label: i for i, (_, labels) in enumerate(chapters) for label in labels}
missing = [l for l in chapter_of if l not in nodes]
if missing:
    sys.exit(f"missing extracted nodes: {missing}")

def closure(root):
    seen, stack = set(), [root]
    while stack:
        label = stack.pop()
        if label in seen:
            continue
        seen.add(label)
        stack.extend(u for u in nodes[label][0] if u in nodes)
    return seen

def display(label):
    parts = label.split(".")
    return "\\n".join([".".join(parts[:-1]), parts[-1]]) if len(parts) > 1 else label

os.makedirs(FIGURES, exist_ok=True)
for index, (title, labels) in enumerate(chapters):
    root = labels[0]
    members = closure(root)
    lines = ["digraph {", "  rankdir=BT; nodesep=0.25; ranksep=0.45;",
             '  node [shape=box, style="rounded,filled", fontname="Helvetica", fontsize=11, penwidth=0, margin="0.08,0.03"];',
             '  edge [arrowsize=0.6, color="#555555"];']
    for label in sorted(members):
        chapter = chapter_of.get(label, index)
        color = COLORS[chapter % len(COLORS)]
        shape = "shape=box" if nodes[label][1] else "shape=box"
        fill = color if chapter == index else "#DDDDDD"
        font = "white" if chapter == index else "#333333"
        peripheries = ', peripheries=2' if label == root else ""
        lines.append(f'  "{label}" [label="{display(label)}", fillcolor="{fill}", fontcolor="{font}"{peripheries}];')
    for label in sorted(members):
        for use in sorted(nodes[label][0]):
            if use in members:
                lines.append(f'  "{use}" -> "{label}";')
    lines.append("}")
    dot = "\n".join(lines)
    name = slug(title)
    open(os.path.join(FIGURES, name + ".dot"), "w").write(dot)
    # Stagger the leaves so wide graphs become taller and more legible.
    staggered = subprocess.run(["unflatten", "-f", "-l", "3", "-c", "4"], input=dot.encode(),
                               check=True, capture_output=True).stdout
    for fmt in ("pdf", "svg"):
        out = os.path.join(FIGURES, name + "." + fmt)
        subprocess.run(["dot", "-T" + fmt, "-o", out], input=staggered, check=True)
    print(f"{name}: {len(members)} nodes")

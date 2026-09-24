# ArgoMAC proof blueprint

The blueprint documents the three verified security properties.
LeanArchitect extracts each node from the `@[blueprint]` attributes in the `lean/` package.
Lean Blueprint renders the nodes as a PDF and as a web site with a dependency graph.

## Build

1. Install the Python tools: `pip install leanblueprint`.
2. Fetch the Mathlib build cache: `lake exe cache get`.
3. Build the root project: `lake build`.
4. Extract the nodes: `make -C docs/blueprint extract`.
5. Build the PDF: `make -C docs/blueprint pdf`.
6. Build the web site: `make -C docs/blueprint web`.
7. View the web site: `make -C docs/blueprint serve`.

The `leanblueprint` command expects the blueprint at the repository root.
The Makefile runs the same `latexmk` and `plastex` commands from this directory.

`lakefile.toml` enables the Lake artifact cache.
Lake stores every build artifact in the toolchain cache directory.
A second checkout of the same commit reuses the artifacts and does not rebuild.

The PDF is `docs/blueprint/print/print.pdf`.
The web site is `docs/blueprint/web/index.html`.
The dependency graph is `docs/blueprint/web/dep_graph_document.html`.

## Layout

- `lean/` is the Lake package with the `@[blueprint]` nodes. It requires the root package by path and reuses its dependency checkouts.
- `src/content.tex` selects the nodes for each property.
- `src/print.tex` and `src/web.tex` are the document preambles.
- `src/macros/` holds the shared, print, and web macros.
- `lean/.lake/build/blueprint/` holds the extracted nodes.

## Paper restatements

Each chapter opens with a `Statements from the paper` section.
The `restatement` environment restates a BABE item and lists the Lean nodes that formalize it.
The bibliography entry for the paper is in `src/references.bib`.
Cite it with `\cite{babe}`.
The restatement environment is not part of the dependency graph.

## Edit a node

The nodes live in the Lake package `lean/`, in `lean/Blueprint/*.lean`.
Each node is an `attribute [blueprint "label" (statement := /-- ... -/) (proof := /-- ... -/)] Name` command on a declaration of the root package.
The verified sources in `Construction/` and `Proof/` do not import LeanArchitect, so the Kriterion verifier does not see the blueprint.
Private lemmas become visible through `open private ... from Module`.
Use `\cref{label}` in the text to cite another node.
LeanArchitect infers the dependencies from the constants in the statement and the proof.
Add `(proofUses := ["label"])` to show a dependency that passes through untagged lemmas.
Add `\inputleannode{label}` to `src/content.tex` to show a new node.

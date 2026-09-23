# The leanblueprint CLI expects the blueprint at the repository root.
# These targets run the same commands from docs/blueprint.
LATEXMK ?= latexmk
PLASTEX ?= plastex
LAKE ?= lake

.PHONY: all extract figures pdf web serve clean

all: pdf web

extract:
	cd ../.. && $(LAKE) build :blueprint

figures:
	python3 depgraph.py

pdf: figures
	mkdir -p print
	cd src && $(LATEXMK) -output-directory=../print
	cp print/print.bbl src/web.bbl

web: figures src/web.bbl
	mkdir -p web
	cd src && $(PLASTEX) -c plastex.cfg web.tex

serve:
	cd web && python3 -m http.server 8000

src/web.bbl: pdf

clean:
	rm -rf print web lean_decls src/figures src/web.bbl

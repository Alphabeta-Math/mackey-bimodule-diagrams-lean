# README diagram

The [identity-dot example](identity-dot.tex) is written in TikZ and rendered as a self-contained [SVG](identity-dot.svg). It illustrates `MackeyDiagrams.DotLabel.upDrawing_identity`: equality of evaluated maps, with distinct diagram syntax.

With LaTeX, PGF/TikZ and dvisvgm installed, run from the repository root:

```sh
mkdir -p .lake/readme-tikz
latex -interaction=nonstopmode -halt-on-error -output-directory=.lake/readme-tikz docs/identity-dot.tex
dvisvgm --no-fonts --exact --bbox=min --output=docs/identity-dot.svg .lake/readme-tikz/identity-dot.dvi
```

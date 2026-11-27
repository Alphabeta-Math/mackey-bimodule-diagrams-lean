"""Merge the stable diagram documentation into the workflow's README."""
from pathlib import Path

root = Path(__file__).resolve().parent
readme = root / "README.md"
diagram_documentation = root / "DIAGRAMS.md"
marker = "<!-- Diagram semantics appendix -->"
if readme.exists():
    heading = readme.read_text(encoding="utf-8").partition(marker)[0].rstrip()
else:
    heading = "# Bimodule String Diagrams and the Generalized Mackey Decomposition\n\nFormal verification in progress."
next_readme = f"{heading}\n\n{marker}\n\n{diagram_documentation.read_text(encoding='utf-8').rstrip()}\n"
temporary = root / ".README.next"
temporary.write_text(next_readme, encoding="utf-8")
temporary.replace(readme)


# Building the complete formalization

All article proofs, the 35 necessary lecture-note results, supporting Lean sources, and their workflow evidence live in this repository.

After installing the pinned Lean toolchain, run:

```sh
lake update
lake exe cache get
lake -d prerequisites update
make
```

The default Make target builds the main article library and the prerequisite library sequentially. `lake build` alone builds the main package; `lake -d prerequisites build` builds the lecture-note package against the main sources in this checkout.

The package boundary preserves the different statements sharing theorem names in the two articles. It does not require a second repository. The main paper uses the explicitly checked WattsFoundation bridges; the lecture-note statements, sources, reviews, and axiom evidence are retained under prerequisites/.

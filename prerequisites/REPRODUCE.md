# Necessary categorical prerequisites

This Lake package belongs to the main article repository. From the repository root, `make` builds both the article library and these 35 prerequisite results. To build this package alone, run `lake -d prerequisites build`. Its dependency is the repository root, declared as `path = ".."`; no sibling checkout is required.

The packages keep distinct build environments because the two articles use some of the same theorem names for different precise statements. The main paper uses the checked bridges in WattsFoundation. The complete source and independent workflow evidence for the lecture-note results are retained here.

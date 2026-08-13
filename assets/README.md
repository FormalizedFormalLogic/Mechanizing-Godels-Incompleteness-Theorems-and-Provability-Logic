# Assets

## `Lean.sublime-syntax`

Sublime Text syntax definition for Lean 4, used by Typst's `raw` highlighting via the `syntaxes` parameter.

Vendored from [sharkdp/bat](https://github.com/sharkdp/bat/blob/master/assets/syntaxes/02_Extra/Lean.sublime-syntax) (converted there from [leanprover/vscode-lean4](https://github.com/leanprover/vscode-lean4)'s `lean4.json` TextMate grammar).

Licensed under the Apache License 2.0 (see [vscode-lean4's LICENSE](https://github.com/leanprover/vscode-lean4/blob/master/LICENSE)).

## `ORCID.svg`

The ORCID iD icon, taken from the [ORCID brand guidelines](https://info.orcid.org/brand-guidelines/).

ORCID™, the ORCID logo, and the iD logo are trademarks of ORCID, Inc. They are not covered by an open-source license: they must be used in accordance with the brand guidelines and must not be altered. The file here is used unmodified.

## `springer-lecture-notes-in-computer-science.csl`

Springer LNCS citation style, modified from [citation-style-language/styles](https://github.com/citation-style-language/styles/blob/master/springer-lecture-notes-in-computer-science.csl).

Modifications, both following [`splncs04.bst`](https://ctan.org/tex-archive/macros/latex/contrib/llncs), the BibTeX style shipped with the official `llncs` LaTeX class:

- A `<sort>` block (author, then issue date, then title) was added to `<bibliography>`, so that the bibliography is ordered by author instead of by order of citation (see [Springer's guidelines for authors of proceedings](https://www.springer.com/gp/computer-science/lncs/conference-proceedings-guidelines), which permit either ordering).
- An `<else-if type="thesis">` branch, so that theses print their type and awarding institution, e.g. "Master's thesis, Università degli Studi di Firenze (2025)". The upstream style falls through to a generic branch that drops both.

Licensed under the [Creative Commons Attribution-ShareAlike 3.0 License](http://creativecommons.org/licenses/by-sa/3.0/), as stated in the original file.

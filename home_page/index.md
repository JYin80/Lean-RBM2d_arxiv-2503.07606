---
usemathjax: true
---

A Lean 4 / Mathlib formalization of the deterministic core of the two-dimensional
random band matrix paper, [arXiv:2503.07606](https://arxiv.org/abs/2503.07606).

* [Blueprint](https://jyin80.github.io/Lean-RBM2d_arxiv-2503.07606/blueprint/) — statements, proofs and their Lean counterparts
* [Dependency graph](https://jyin80.github.io/Lean-RBM2d_arxiv-2503.07606/blueprint/dep_graph_document.html) — green nodes are formalized
* [Blueprint as pdf](https://jyin80.github.io/Lean-RBM2d_arxiv-2503.07606/blueprint.pdf)
* [API documentation](https://jyin80.github.io/Lean-RBM2d_arxiv-2503.07606/docs/)
* [Repository](https://github.com/JYin80/Lean-RBM2d_arxiv-2503.07606)

Sister project: [Lean-RBM1d](https://jyin80.github.io/Lean-RBM1d_arxiv-2501.01718/), the $d=1$ paper.

## Scope

Mathlib has no Itô calculus for matrix-valued Brownian motion, no matrix SDEs and no
Dyson Brownian motion, so the loop hierarchy of Sections 5–7 cannot presently be
formalized. What can be — and what this project targets — is the deterministic
backbone: the propagator $\Theta^{(B)}_\xi = (1 - \xi S^{(B)})^{-1}$ on $\mathbb Z_L^2$,
and the whole of Section 8, which proves the sharp entrywise estimates on it.

Section 8 is the part of this paper that could not be inherited from the $d=1$ work:
on $\mathbb Z_L^2$ there is no three-term recursion and hence no closed form for
$\Theta^{(B)}_\xi$, so the Fourier route — ellipticity, contour shift, periodization,
dyadic decomposition — is the only one available.

## Status

The first batch of files is drafted but not yet compiled; see `docs/TASKS.md`.
Once it is green, everything in the repository is kept `sorry`-free and the axiom
set of every result is audited to be exactly `propext`, `Classical.choice`,
`Quot.sound`.

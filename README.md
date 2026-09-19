# RBM2D

A Lean 4 / Mathlib formalization of the **deterministic core** of the
two-dimensional random band matrix paper,
[arXiv:2503.07606](https://arxiv.org/abs/2503.07606).

Sister project: [RBM1D](https://github.com/JYin80/Lean-RBM1d_arxiv-2501.01718)
(the $d=1$ paper, arXiv:2501.01718).

## Scope

Mathlib currently has no Itô calculus for matrix-valued Brownian motion, no
matrix SDEs and no Dyson Brownian motion, so the loop hierarchy of Sections 5–7
cannot presently be formalized.  What *can* be — and what this project targets —
is the deterministic backbone:

* **Section 2.5** — the propagator `Θ^(B)_ξ = (1 - ξ S^(B))⁻¹` on `Z_L^2`
* **Section 8** — the proof of Lemma `lem_propTH`: Fourier setup, the ellipticity
  estimate, exponential decay at scale `ℓ̂(ξ) = min(|1-ξ|^{-1/2}, L)`, and the
  first- and second-difference bounds

Section 8 is the part of this paper that could *not* be inherited from the `d=1`
work: on `Z_L^2` there is no three-term recursion and hence no closed form for
`Θ^(B)_ξ`, so the Fourier route — ellipticity, contour shift, periodization,
dyadic decomposition — is the only one available.

## Status

See [`docs/STATUS.md`](docs/STATUS.md) and the work queue in
[`docs/TASKS.md`](docs/TASKS.md).

**The first batch of Lean files has not been compiled yet** — it was drafted in a
cloud session that cannot fetch the Mathlib olean cache.  Getting it to build is
work order T1.

Departures from the paper's literal statements (extra hypotheses, corrections)
are logged in [`docs/paper-deltas.md`](docs/paper-deltas.md) rather than applied
silently.

## Building

```bash
lake exe cache get
lake build
```

`./check.sh` writes a full build to `build.log`; `./watch.sh` rebuilds on every
source change.  For a single file, `lake env lean RBM2D/Propagator/Symbol.lean`.

## Blueprint

```bash
pip install leanblueprint
leanblueprint checkdecls   # verifies every \lean{...} tag resolves
leanblueprint web          # renders to blueprint/web/
```

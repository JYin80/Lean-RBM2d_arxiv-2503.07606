# RBM2D

A Lean 4 / Mathlib formalization of the **deterministic core** of the
two-dimensional random band matrix paper,
[arXiv:2503.07606](https://arxiv.org/abs/2503.07606).

Sister project: [RBM1D](https://github.com/JYin80/Lean-RBM1d_arxiv-2501.01718)
(the $d=1$ paper, arXiv:2501.01718).

## Scope

The project targets the full paper, beginning with its deterministic backbone:

* **Sections 2 and 8** — the two-dimensional block model, propagator
  `Θ^(B)_ξ = (1 - ξ S^(B))⁻¹`, and all six properties of Lemma `lem_propTH`.
* **Sections 3–7** — the loop hierarchy and probabilistic estimates. The plan
  replaces the paper's Brownian-time argument with one-time Gaussian laws,
  Gaussian integration by parts, a generator identity, moment bounds, and
  continuous induction; see [`docs/random-layer.md`](docs/random-layer.md).

Section 8 needs a new Fourier proof: the three-term recursion used in the
`d=1` project does not extend to `Z_L^2`. The current scope and dependencies are
recorded in [`docs/PLAN.md`](docs/PLAN.md). Any theorem imported from the paper
or left as an interface is recorded explicitly rather than presented as proved.

## Status

See [`docs/STATUS.md`](docs/STATUS.md) and the work queue in
[`docs/TASKS.md`](docs/TASKS.md).

T1 and the first Fourier layer have been compiled and checked in CI. The
remaining work includes the two hard bounds in Section 8, the two-dimensional
model layer, and the random-layer replacement stack. The current checkout's
local build status is tracked in [`docs/STATUS.md`](docs/STATUS.md).

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

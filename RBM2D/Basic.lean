/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/

/-!
# RBM2D

A Lean 4 / Mathlib formalization of the deterministic core of the
two-dimensional random band matrix paper (arXiv:2503.07606).

See `docs/STATUS.md` for what is formalized, `docs/PLAN.md` for the roadmap,
`docs/TASKS.md` for the work queue, `docs/paper-deltas.md` for the places where
the Lean statement departs from the paper, and `blueprint/` for the dependency
graph.

The file layout follows the paper:

* `RBM2D.Defs.Block`        — the block covariance matrix `S^(B)` on `Z_L^2`
* `RBM2D.Defs.Dist`         — the periodic `L^1` distance `|x|_L` on `Z_L^2`
* `RBM2D.Defs.Domination`   — Definition `stoch_domination` (ii), the deterministic `≺`
* `RBM2D.Propagator.Basic`  — Definition `def_Theta`, properties 1--4 of `lem_propTH`
* `RBM2D.Propagator.Bounds` — crude `ℓ^1` / `ℓ^∞` bounds on `Θ^(B)_ξ`
* `RBM2D.Propagator.Symbol` — Section 8.1, `(eq_symbol)` and `(eq_Fourier_rep)`
* `RBM2D.Propagator.Elliptic` — Section 8.1, `(eq_kappa_def)`, `(eq_qdef)`, `(eq_elliptic)`
* `RBM2D.Delocalization`    — the deterministic spectral core of Theorem `MR:decol`

The one structural difference from the one-dimensional project `RBM1D` is that
there is **no closed form** for `Θ^(B)_ξ`: in `d = 1` the nearest-neighbour
three-term recursion has a characteristic equation whose roots give
`(Θ_ξ)_{xy} = A(ξ)(ρ^d + ρ^{L-d})`, and the whole decay analysis rests on it.
On `Z_L^2` no such recursion exists, so the Fourier route of Section 8 --
ellipticity, contour shift, Poisson summation, dyadic decomposition -- is the
only route.  That is why `Propagator/Symbol.lean` and `Propagator/Elliptic.lean`
are load-bearing here and were optional in `RBM1D`.
-/

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/

/-!
# RBM2D

A Lean 4 / Mathlib formalization of the two-dimensional random band matrix paper
(arXiv:2503.07606): delocalization, the local semicircle law, generalized quantum unique
ergodicity, quantum diffusion and bulk universality for the band matrix on `Z_L^2` with blocks
of size `W^2`.

The five endpoint statements `RBM.Endpoints.{decol, locSC, QUE, QDiff, BUniv}` are stated in
`RBM2D/Endpoints.lean`.  The first four are proved in `RBM2D/Main/Endpoints.lean`; `BUniv`
is proved from the external input `L32` ([32] Theorem 2.2) in `RBM2D/Main/BUnivHolds.lean`.

The directory layout follows the paper:

* `RBM2D.Defs`         — the band model (block covariance `S^(B)` on `Z_L^2`), the periodic
  `L^1` distance `|x|_L`, stochastic domination (Definition `stoch_domination`), the semicircle
  law
* `RBM2D.Propagator`   — the propagator `Θ^(B)_ξ` (Definition `def_Theta`, `lem_propTH`) and
  its bounds; Section 8: the symbol `(eq_symbol)`, `(eq_Fourier_rep)`, ellipticity
  `(eq_kappa_def)`, `(eq_qdef)`, `(eq_elliptic)`, contour shift, Poisson summation, dyadic
  decomposition
* `RBM2D.Delocalization` — the deterministic spectral core of Theorem `MR:decol`
* `RBM2D.Gauss`, `RBM2D.Green`, `RBM2D.Loop`, `RBM2D.Hierarchy`, `RBM2D.Path`,
  `RBM2D.Evolution`, `RBM2D.Induction` — the Gaussian model and the Green function estimates,
  the loop hierarchy and the stochastic flow, the evolution kernel estimates and the induction
  on loop levels
* `RBM2D.Universality` — the Ornstein--Uhlenbeck flow and the GUE comparison used for
  Theorem `Thm: B_Univ`
* `RBM2D.Main`         — assembly of the five endpoint theorems

In contrast with `d = 1`, there is **no closed form** for `Θ^(B)_ξ` on `Z_L^2`: in `d = 1` the
nearest-neighbour three-term recursion has a characteristic equation whose roots give
`(Θ_ξ)_{xy} = A(ξ)(ρ^d + ρ^{L-d})`, and the whole decay analysis rests on it.  On `Z_L^2` no
such recursion exists, so the Fourier method of Section 8 -- ellipticity, contour shift,
Poisson summation, dyadic decomposition -- is the only approach.  That is why
`Propagator/Symbol.lean` and `Propagator/Elliptic.lean` are load-bearing.
-/

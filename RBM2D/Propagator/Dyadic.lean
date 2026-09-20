/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.GeomSum
import RBM2D.Propagator.ZeroMode
import RBM2D.Defs.Dist

/-!
# `(eq_dyadic)` as an interface, and Case 1 of the derivative bounds

Work order T18.  Section 8.3 decomposes the non-zero momenta of
`(eq_Fourier_rep)` into dyadic annuli `|p|_* ∼ 2^{-j}` and estimates the
contribution `K_r` of one annulus.  That per-annulus estimate is the hard part
(work orders T19-T22); **everything downstream of it is not**, and this file is
that everything.

Following the project rule -- never `axiom`, always a `structure` field or a
theorem parameter -- `(eq_dyadic)` is carried as `DyadicDecomp`.  Case 1 of
`(prop:BD1)` and `(prop:BD2)` is then a theorem today, and when T22 lands it
produces a `DyadicDecomp` and the four theorems below do not change by a
character.

## What is actually missing from Mathlib

Not summation by parts: `fwdDiff` and `fwdDiff_iter_eq_sum_shift` are in
`Mathlib/Algebra/Group/ForwardDiff.lean` and work for `M := Z2 L`, `G := ℂ`,
and on a finite abelian group summation by parts degenerates to a shift of the
index (`Fintype.sum_equiv (Equiv.addRight 1)`, boundary terms cancelling by
periodicity).  What is missing is a **quantitative, scale-uniform** derivative
bound for a cutoff: `ContDiffBump` carries no bound on
`‖iteratedFDeriv ℝ n f x‖` at all, so a dyadic family `χ(2^j ·)` gets one
constant per `j` and none uniform in `j` -- and uniformity in `j` is the whole
content of `(eq_dyadic)`.  T19 sidesteps this with an explicit degree-seven
smoothstep, for which the third difference is a polynomial inequality.

## Why `m = 1, 2` and no `m = 0`

The paper states `(eq_dyadic)` for `m = 0, 1, 2`, but `m = 0` has no consumer:
Section 8.2 never uses the dyadic decomposition at all (its two regimes go
through the contour shift and through a bare lattice sum), and Section 8.3
Case 1 uses only the first and second differences.  The fields below are
therefore `(eq_dyadic)` at `m = 1, 2` *after* the fundamental theorem of
calculus of `(eq_fd1)`/`(eq_fd2)` has been applied on a single annulus, which is
also the only form Case 1 consumes.

The second index is pinned to `0`; translation invariance
(`Theta_apply_add_right`, property 2) makes that no loss, exactly as in
`ZeroMode.lean`.
-/

namespace RBM

open Finset

/-- `(eq_dyadic)` of Section 8.3, carried as an interface rather than an axiom.
Every field is a theorem to be proved by work order T22; none is assumed to be
unprovable, and `#assert_rbm_axioms` stays at three names throughout. -/
structure DyadicDecomp (L : ℕ) [NeZero L] (ξ : ℂ) where
  /-- The number of dyadic scales.  Downstream `J ≈ log₂ L`; every estimate
  below, and all of `GeomSum.lean`, is uniform in `J`. -/
  J : ℕ
  /-- `K_r` of `(eq_dyadic)`: the contribution of the annulus `|p|_* ∼ 2^{-j}`
  to `(eq_Fourier_rep)`, as a function of `x = a - b`. -/
  Kr : ℕ → Z2 L → ℂ
  /-- The absolute constant `C_M` of `(eq_dyadic)` at `M = 3`, with the factor
  `2^M` from the segment estimate of Case 1 already absorbed. -/
  C : ℝ
  /-- `C` is a bound, so it is non-negative. -/
  C_nonneg : 0 ≤ C
  /-- The partition of unity: the zero mode of `Theta_apply_eq_zero_mode_add`
  together with the annuli reconstruct `(eq_Fourier_rep)`. -/
  theta_eq : ∀ u : Z2 L,
    Theta L ξ u 0 = ((L : ℂ) ^ 2)⁻¹ * (1 - ξ)⁻¹ + ∑ j ∈ Finset.range (J + 1), Kr j u
  /-- `(eq_dyadic)` at `m = 1`, per annulus, in the finite-difference form
  `(eq_fd1)` consumes.  The hypothesis `2|s|_L ≤ |u|_L` is Case 1's
  `|s|_L ≤ d/2`: it is what keeps the whole segment at distance `≥ d/2` from the
  origin, so that `(1 + r|y|_L)^{-3} ≤ 8 (1 + r d)^{-3}` along it. -/
  fd1 : ∀ u s : Z2 L, 2 * zdist2 L s ≤ zdist2 L u → ∀ j ∈ Finset.range (J + 1),
    ‖Kr j u - Kr j (u - s)‖
      ≤ C * (zdist2 L s : ℝ) *
          (dyad j ^ 3 / (kappa ξ ^ 2 + dyad j ^ 2)
            * (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ))
  /-- `(eq_dyadic)` at `m = 2`, per annulus, in the form `(eq_fd2)` consumes. -/
  fd2 : ∀ u s : Z2 L, 2 * zdist2 L s ≤ zdist2 L u → ∀ j ∈ Finset.range (J + 1),
    ‖2 * Kr j u - Kr j (u - s) - Kr j (u + s)‖
      ≤ C * (zdist2 L s : ℝ) ^ 2 *
          (dyad j ^ 4 / (kappa ξ ^ 2 + dyad j ^ 2)
            * (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ))

variable {L : ℕ} [NeZero L] {ξ : ℂ}

/-- `(eq_fd1)` summed against `(eq_dyadic_sum1)`: Case 1 of `(prop:BD1)`. -/
theorem norm_Theta_fd1_le (H : DyadicDecomp L ξ) {u s : Z2 L}
    (hs : 2 * zdist2 L s ≤ zdist2 L u) :
    ‖Theta L ξ u 0 - Theta L ξ (u - s) 0‖
      ≤ H.C * (zdist2 L s : ℝ)
          * (8 * ((zdist2 L u : ℝ) + 1)⁻¹ + 8 * (ellhat L ξ)⁻¹) := by
  have hdiff : Theta L ξ u 0 - Theta L ξ (u - s) 0
      = ∑ j ∈ Finset.range (H.J + 1), (H.Kr j u - H.Kr j (u - s)) := by
    rw [H.theta_eq u, H.theta_eq (u - s), Finset.sum_sub_distrib]
    ring
  rw [hdiff]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (H.fd1 u s hs)) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (dyadic_sum_three_le L ξ (zdist2 L u) H.J) ?_
  exact mul_nonneg H.C_nonneg (Nat.cast_nonneg _)

/-- `(eq_fd2)` summed against `(eq_dyadic_sum2)`: Case 1 of `(prop:BD2)`. -/
theorem norm_Theta_fd2_le (H : DyadicDecomp L ξ) {u s : Z2 L}
    (hs : 2 * zdist2 L s ≤ zdist2 L u) :
    ‖2 * Theta L ξ u 0 - Theta L ξ (u - s) 0 - Theta L ξ (u + s) 0‖
      ≤ H.C * (zdist2 L s : ℝ) ^ 2
          * (8 * ((zdist2 L u : ℝ) ^ 2 + 1)⁻¹ + 8 * (ellhat L ξ) ^ (-2 : ℤ)) := by
  have hdiff : 2 * Theta L ξ u 0 - Theta L ξ (u - s) 0 - Theta L ξ (u + s) 0
      = ∑ j ∈ Finset.range (H.J + 1),
          (2 * H.Kr j u - H.Kr j (u - s) - H.Kr j (u + s)) := by
    rw [H.theta_eq u, H.theta_eq (u - s), H.theta_eq (u + s),
      show (∑ j ∈ Finset.range (H.J + 1),
            (2 * H.Kr j u - H.Kr j (u - s) - H.Kr j (u + s)))
          = 2 * (∑ j ∈ Finset.range (H.J + 1), H.Kr j u)
            - (∑ j ∈ Finset.range (H.J + 1), H.Kr j (u - s))
            - (∑ j ∈ Finset.range (H.J + 1), H.Kr j (u + s)) from by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]]
    ring
  rw [hdiff]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (H.fd2 u s hs)) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (dyadic_sum_four_le L ξ (zdist2 L u) H.J) ?_
  exact mul_nonneg H.C_nonneg (sq_nonneg _)

omit [NeZero L] in
/-- `ℓ̂⁻¹ ≤ (κ ℓ̂²)⁻¹`, the rescaling the paper performs between
`(eq_dyadic_sum1)` and `(prop:BD1)`.  It is exactly `κ ℓ̂ ≤ 1`. -/
theorem inv_ellhat_le_inv_kappa_mul_sq (hL : 3 ≤ L) (hξ : ‖ξ‖ < 1) :
    (ellhat L ξ)⁻¹ ≤ (kappa ξ * (ellhat L ξ) ^ 2)⁻¹ := by
  have hpos : 0 < ellhat L ξ := ellhat_pos L hL hξ
  have hk : 0 < kappa ξ := kappa_pos hξ
  have hnum : kappa ξ * (ellhat L ξ) ^ 2 ≤ ellhat L ξ := by
    nlinarith [kappa_mul_ellhat_le_one L hξ]
  exact inv_anti₀ (by positivity) hnum

/-- `(prop:BD1)`, Case 1, in the paper's own shape. -/
theorem norm_Theta_fd1_le_paper (H : DyadicDecomp L ξ) (hL : 3 ≤ L) (hξ : ‖ξ‖ < 1)
    {u s : Z2 L} (hs : 2 * zdist2 L s ≤ zdist2 L u) :
    ‖Theta L ξ u 0 - Theta L ξ (u - s) 0‖
      ≤ 8 * H.C * ((zdist2 L s : ℝ) * ((zdist2 L u : ℝ) + 1)⁻¹
          + (zdist2 L s : ℝ) * (kappa ξ * (ellhat L ξ) ^ 2)⁻¹) := by
  refine le_trans (norm_Theta_fd1_le H hs) ?_
  have h := inv_ellhat_le_inv_kappa_mul_sq (L := L) (ξ := ξ) hL hξ
  have hCs : 0 ≤ H.C := H.C_nonneg
  have hsn : (0 : ℝ) ≤ (zdist2 L s : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hCs hsn]

/-- `(prop:BD2)`, Case 1, in the paper's own shape. -/
theorem norm_Theta_fd2_le_paper (H : DyadicDecomp L ξ) {u s : Z2 L}
    (hs : 2 * zdist2 L s ≤ zdist2 L u) :
    ‖2 * Theta L ξ u 0 - Theta L ξ (u - s) 0 - Theta L ξ (u + s) 0‖
      ≤ 8 * H.C * ((zdist2 L s : ℝ) ^ 2 * ((zdist2 L u : ℝ) ^ 2 + 1)⁻¹
          + (zdist2 L s : ℝ) ^ 2 * ((ellhat L ξ) ^ 2)⁻¹) := by
  refine le_trans (norm_Theta_fd2_le H hs) ?_
  have hzp : (ellhat L ξ) ^ (-2 : ℤ) = ((ellhat L ξ) ^ 2)⁻¹ := by
    rw [zpow_neg]; norm_num
  rw [hzp]
  have hCs : 0 ≤ H.C := H.C_nonneg
  nlinarith [mul_nonneg hCs (sq_nonneg ((zdist2 L s : ℝ)))]

end RBM

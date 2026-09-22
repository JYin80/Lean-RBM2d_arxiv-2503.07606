/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.Momentum
import RBM2D.Propagator.Cutoff

/-!
# Resolvent denominator on a dyadic momentum annulus

The lower bound uses the inner radius only. The cutoff below is evaluated at
the unnormalized Euclidean momentum radius; a later partition argument must
handle normalization and the low-frequency endpoint separately.
-/

namespace RBM

/-- A dyadic inner-radius bound, with the exact ellipticity constant retained. -/
theorem norm_one_sub_mul_Shat_ge_dyadic (L : ℕ) [NeZero L]
    {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p : Z2 L) (j : ℕ)
    (hinner : (dyad (j + 1)) ^ 2 ≤ pstar2 L p) :
    4 / (45 * Real.pi ^ 2) *
        ((kappa ξ) ^ 2 + (dyad (j + 1)) ^ 2) ≤
      ‖1 - ξ * Shat L p‖ := by
  calc
    4 / (45 * Real.pi ^ 2) *
        ((kappa ξ) ^ 2 + (dyad (j + 1)) ^ 2) ≤
      4 / (45 * Real.pi ^ 2) * ((kappa ξ) ^ 2 + pstar2 L p) := by
        gcongr
    _ ≤ ‖1 - ξ * Shat L p‖ :=
      norm_one_sub_mul_Shat_ge_pstar L hξ p

/-- A nonzero annular cutoff supplies the required lower momentum radius. -/
theorem norm_one_sub_mul_Shat_ge_of_dyadicCutoff_ne_zero (L : ℕ) [NeZero L]
    {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p : Z2 L) (j : ℕ)
    (hcut : dyadicCutoff j (Real.sqrt (pstar2 L p)) ≠ 0) :
    4 / (45 * Real.pi ^ 2) *
        ((kappa ξ) ^ 2 + (dyad (j + 1)) ^ 2) ≤
      ‖1 - ξ * Shat L p‖ := by
  have hinner : dyad (j + 1) ≤ Real.sqrt (pstar2 L p) :=
    (dyadicCutoff_support j _ hcut).1
  have hsq : (dyad (j + 1)) ^ 2 ≤ pstar2 L p := by
    have h := (sq_le_sq₀ (dyad_nonneg (j + 1))
      (Real.sqrt_nonneg (pstar2 L p))).2 hinner
    simpa only [Real.sq_sqrt (pstar2_nonneg L p)] using h
  exact norm_one_sub_mul_Shat_ge_dyadic L hξ p j hsq

/-- A nonzero momentum and resolvent parameter satisfy the inner-radius condition. -/
example :
    4 / (45 * Real.pi ^ 2) *
        ((kappa (1 / 2 : ℂ)) ^ 2 + (dyad 1) ^ 2) ≤
      ‖1 - (1 / 2 : ℂ) * Shat 3 (1, 0)‖ := by
  apply norm_one_sub_mul_Shat_ge_dyadic 3 (by norm_num) (1, 0) 0
  have hz : zdist 3 (1 : ZMod 3) = 1 := by decide
  simp only [dyad, pstar2, pstar, hz, zdist_zero]
  norm_num
  nlinarith [Real.pi_gt_three]

end RBM

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.CombesThomasFixedGap

/-!
# Combes–Thomas bound parameterized by a spectral gap

The real gap `0 < δ ≤ 1` and `‖ξ‖ ≤ 1 - δ` admit the explicit weight
`t = log (1 + δ/2)`. This remains within the Neumann regime `‖ξ‖ < 1`.
-/

namespace RBM

variable (L : ℕ) [NeZero L]

/-- The explicit gap-dependent exponential weight satisfies the weighted inverse gate. -/
theorem gap_parameter_weighted_gate {δ : ℝ} {ξ : ℂ}
    (hδ : 0 < δ) (_hδone : δ ≤ 1) (hξ : ‖ξ‖ ≤ 1 - δ) :
    ‖ξ‖ * Real.exp (Real.log (1 + δ / 2)) < 1 := by
  have hfac : 0 ≤ 1 + δ / 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hξ hfac
  have hden : δ / 2 ≤ 1 - ‖ξ‖ * (1 + δ / 2) := by
    nlinarith [sq_nonneg δ]
  rw [Real.exp_log (by positivity)]
  linarith

/-- The inverse prefactor at the chosen weight is at most `2/δ`. -/
theorem gap_parameter_inverse_prefactor_le {δ : ℝ} {ξ : ℂ}
    (hδ : 0 < δ) (_hδone : δ ≤ 1) (hξ : ‖ξ‖ ≤ 1 - δ) :
    (1 - ‖ξ‖ * (1 + δ / 2))⁻¹ ≤ 2 / δ := by
  have hfac : 0 ≤ 1 + δ / 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hξ hfac
  have hden : δ / 2 ≤ 1 - ‖ξ‖ * (1 + δ / 2) := by
    nlinarith [sq_nonneg δ]
  have hpos : 0 < 1 - ‖ξ‖ * (1 + δ / 2) := by linarith
  rw [← one_div]
  exact (div_le_div_iff₀ hpos hδ).mpr (by nlinarith)

/-- Geometric kernel decay at the explicit gap-dependent rate. -/
theorem norm_Theta_apply_le_gap_parameter (hL : 3 ≤ L)
    {δ : ℝ} {ξ : ℂ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hξ : ‖ξ‖ ≤ 1 - δ) (a b : Z2 L) :
    ‖Theta L ξ a b‖ ≤
      (2 / δ) * Real.exp (-(Real.log (1 + δ / 2) *
        (zdist2 L (a - b) : ℝ))) := by
  have ht : 0 ≤ Real.log (1 + δ / 2) :=
    Real.log_nonneg (by linarith)
  have hbase := norm_Theta_apply_le_exp_zdist2 L hL ht
    (gap_parameter_weighted_gate hδ hδone hξ) a b
  have hden := gap_parameter_inverse_prefactor_le hδ hδone hξ
  rw [Real.exp_log (by positivity)] at hbase
  calc
    ‖Theta L ξ a b‖ ≤
        Real.exp (-(Real.log (1 + δ / 2) * (zdist2 L (a - b) : ℝ))) *
          (1 - ‖ξ‖ * (1 + δ / 2))⁻¹ := hbase
    _ ≤ Real.exp (-(Real.log (1 + δ / 2) * (zdist2 L (a - b) : ℝ))) *
          (2 / δ) := mul_le_mul_of_nonneg_left hden (le_of_lt (Real.exp_pos _))
    _ = (2 / δ) * Real.exp (-(Real.log (1 + δ / 2) *
          (zdist2 L (a - b) : ℝ))) := by ring

end RBM

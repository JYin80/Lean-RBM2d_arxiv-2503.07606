/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.CombesThomasKernelDecay

/-!
# A fixed-gap Combes–Thomas estimate

Choosing the exponential weight with `t = log 2` gives a geometric decay
bound in the explicit regime `‖ξ‖ < 1/2`.
-/

namespace RBM

variable (L : ℕ) [NeZero L]

private theorem exp_neg_log_two_mul_nat (d : ℕ) :
    Real.exp (-(Real.log 2 * (d : ℝ))) = (1 / 2 : ℝ) ^ d := by
  calc
    Real.exp (-(Real.log 2 * (d : ℝ))) =
        Real.exp ((d : ℝ) * (-Real.log 2)) := by congr 1; ring
    _ = Real.exp (-Real.log 2) ^ d := Real.exp_nat_mul _ _
    _ = ((2 : ℝ)⁻¹) ^ d := by rw [Real.exp_neg, Real.exp_log (by norm_num)]
    _ = (1 / 2 : ℝ) ^ d := by norm_num

/-- Uniform geometric kernel decay when the spectral parameter has norm below `1/2`. -/
theorem norm_Theta_apply_le_geometric (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1 / 2) (a b : Z2 L) :
    ‖Theta L ξ a b‖ ≤
      (1 / 2 : ℝ) ^ (zdist2 L (a - b)) * (1 - 2 * ‖ξ‖)⁻¹ := by
  have ht : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hexp : Real.exp (Real.log (2 : ℝ)) = 2 := Real.exp_log (by norm_num)
  have hsmall : ‖ξ‖ * Real.exp (Real.log (2 : ℝ)) < 1 := by
    rw [hexp]
    nlinarith
  have h := norm_Theta_apply_le_exp_zdist2 L hL ht hsmall a b
  simpa only [hexp, exp_neg_log_two_mul_nat, mul_comm ‖ξ‖ (2 : ℝ)] using h

/-- A fixed constant `2` suffices when `‖ξ‖ ≤ 1/4`. -/
theorem norm_Theta_apply_le_two_geometric (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1 / 4) (a b : Z2 L) :
    ‖Theta L ξ a b‖ ≤ 2 * (1 / 2 : ℝ) ^ (zdist2 L (a - b)) := by
  have hhalf : ‖ξ‖ < 1 / 2 := by linarith
  have hbase := norm_Theta_apply_le_geometric L hL hhalf a b
  have hpos : 0 < 1 - 2 * ‖ξ‖ := by linarith
  have hden : (1 - 2 * ‖ξ‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hpos).mpr
    nlinarith
  calc
    ‖Theta L ξ a b‖ ≤
        (1 / 2 : ℝ) ^ (zdist2 L (a - b)) * (1 - 2 * ‖ξ‖)⁻¹ := hbase
    _ ≤ (1 / 2 : ℝ) ^ (zdist2 L (a - b)) * 2 :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = 2 * (1 / 2 : ℝ) ^ (zdist2 L (a - b)) := by ring

end RBM

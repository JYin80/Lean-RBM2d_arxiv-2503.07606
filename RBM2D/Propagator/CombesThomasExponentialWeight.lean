/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.CombesThomasDistanceWeight

/-!
# Exponential distance weight for the block walk

The weight centered at a block is exponential in the periodic graph distance.
Its conjugation perturbation is bounded by `exp t - 1` for `t ≥ 0`.
-/

namespace RBM

open Matrix
open scoped NNReal Matrix.Norms.Operator

variable (L : ℕ) [NeZero L]

/-- The exponential periodic-distance weight, viewed as a complex scalar. -/
noncomputable def blockExponentialWeight (c : Z2 L) (t : ℝ) (a : Z2 L) : ℂ :=
  (Real.exp (t * (zdist2 L (a - c) : ℝ)) : ℂ)

omit [NeZero L] in
theorem blockExponentialWeight_ne_zero (c : Z2 L) (t : ℝ) (a : Z2 L) :
    blockExponentialWeight L c t a ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)

private theorem abs_exp_sub_one_le {d t : ℝ}
    (hupper : d ≤ t) (hlower : -t ≤ d) :
    |Real.exp d - 1| ≤ Real.exp t - 1 := by
  have hle : Real.exp d ≤ Real.exp t := Real.exp_le_exp.mpr hupper
  have hge : Real.exp (-t) ≤ Real.exp d := Real.exp_le_exp.mpr hlower
  have hneg := Real.add_one_le_exp (-t)
  have hpos := Real.add_one_le_exp t
  apply abs_le.mpr
  constructor <;> linarith

private theorem exp_ratio_bound {t x y : ℝ} (ht : 0 ≤ t)
    (hxy : x ≤ y + 1) (hyx : y ≤ x + 1) :
    |Real.exp (t * x) / Real.exp (t * y) - 1| ≤ Real.exp t - 1 := by
  have hupper : t * (x - y) ≤ t := by
    have h : x - y ≤ 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h ht]
  have hlower : -t ≤ t * (x - y) := by
    have h : -1 ≤ x - y := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h ht]
  rw [← Real.exp_sub, ← mul_sub]
  exact abs_exp_sub_one_le hupper hlower

/-- Actual walk edges have exponential-weight ratio deviation at most `exp t - 1`. -/
theorem blockExponentialWeight_edge_ratio_le (hL : 3 ≤ L) (c a b : Z2 L)
    {t : ℝ} (ht : 0 ≤ t) (hab : SB L a b ≠ 0) :
    ‖blockExponentialWeight L c t a * (blockExponentialWeight L c t b)⁻¹ - 1‖₊
      ≤ Real.toNNReal (Real.exp t - 1) := by
  obtain ⟨habd, hbad⟩ := zdist2_center_edge_le L hL c a b hab
  have hdelta : 0 ≤ Real.exp t - 1 := by linarith [Real.add_one_le_exp t]
  apply NNReal.coe_le_coe.mp
  rw [coe_nnnorm, Real.coe_toNNReal _ hdelta]
  change ‖(Real.exp (t * (zdist2 L (a - c) : ℝ)) : ℂ) *
    ((Real.exp (t * (zdist2 L (b - c) : ℝ)) : ℂ))⁻¹ - 1‖ ≤ Real.exp t - 1
  rw [← div_eq_mul_inv, ← Complex.ofReal_div]
  norm_cast
  apply exp_ratio_bound ht
  · exact_mod_cast habd
  · exact_mod_cast hbad

/-- The exponential-weight conjugation is a small perturbation when `t` is small. -/
theorem nnnorm_blockExponentialWeight_SB_sub_le (hL : 3 ≤ L)
    (c : Z2 L) {t : ℝ} (ht : 0 ≤ t) :
    ‖blockWeightMatrix L (blockExponentialWeight L c t) * SB L *
      blockWeightInverse L (blockExponentialWeight L c t) - SB L‖₊
        ≤ Real.toNNReal (Real.exp t - 1) := by
  exact nnnorm_blockWeight_SB_sub_le L hL _ _
    (fun a b hab => blockExponentialWeight_edge_ratio_le L hL c a b ht hab)

end RBM

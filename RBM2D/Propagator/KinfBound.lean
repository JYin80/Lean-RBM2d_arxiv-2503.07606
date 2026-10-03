/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.KinfSwap
import RBM2D.Propagator.KinfBoundFirst

/-!
# The `L¹` bound on the infinite-volume kernel

`|K_{ξ,∞}(x)| ≤ 180 log(2+κ⁻¹) exp(-κ(|x₁|+|x₂|)/20000)` (equation `(eq_Kinf_bound)`), from the
first-coordinate bound `norm_Kinf_le_first`, the swap symmetry `Kinf_swap`, and
`max(|x₁|,|x₂|) ≥ (|x₁|+|x₂|)/2`.
-/

namespace RBM

open Real

private theorem KinfBound_step (κ a b A : ℝ) (hκ : 0 < κ) (hA : 0 ≤ A)
    (hba : b ≤ a) :
    A * Real.exp (-(κ * a) / 10000) ≤ A * Real.exp (-(κ * (a + b)) / 20000) := by
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA
  have h : κ * b ≤ κ * a := mul_le_mul_of_nonneg_left hba hκ.le
  linarith

theorem norm_Kinf_le :
    ∀ ξ : ℂ, ‖ξ‖ < 1 → ∀ x : ℤ × ℤ,
      ‖Kinf ξ x‖ ≤ 180 * Real.log (2 + (kappa ξ)⁻¹) *
        Real.exp (-(kappa ξ * (|(x.1 : ℝ)| + |(x.2 : ℝ)|)) / 20000) := by
  intro ξ hξ x
  have hκ : 0 < kappa ξ := kappa_pos hξ
  have hlog : 0 ≤ Real.log (2 + (kappa ξ)⁻¹) :=
    Real.log_nonneg (by have := inv_nonneg.mpr hκ.le; linarith)
  have hA : 0 ≤ 180 * Real.log (2 + (kappa ξ)⁻¹) := by positivity
  rcases le_total |(x.2 : ℝ)| |(x.1 : ℝ)| with h | h
  · exact le_trans (norm_Kinf_le_first ξ hξ x)
      (KinfBound_step _ _ _ _ hκ hA h)
  · have h1 := norm_Kinf_le_first ξ hξ (x.2, x.1)
    rw [Kinf_swap ξ hξ x] at h1
    refine le_trans h1 ?_
    have h2 := KinfBound_step (kappa ξ) |(x.2 : ℝ)| |(x.1 : ℝ)|
      (180 * Real.log (2 + (kappa ξ)⁻¹)) hκ hA h
    rw [add_comm |(x.2 : ℝ)| |(x.1 : ℝ)|] at h2
    exact h2

end RBM

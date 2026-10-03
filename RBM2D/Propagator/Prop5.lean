/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.Decay
import RBM2D.Propagator.DecayLarge
import RBM2D.Propagator.Harmonic
import RBM2D.Defs.Domination
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Property 5 (`prop:ThfadC`): merge of the two regimes

The bound `‖Θ_ξ(a,b)‖ ≤ C (1 + log L) (κ² ℓ̂²)⁻¹ exp (-|a-b|_L / (20000 ℓ̂))` for all
`3 ≤ L`, `‖ξ‖ < 1`, from `norm_Theta_apply_le_small_kappa_log` (`κL < 1`) and
`norm_Theta_apply_le_large_kappa` (`κL ≥ 1`).
-/

namespace RBM

open Filter

/-- Property 5 (`prop:ThfadC`) with explicit constants, for all `3 ≤ L`, all `‖ξ‖ < 1`
and all `a, b`. -/
theorem norm_Theta_apply_le_prop5 :
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ < 1 → ∀ a b : Z2 L,
      ‖Theta L ξ a b‖ ≤ 180 * 40002 ^ 2 * (1 + Real.log L) *
        ((kappa ξ) ^ 2 * (ellhat L ξ) ^ 2)⁻¹ *
        Real.exp (-(zdist2 L (a - b) : ℝ) / (20000 * ellhat L ξ)) := by
  intro L _ hL ξ hξ a b
  by_cases hs : kappa ξ * (L : ℝ) < 1
  · have h1 := norm_Theta_apply_le_small_kappa_log L hL hξ hs a b
    have hℓ : 0 < ellhat L ξ := ellhat_pos L hL hξ
    have hz : (0 : ℝ) ≤ (zdist2 L (a - b) : ℝ) := Nat.cast_nonneg _
    have hexp : Real.exp (-(zdist2 L (a - b) : ℝ) / ellhat L ξ) ≤
        Real.exp (-(zdist2 L (a - b) : ℝ) / (20000 * ellhat L ξ)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left hz hℓ (by linarith)
    have hlog : 0 ≤ 1 + Real.log L := by
      have := Real.log_natCast_nonneg L
      linarith
    have hinv : 0 ≤ ((kappa ξ) ^ 2 * (ellhat L ξ) ^ 2)⁻¹ := by positivity
    have he : 46 * Real.exp 1 ≤ 180 * 40002 ^ 2 := by
      have := Real.exp_one_lt_three
      norm_num
      linarith
    calc ‖Theta L ξ a b‖
        ≤ 46 * Real.exp 1 * (1 + Real.log L) *
            ((kappa ξ) ^ 2 * (ellhat L ξ) ^ 2)⁻¹ *
            Real.exp (-(zdist2 L (a - b) : ℝ) / ellhat L ξ) := h1
      _ ≤ 180 * 40002 ^ 2 * (1 + Real.log L) *
            ((kappa ξ) ^ 2 * (ellhat L ξ) ^ 2)⁻¹ *
            Real.exp (-(zdist2 L (a - b) : ℝ) / (20000 * ellhat L ξ)) := by
          gcongr
  · exact norm_Theta_apply_le_large_kappa L hL ξ hξ (not_lt.mp hs) a b

end RBM

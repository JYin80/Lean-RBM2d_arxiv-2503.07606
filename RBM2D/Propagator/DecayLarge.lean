/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.KinfBound
import RBM2D.Propagator.PeriodizeImageSum
import RBM2D.Propagator.PeriodizeKinfSummable

/-!
# Property 5 (`prop:ThfadC`) in the regime `κL ≥ 1` (Section 8.2)

In the regime `κL ≥ 1` one has `ℓ̂ = κ⁻¹` (Section 8.2). Writing
`Θ_ab = Σₙ Kinf(lift(a - b) + L n)` (`Theta_apply_periodized`), the triangle inequality, the
`L¹` kernel bound `norm_Kinf_le` and the image sum `tsum_exp_neg_l1_periodized_le` with
`α = κ/20000` (so `20000 α L = κL ≥ 1`) give the bound, with `log(2 + κ⁻¹) ≤ 1 + log L`.

This is only the `κL ≥ 1` half of property 5, not the statement for all `‖ξ‖ < 1`.
-/

namespace RBM

/-- `log (2 + κ⁻¹) ≤ 1 + log L` when `κ⁻¹ ≤ L` and `3 ≤ L`. -/
private theorem DecayLarge_log_le (L : ℕ) (hL : 3 ≤ L) {k : ℝ} (hk : 0 < k)
    (hkL : k⁻¹ ≤ (L : ℝ)) : Real.log (2 + k⁻¹) ≤ 1 + Real.log L := by
  have hL3 : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hki : 0 < k⁻¹ := inv_pos.mpr hk
  calc Real.log (2 + k⁻¹) ≤ Real.log (2 + (L : ℝ)) :=
        Real.log_le_log (by linarith) (by linarith)
    _ ≤ Real.log (2 * (L : ℝ)) := Real.log_le_log (by linarith) (by linarith)
    _ = Real.log 2 + Real.log L := Real.log_mul (by norm_num) (by linarith)
    _ ≤ 1 + Real.log L := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        linarith

/-- Property 5 (`prop:ThfadC`) of `lem_propTH` in the regime `κL ≥ 1`, with explicit constants. -/
theorem norm_Theta_apply_le_large_kappa :
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ < 1 → 1 ≤ kappa ξ * (L : ℝ) →
      ∀ a b : Z2 L,
        ‖Theta L ξ a b‖ ≤ 180 * 40002 ^ 2 * (1 + Real.log L) *
          ((kappa ξ) ^ 2 * (ellhat L ξ) ^ 2)⁻¹ *
          Real.exp (-(zdist2 L (a - b) : ℝ) / (20000 * ellhat L ξ)) := by
  intro L _ hL ξ hξ hκL a b
  have hκ : 0 < kappa ξ := kappa_pos hξ
  have hinvle : (kappa ξ)⁻¹ ≤ (L : ℝ) := by
    rw [inv_le_iff_one_le_mul₀ hκ]
    linarith
  have hell : ellhat L ξ = (kappa ξ)⁻¹ := min_eq_left hinvle
  rw [Theta_apply_periodized L hL hξ (Kinf ξ) (summable_Kinf_periodized L hL ξ hξ)
    (fun x => Kinf_sub_latticeFiveAverage ξ hξ x) a b]
  unfold periodizedTorusKernel periodizeKernel
  set α : ℝ := kappa ξ / 20000 with hαdef
  have hα : 0 < α := div_pos hκ (by norm_num)
  have hαL : 1 ≤ 20000 * α * L := by
    rw [hαdef, show 20000 * (kappa ξ / 20000) = kappa ξ by ring]
    exact hκL
  obtain ⟨hsum, hle⟩ := tsum_exp_neg_l1_periodized_le L α hα hαL (a - b)
  set A : ℝ := 180 * Real.log (2 + (kappa ξ)⁻¹) with hAdef
  have hA : 0 ≤ A := by
    have h1 : (1 : ℝ) ≤ 2 + (kappa ξ)⁻¹ := by
      have := inv_pos.mpr hκ
      linarith
    have := Real.log_nonneg h1
    rw [hAdef]
    positivity
  set w : ℤ × ℤ := torusLatticeLift (a - b) with hwdef
  have hpt : ∀ n : ℤ × ℤ, ‖Kinf ξ (w + L • n)‖ ≤
      A * Real.exp (-(α * (|((w + L • n).1 : ℝ)| + |((w + L • n).2 : ℝ)|))) := by
    intro n
    refine (norm_Kinf_le ξ hξ (w + L • n)).trans_eq ?_
    rw [hAdef, hαdef]
    congr 2
    ring
  have hsumA := hsum.mul_left A
  have hsumN : Summable (fun n : ℤ × ℤ => ‖Kinf ξ (w + L • n)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsumA
  have hlog : Real.log (2 + (kappa ξ)⁻¹) ≤ 1 + Real.log L := DecayLarge_log_le L hL hκ hinvle
  have hpref : ((kappa ξ) ^ 2 * (ellhat L ξ) ^ 2)⁻¹ = 1 := by
    rw [hell]
    field_simp
  have hexp : -(zdist2 L (a - b) : ℝ) / (20000 * ellhat L ξ) =
      -(α * (zdist2 L (a - b) : ℝ)) := by
    rw [hell, hαdef]
    field_simp
  have hE : 0 ≤ (40002 : ℝ) ^ 2 * Real.exp (-(α * (zdist2 L (a - b) : ℝ))) := by positivity
  calc ‖∑' n : ℤ × ℤ, Kinf ξ (w + L • n)‖
      ≤ ∑' n : ℤ × ℤ, ‖Kinf ξ (w + L • n)‖ := norm_tsum_le_tsum_norm hsumN
    _ ≤ ∑' n : ℤ × ℤ,
          A * Real.exp (-(α * (|((w + L • n).1 : ℝ)| + |((w + L • n).2 : ℝ)|))) :=
        Summable.tsum_le_tsum hpt hsumN hsumA
    _ = A * ∑' n : ℤ × ℤ,
          Real.exp (-(α * (|((w + L • n).1 : ℝ)| + |((w + L • n).2 : ℝ)|))) := tsum_mul_left
    _ ≤ A * ((40002 : ℝ) ^ 2 * Real.exp (-(α * (zdist2 L (a - b) : ℝ)))) :=
        mul_le_mul_of_nonneg_left hle hA
    _ ≤ (180 * (1 + Real.log L)) *
          ((40002 : ℝ) ^ 2 * Real.exp (-(α * (zdist2 L (a - b) : ℝ)))) := by
        apply mul_le_mul_of_nonneg_right _ hE
        rw [hAdef]
        linarith
    _ = 180 * 40002 ^ 2 * (1 + Real.log L) *
          ((kappa ξ) ^ 2 * (ellhat L ξ) ^ 2)⁻¹ *
          Real.exp (-(zdist2 L (a - b) : ℝ) / (20000 * ellhat L ξ)) := by
        rw [hpref, hexp]
        ring

end RBM

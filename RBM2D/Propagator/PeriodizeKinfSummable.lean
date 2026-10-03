/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.KinfBound
import RBM2D.Propagator.PeriodizeConvergence
import RBM2D.Propagator.PeriodizeResolventBridge
import RBM2D.Propagator.PeriodizeIntegrand

/-!
# Summability of the shifted `Kinf` lattice sums

For `w = torusLatticeLift u + δ` one has `|w + L n|₁ ≥ L · max(|n₁|,|n₂|) - |w|₁`, so `norm_Kinf_le`
gives a geometric max-radius majorant with ratio `exp (-κ L / 20000) < 1`. This supplies the
summability hypothesis of `Theta_apply_periodized` for `K = Kinf ξ`.
-/

namespace RBM

private theorem PeriodizeKinfSummable_lower (L : ℕ) (w n : ℤ × ℤ) :
    (L : ℝ) * (latticeMaxRadius n : ℝ) - (|(w.1 : ℝ)| + |(w.2 : ℝ)|) ≤
      |((w + L • n).1 : ℝ)| + |((w + L • n).2 : ℝ)| := by
  have h1 : (L : ℝ) * |(n.1 : ℝ)| - |(w.1 : ℝ)| ≤ |((w + L • n).1 : ℝ)| := by
    have : ((w + L • n).1 : ℝ) = (w.1 : ℝ) + (L : ℝ) * (n.1 : ℝ) := by
      simp
    rw [this]
    have := abs_sub_abs_le_abs_sub ((L : ℝ) * (n.1 : ℝ)) (-(w.1 : ℝ))
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg L)] at this
    have e : (L : ℝ) * (n.1 : ℝ) - -(w.1 : ℝ) = (w.1 : ℝ) + (L : ℝ) * (n.1 : ℝ) := by ring
    rw [e, abs_neg] at this
    exact this
  have h2 : (L : ℝ) * |(n.2 : ℝ)| - |(w.2 : ℝ)| ≤ |((w + L • n).2 : ℝ)| := by
    have : ((w + L • n).2 : ℝ) = (w.2 : ℝ) + (L : ℝ) * (n.2 : ℝ) := by
      simp
    rw [this]
    have := abs_sub_abs_le_abs_sub ((L : ℝ) * (n.2 : ℝ)) (-(w.2 : ℝ))
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg L)] at this
    have e : (L : ℝ) * (n.2 : ℝ) - -(w.2 : ℝ) = (w.2 : ℝ) + (L : ℝ) * (n.2 : ℝ) := by ring
    rw [e, abs_neg] at this
    exact this
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have a1 : 0 ≤ |(w.1 : ℝ)| := abs_nonneg _
  have a2 : 0 ≤ |(w.2 : ℝ)| := abs_nonneg _
  have b1 : 0 ≤ |((w + L • n).1 : ℝ)| := abs_nonneg _
  have b2 : 0 ≤ |((w + L • n).2 : ℝ)| := abs_nonneg _
  have c1 : 0 ≤ |(n.1 : ℝ)| := abs_nonneg _
  have c2 : 0 ≤ |(n.2 : ℝ)| := abs_nonneg _
  unfold latticeMaxRadius
  rcases le_total n.1.natAbs n.2.natAbs with h | h
  · rw [max_eq_right h]
    have : (n.2.natAbs : ℝ) = |(n.2 : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [this]
    nlinarith
  · rw [max_eq_left h]
    have : (n.1.natAbs : ℝ) = |(n.1 : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [this]
    nlinarith

theorem summable_Kinf_periodized :
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ < 1 →
      ∀ u : Z2 L, ∀ δ ∈ latticeFivePoint,
        Summable (fun n : ℤ × ℤ => Kinf ξ (torusLatticeLift u + δ + L • n)) := by
  intro L _ hL ξ hξ u δ _
  set w : ℤ × ℤ := torusLatticeLift u + δ with hw
  have hκ : 0 < kappa ξ := kappa_pos hξ
  set κ := kappa ξ with hκdef
  set A : ℝ := 180 * Real.log (2 + κ⁻¹) with hA
  have hA0 : 0 ≤ A := by
    have : 0 ≤ Real.log (2 + κ⁻¹) :=
      Real.log_nonneg (by have := inv_pos.mpr hκ; linarith)
    positivity
  set W : ℝ := |(w.1 : ℝ)| + |(w.2 : ℝ)| with hW
  set ρ : ℝ := Real.exp (-(κ * L) / 20000) with hρ
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hρ1 : ρ < 1 := by
    rw [hρ, Real.exp_lt_one_iff]
    have : 0 < κ * L := mul_pos hκ hLpos
    linarith
  refine summable_complex_lattice_of_geometric_bound _
    (A * Real.exp (κ * W / 20000)) ρ (by positivity) (Real.exp_nonneg _) hρ1 ?_
  intro n
  have hb := norm_Kinf_le ξ hξ (w + L • n)
  have hlow := PeriodizeKinfSummable_lower L w n
  have hexp : Real.exp (-(κ * (|((w + L • n).1 : ℝ)| + |((w + L • n).2 : ℝ)|)) / 20000) ≤
      Real.exp (κ * W / 20000) * ρ ^ latticeMaxRadius n := by
    rw [hρ, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hlow hκ.le
    nlinarith
  calc ‖Kinf ξ (w + L • n)‖
      ≤ A * Real.exp (-(κ * (|((w + L • n).1 : ℝ)| + |((w + L • n).2 : ℝ)|)) / 20000) := hb
    _ ≤ A * (Real.exp (κ * W / 20000) * ρ ^ latticeMaxRadius n) :=
        mul_le_mul_of_nonneg_left hexp hA0
    _ = A * Real.exp (κ * W / 20000) * ρ ^ latticeMaxRadius n := by ring

end RBM

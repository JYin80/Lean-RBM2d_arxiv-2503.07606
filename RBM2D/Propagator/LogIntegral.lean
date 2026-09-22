/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The two-dimensional logarithmic integral

On `[-π, π]²`, the periodic distance `|p|_*` in Section 8.2 of the paper is the
ordinary Euclidean norm. We prove the logarithmic bound for the corresponding
iterated Lebesgue integral, uniformly in positive `κ`.
-/

namespace RBM.LogIntegral

open Real MeasureTheory intervalIntegral

/-- The one-dimensional Gaussian resolvent integral is at most `π/A`. -/
theorem slice_le (A : ℝ) (hA : 0 < A) :
    (∫ s : ℝ in -π..π, (A ^ 2 + s ^ 2)⁻¹) ≤ π / A := by
  rw [integral_inv_sq_add_sq hA.ne']
  have h₁ := Real.arctan_lt_pi_div_two (π / A)
  have h₂ := Real.neg_pi_div_two_lt_arctan (-π / A)
  have hdiff : Real.arctan (π / A) - Real.arctan (-π / A) ≤ π := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hA.le)
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul

/-- The inner integral over the first momentum coordinate. -/
noncomputable def slice (κ t : ℝ) : ℝ :=
  ∫ s : ℝ in -π..π, (κ ^ 2 + t ^ 2 + s ^ 2)⁻¹

theorem slice_eq (κ t : ℝ) (hκ : 0 < κ) :
    slice κ t = (Real.sqrt (κ ^ 2 + t ^ 2))⁻¹ *
      (Real.arctan (π / Real.sqrt (κ ^ 2 + t ^ 2)) -
       Real.arctan (-π / Real.sqrt (κ ^ 2 + t ^ 2))) := by
  have hpos : 0 < κ ^ 2 + t ^ 2 := by positivity
  have hc : Real.sqrt (κ ^ 2 + t ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  have hsq : (Real.sqrt (κ ^ 2 + t ^ 2)) ^ 2 = κ ^ 2 + t ^ 2 :=
    Real.sq_sqrt hpos.le
  unfold slice
  rw [← integral_inv_sq_add_sq (a := -π) (b := π) hc]
  apply intervalIntegral.integral_congr
  intro s _
  rw [hsq]

/-- A uniform bound for the inner integral that exposes the logarithm in the second. -/
theorem slice_le_inv_add_abs (κ t : ℝ) (hκ : 0 < κ) :
    slice κ t ≤ 2 * π / (κ + |t|) := by
  have hsum : 0 < κ ^ 2 + t ^ 2 := by positivity
  let A := Real.sqrt (κ ^ 2 + t ^ 2)
  have hA : 0 < A := Real.sqrt_pos.2 hsum
  have hκA : κ ≤ A := by
    apply (Real.le_sqrt hκ.le hsum.le).2
    nlinarith [sq_nonneg t]
  have htA : |t| ≤ A := by
    apply (Real.le_sqrt (abs_nonneg t) hsum.le).2
    nlinarith [sq_nonneg κ, sq_abs t]
  have hbound : π / A ≤ 2 * π / (κ + |t|) := by
    apply (div_le_div_iff₀ hA (by positivity)).2
    nlinarith [Real.pi_pos]
  calc
    slice κ t = ∫ s : ℝ in -π..π, (A ^ 2 + s ^ 2)⁻¹ := by
      unfold slice
      apply intervalIntegral.integral_congr
      intro s _
      simp only [A, Real.sq_sqrt hsum.le]
    _ ≤ π / A := slice_le A hA
    _ ≤ _ := hbound

theorem slice_continuous (κ : ℝ) (hκ : 0 < κ) : Continuous (slice κ) := by
  have hsq : Continuous fun t : ℝ => κ ^ 2 + t ^ 2 := by fun_prop
  have hc : Continuous fun t : ℝ => Real.sqrt (κ ^ 2 + t ^ 2) :=
    Real.continuous_sqrt.comp hsq
  have hn : ∀ t : ℝ, Real.sqrt (κ ^ 2 + t ^ 2) ≠ 0 := by
    intro t
    exact (Real.sqrt_pos.2 (by positivity)).ne'
  have hci : Continuous fun t : ℝ => (Real.sqrt (κ ^ 2 + t ^ 2))⁻¹ :=
    hc.inv₀ hn
  have hquot : Continuous fun t : ℝ => π / Real.sqrt (κ ^ 2 + t ^ 2) := by
    fun_prop
  have hquotneg : Continuous fun t : ℝ => -π / Real.sqrt (κ ^ 2 + t ^ 2) := by
    fun_prop
  have hform : (slice κ) = fun t : ℝ =>
      (Real.sqrt (κ ^ 2 + t ^ 2))⁻¹ *
        (Real.arctan (π / Real.sqrt (κ ^ 2 + t ^ 2)) -
         Real.arctan (-π / Real.sqrt (κ ^ 2 + t ^ 2))) := by
    funext t
    exact slice_eq κ t hκ
  rw [hform]
  exact hci.mul ((Real.continuous_arctan.comp hquot).sub
    (Real.continuous_arctan.comp hquotneg))

theorem inv_add_abs_continuous (κ : ℝ) (hκ : 0 < κ) :
    Continuous fun t : ℝ => (κ + |t|)⁻¹ := by
  have hn : ∀ t : ℝ, κ + |t| ≠ 0 := fun t => ne_of_gt (by positivity)
  exact (continuous_const.add continuous_abs).inv₀ hn

theorem integral_inv_add_abs (κ : ℝ) (hκ : 0 < κ) :
    (∫ t : ℝ in -π..π, (κ + |t|)⁻¹) =
      2 * Real.log ((κ + π) / κ) := by
  have hpos : 0 < κ + π := by positivity
  have hhalf : (∫ t : ℝ in 0..π, (κ + |t|)⁻¹) =
      Real.log ((κ + π) / κ) := by
    calc
      (∫ t : ℝ in 0..π, (κ + |t|)⁻¹)
          = ∫ t : ℝ in 0..π, (t + κ)⁻¹ := by
              apply intervalIntegral.integral_congr
              intro t ht
              rw [Set.uIcc_of_le (le_of_lt Real.pi_pos)] at ht
              simp only [abs_of_nonneg ht.1, add_comm]
      _ = ∫ u : ℝ in κ..π + κ, u⁻¹ := by
            simpa only [zero_add] using
              (intervalIntegral.integral_comp_add_right (fun u : ℝ => u⁻¹) κ
              (a := 0) (b := π))
      _ = _ := by simpa only [add_comm π κ] using integral_inv_of_pos hκ hpos
  have hneg : (∫ t : ℝ in -π..0, (κ + |t|)⁻¹) =
      (∫ t : ℝ in 0..π, (κ + |t|)⁻¹) := by
    have h := intervalIntegral.integral_comp_neg
      (f := fun t : ℝ => (κ + |t|)⁻¹) (a := 0) (b := π)
    simpa only [abs_neg, neg_zero, neg_neg] using h.symm
  have hi : IntervalIntegrable (fun t : ℝ => (κ + |t|)⁻¹) volume (-π) 0 :=
    (inv_add_abs_continuous κ hκ).intervalIntegrable _ _
  have hj : IntervalIntegrable (fun t : ℝ => (κ + |t|)⁻¹) volume 0 π :=
    (inv_add_abs_continuous κ hκ).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hi hj, hneg, hhalf]
  ring

/-- The iterated integral over `[-π, π]²` grows only logarithmically as `κ ↓ 0`.
The fixed constant `32` is convenient for downstream bounds and is not optimized. -/
theorem log_integral_le (κ : ℝ) (hκ : 0 < κ) :
    (∫ t : ℝ in -π..π, ∫ s : ℝ in -π..π,
        (κ ^ 2 + t ^ 2 + s ^ 2)⁻¹) ≤
      32 * Real.log (2 + κ⁻¹) := by
  have hmaj : Continuous fun t : ℝ => 2 * π / (κ + |t|) := by
    have h := inv_add_abs_continuous κ hκ
    change Continuous fun t : ℝ => (2 * π) * (κ + |t|)⁻¹
    exact continuous_const.mul h
  have hπ : -π ≤ π := by linarith [Real.pi_pos]
  have hstep : (∫ t : ℝ in -π..π, slice κ t) ≤
      ∫ t : ℝ in -π..π, 2 * π / (κ + |t|) := by
    exact intervalIntegral.integral_mono_on hπ
      ((slice_continuous κ hκ).intervalIntegrable _ _)
      (hmaj.intervalIntegrable _ _)
      (fun t _ => slice_le_inv_add_abs κ t hκ)
  have hmajor : (∫ t : ℝ in -π..π, 2 * π / (κ + |t|)) =
      4 * π * Real.log ((κ + π) / κ) := by
    have heq : (fun t : ℝ => 2 * π / (κ + |t|)) =
        fun t : ℝ => (2 * π) * (κ + |t|)⁻¹ := by
      funext t
      ring
    rw [heq, intervalIntegral.integral_const_mul, integral_inv_add_abs κ hκ]
    ring
  have hx : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  have hrat : (κ + π) / κ = 1 + π * κ⁻¹ := by
    field_simp
  have hprod : π * κ⁻¹ ≤ 4 * κ⁻¹ :=
    mul_le_mul_of_nonneg_right Real.pi_le_four hx
  have hsq : 1 + π * κ⁻¹ ≤ (2 + κ⁻¹) ^ 2 := by
    nlinarith [sq_nonneg (κ⁻¹)]
  have harg : 0 < (κ + π) / κ := by positivity
  have hlog : Real.log ((κ + π) / κ) ≤ 2 * Real.log (2 + κ⁻¹) := by
    rw [hrat] at harg ⊢
    calc
      Real.log (1 + π * κ⁻¹) ≤ Real.log ((2 + κ⁻¹) ^ 2) :=
        Real.log_le_log harg hsq
      _ = _ := by rw [Real.log_pow]; ring
  have hlognonneg : 0 ≤ Real.log (2 + κ⁻¹) :=
    (Real.log_pos (by linarith)).le
  change (∫ t : ℝ in -π..π, slice κ t) ≤ _
  calc
    _ ≤ 4 * π * Real.log ((κ + π) / κ) := by rw [← hmajor]; exact hstep
    _ ≤ 8 * π * Real.log (2 + κ⁻¹) := by
      nlinarith [mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 4 * π)]
    _ ≤ 32 * Real.log (2 + κ⁻¹) := by
      nlinarith [Real.pi_le_four]

/-- The same bound for Lebesgue integration on the square, as written in `(eq_log_int)`.
The measure on `ℝ × ℝ` is the product of the one-dimensional Lebesgue measures. -/
theorem log_integral_square_le (κ : ℝ) (hκ : 0 < κ) :
    (∫ p : ℝ × ℝ in Set.Icc (-π) π ×ˢ Set.Icc (-π) π,
        (κ ^ 2 + p.1 ^ 2 + p.2 ^ 2)⁻¹ ∂(volume.prod volume)) ≤
      32 * Real.log (2 + κ⁻¹) := by
  let f : ℝ × ℝ → ℝ := fun p => (κ ^ 2 + p.1 ^ 2 + p.2 ^ 2)⁻¹
  have hf : Continuous f := by
    have hn : ∀ p : ℝ × ℝ, κ ^ 2 + p.1 ^ 2 + p.2 ^ 2 ≠ 0 := by
      intro p
      exact ne_of_gt (by positivity)
    exact (by fun_prop : Continuous f)
  have hint : IntegrableOn f (Set.Icc (-π) π ×ˢ Set.Icc (-π) π)
      (volume.prod volume) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hπ : -π ≤ π := by linarith [Real.pi_pos]
  have hFubini :
      (∫ p : ℝ × ℝ in Set.Icc (-π) π ×ˢ Set.Icc (-π) π, f p
          ∂(volume.prod volume)) =
        ∫ t : ℝ in -π..π, ∫ s : ℝ in -π..π, f (t, s) := by
    rw [setIntegral_prod f hint]
    simp_rw [integral_Icc_eq_integral_Ioc]
    simp_rw [← intervalIntegral.integral_of_le hπ]
  change (∫ p : ℝ × ℝ in Set.Icc (-π) π ×ˢ Set.Icc (-π) π, f p
    ∂(volume.prod volume)) ≤ _
  rw [hFubini]
  exact log_integral_le κ hκ

/-- A concrete positive-mass parameter in the paper's square integral. -/
example :
    (∫ p : ℝ × ℝ in Set.Icc (-π) π ×ˢ Set.Icc (-π) π,
        (1 + p.1 ^ 2 + p.2 ^ 2)⁻¹ ∂(volume.prod volume)) ≤
      32 * Real.log 3 := by
  have h := log_integral_square_le 1 (by norm_num)
  norm_num at h
  simpa using h

end RBM.LogIntegral

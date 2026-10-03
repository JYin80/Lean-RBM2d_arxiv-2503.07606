/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import RBM2D.Defs.Semicircle

/-!
# The semicircle Stieltjes transform as the paper's integral

`msc z` (the root of `m² + z m + 1 = 0` with `Im m > 0`, `RBM2D/Defs/Semicircle.lean`)
equals the paper's integral `∫_{-2}^{2} (2π)⁻¹ √(4 - x²) / (x - z) dx` (Section 2.1) for
`Im z > 0`.

Proof outline: the substitution `x = 2 cos θ` turns the integral into
`(2/π) ∫_0^π sin²θ / (2 cos θ - z) dθ`; polynomial division reduces it to
`J = ∫_0^π (2 cos θ - z)⁻¹ dθ`; folding gives `2 J = ∫_0^{2π} (2 cos θ - z)⁻¹ dθ`, which is
evaluated by the Cauchy integral formula on the unit circle, with the roots `-m` (inside)
and `-m⁻¹` (outside) of `w² - z w + 1`.
-/

namespace RBM

open Complex MeasureTheory intervalIntegral Metric

open scoped Real

private theorem semicircleIntegral_sub_ne {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    (t : ℂ) - z ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- The kernel `(2 cos θ - z)⁻¹`. -/
private noncomputable def semicircleIntegral_k (z : ℂ) (θ : ℝ) : ℂ :=
  (((2 * Real.cos θ : ℝ) : ℂ) - z)⁻¹

private theorem semicircleIntegral_k_continuous {z : ℂ} (hz : 0 < z.im) :
    Continuous (semicircleIntegral_k z) := by
  unfold semicircleIntegral_k
  exact Continuous.inv₀ (by fun_prop) (fun θ => semicircleIntegral_sub_ne hz _)

/-- Substitution `x = 2 cos θ` and polynomial division. -/
private theorem semicircleIntegral_subst {z : ℂ} (hz : 0 < z.im) :
    (∫ x in (-2 : ℝ)..2,
      ((Real.sqrt (4 - x ^ 2) / (2 * Real.pi) : ℝ) : ℂ) / ((x : ℂ) - z)) =
      (2 / (π : ℂ)) * (-(π : ℂ) * z / 4 +
        (1 - z ^ 2 / 4) * ∫ θ in (0 : ℝ)..π, semicircleIntegral_k z θ) := by
  set g : ℝ → ℂ := fun x => ((Real.sqrt (4 - x ^ 2) / (2 * Real.pi) : ℝ) : ℂ) / ((x : ℂ) - z)
    with hg_def
  have hg : Continuous g := by
    refine Continuous.div (by fun_prop) (by fun_prop) (fun x => semicircleIntegral_sub_ne hz x)
  have hsub := intervalIntegral.integral_deriv_smul_comp (a := 0) (b := π)
    (f := fun θ => 2 * Real.cos θ) (f' := fun θ => -(2 * Real.sin θ)) (g := g)
    (fun θ _ => by simpa using (Real.hasDerivAt_cos θ).const_mul 2)
    (show Continuous fun θ : ℝ => -(2 * Real.sin θ) by fun_prop).continuousOn hg
  simp only [Real.cos_zero, Real.cos_pi, Function.comp] at hsub
  norm_num at hsub
  rw [intervalIntegral.integral_symm, ← hsub, neg_neg]
  have hk := semicircleIntegral_k_continuous hz
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [intervalIntegral.integral_congr (g := fun θ => (2 / (π : ℂ)) *
      ((-(1 / 2 : ℂ)) * ((Real.cos θ : ℝ) : ℂ) + (-(z / 4)) + (1 - z ^ 2 / 4) *
        semicircleIntegral_k z θ))]
  · rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add
        ((show Continuous fun θ : ℝ => (-(1 / 2 : ℂ)) * ((Real.cos θ : ℝ) : ℂ) + (-(z / 4)) by
          fun_prop).intervalIntegrable _ _)
        ((show Continuous fun θ : ℝ => (1 - z ^ 2 / 4) * semicircleIntegral_k z θ from
          continuous_const.mul hk).intervalIntegrable _ _),
      intervalIntegral.integral_add
        ((show Continuous fun θ : ℝ => (-(1 / 2 : ℂ)) * ((Real.cos θ : ℝ) : ℂ) by
          fun_prop).intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, intervalIntegral.integral_ofReal, integral_cos]
    simp only [Real.sin_pi, Real.sin_zero, sub_zero, Complex.real_smul]
    push_cast
    ring
  · intro θ hθ
    rw [Set.uIcc_of_le Real.pi_pos.le] at hθ
    have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
    have hsq : Real.sqrt (4 - (2 * Real.cos θ) ^ 2) = 2 * Real.sin θ := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * Real.sin θ)]
      congr 1
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have hd := semicircleIntegral_sub_ne hz (2 * Real.cos θ)
    have hsc' := Complex.sin_sq_add_cos_sq (θ : ℂ)
    simp only [hg_def, semicircleIntegral_k, hsq, ← Complex.ofReal_sin]
    push_cast at hd ⊢
    field_simp
    linear_combination (8 : ℂ) * hsc'

/-- Folding `[0, 2π]` onto `[0, π]`. -/
private theorem semicircleIntegral_fold {z : ℂ} (hz : 0 < z.im) :
    (∫ θ in (0 : ℝ)..2 * π, semicircleIntegral_k z θ) =
      2 * ∫ θ in (0 : ℝ)..π, semicircleIntegral_k z θ := by
  have hk := semicircleIntegral_k_continuous hz
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π)
    (hk.intervalIntegrable _ _) (hk.intervalIntegrable _ _)]
  have hsym : (∫ θ in π..2 * π, semicircleIntegral_k z θ) =
      ∫ θ in (0 : ℝ)..π, semicircleIntegral_k z θ := by
    have h := intervalIntegral.integral_comp_sub_left (a := π) (b := 2 * π)
      (semicircleIntegral_k z) (2 * π)
    simp only [sub_self, show 2 * π - π = π by ring] at h
    rw [← h]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [semicircleIntegral_k, Real.cos_two_pi_sub]
  rw [hsym]
  ring

/-- The Cauchy integral formula on the unit circle. -/
private theorem semicircleIntegral_contour {z : ℂ} (hz : 0 < z.im) :
    (∫ θ in (0 : ℝ)..2 * π, semicircleIntegral_k z θ) =
      2 * (π : ℂ) * (-msc z + (msc z)⁻¹)⁻¹ := by
  have hm := msc_mul z
  have him := msc_im_pos hz
  have hnorm := norm_msc_lt_one hz
  set m := msc z with hm_def
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at him
    exact lt_irrefl _ him
  set r₁ : ℂ := -m with hr₁
  set r₂ : ℂ := -m⁻¹ with hr₂
  have hsum : r₁ + r₂ = z := by
    rw [hr₁, hr₂]
    field_simp
    linear_combination -hm
  have hprod : r₁ * r₂ = 1 := by
    rw [hr₁, hr₂]
    field_simp
  have hmpos : 0 < ‖m‖ := norm_pos_iff.mpr hm0
  have hr₁mem : r₁ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, hr₁, norm_neg]
    exact hnorm
  have hr₂norm : 1 < ‖r₂‖ := by
    rw [hr₂, norm_neg, norm_inv]
    exact one_lt_inv₀ hmpos |>.mpr hnorm
  have hdiff : DiffContOnCl ℂ (fun w : ℂ => (w - r₂)⁻¹) (ball (0 : ℂ) 1) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ one_ne_zero]
    intro w hw
    refine ((differentiableAt_id.sub_const r₂).inv ?_).differentiableWithinAt
    intro h
    rw [id, sub_eq_zero] at h
    rw [mem_closedBall_zero_iff, h] at hw
    linarith
  have hcauchy := hdiff.circleIntegral_sub_inv_smul hr₁mem
  unfold circleIntegral at hcauchy
  rw [intervalIntegral.integral_congr (g := fun θ => I * semicircleIntegral_k z θ)] at hcauchy
  · rw [intervalIntegral.integral_const_mul, smul_eq_mul] at hcauchy
    have hr : r₁ - r₂ = -m + m⁻¹ := by rw [hr₁, hr₂]; ring
    rw [← hr]
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    calc (∫ θ in (0 : ℝ)..2 * π, semicircleIntegral_k z θ)
        = I⁻¹ * (I * ∫ θ in (0 : ℝ)..2 * π, semicircleIntegral_k z θ) := by
          field_simp
      _ = 2 * (π : ℂ) * (r₁ - r₂)⁻¹ := by
          rw [hcauchy]
          field_simp
  · intro θ _
    simp only [deriv_circleMap, circleMap_zero, smul_eq_mul, Complex.ofReal_one, one_mul]
    set e := exp (θ * I) with he
    have he0 : e ≠ 0 := Complex.exp_ne_zero _
    have heinv : exp (-(θ : ℂ) * I) = e⁻¹ := by
      rw [neg_mul, Complex.exp_neg]
    have hcos : ((2 * Real.cos θ : ℝ) : ℂ) = e + e⁻¹ := by
      rw [← heinv, he]
      push_cast
      exact Complex.two_cos (θ : ℂ)
    have hd := semicircleIntegral_sub_ne hz (2 * Real.cos θ)
    have hP : (e - r₁) * (e - r₂) = e * (((2 * Real.cos θ : ℝ) : ℂ) - z) := by
      rw [hcos]
      field_simp
      linear_combination (-e) * hsum + hprod
    have hP0 : (e - r₁) * (e - r₂) ≠ 0 := by
      rw [hP]
      exact mul_ne_zero he0 hd
    rw [← mul_inv, hP, semicircleIntegral_k]
    field_simp

/-- The semicircle Stieltjes transform equals the paper's integral (Section 2.1):
`m_sc(z) = ∫_{-2}^{2} (2π)⁻¹ √(4 - x²) / (x - z) dx` for `Im z > 0`. -/
theorem msc_eq_integral {z : ℂ} (hz : 0 < z.im) :
    msc z = ∫ x in (-2 : ℝ)..2,
      ((Real.sqrt (4 - x ^ 2) / (2 * Real.pi) : ℝ) : ℂ) / ((x : ℂ) - z) := by
  have hm := msc_mul z
  have him := msc_im_pos hz
  have hJ : (∫ θ in (0 : ℝ)..π, semicircleIntegral_k z θ) =
      (π : ℂ) * (-msc z + (msc z)⁻¹)⁻¹ := by
    have h := (semicircleIntegral_fold hz).symm.trans (semicircleIntegral_contour hz)
    linear_combination h / 2
  rw [semicircleIntegral_subst hz, hJ]
  set m := msc z with hm_def
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at him
    exact lt_irrefl _ him
  have h1m : 1 - m ^ 2 ≠ 0 := by
    intro h
    have hsq : m ^ 2 = 1 := by linear_combination -h
    rcases sq_eq_one_iff.mp hsq with h1 | h1 <;>
      · rw [h1] at him
        simp at him
  have hr : -m + m⁻¹ = (1 - m ^ 2) / m := by field_simp; ring
  have hz' : z = -m - m⁻¹ := by
    field_simp
    linear_combination hm
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [hr, hz']
  field_simp
  ring

end RBM

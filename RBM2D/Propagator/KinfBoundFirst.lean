/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.Contour
import RBM2D.Propagator.LogIntegral

/-!
# First-coordinate contour-shift bound for `Kinf`

Section 8.2 of the paper shifts one momentum coordinate `p_j` by `i sgn(x_j) c₀ κ`, where
`κ = |1-ξ|^{1/2}`. Here we carry this out for the first coordinate `j = 1` with the explicit
constants `c₀ = 1/10000` (`contourWidth`) and `C = 180`, obtaining
`‖Kinf ξ x‖ ≤ 180 log(2 + κ⁻¹) exp(-κ |x₁| / 10000)` for every `x : ℤ × ℤ`.

The proof: swap the order of the two momentum integrals (Fubini) so that `p₁` is the inner
variable, shift the inner contour for each fixed outer `t = p₂`, bound the numerator by
`exp(-κ|x₁|/10000)` and the denominator by `(2/(45π²))(κ² + u² + t²)`, and finish with the
logarithmic integral bound `log_integral_le`.  The constant closes as
`(2π)⁻² · (45π²/2) · 32 = 180`.
-/

namespace RBM

open Real MeasureTheory intervalIntegral

/-- Fubini swap: the first momentum coordinate becomes the inner integration variable. -/
private theorem KinfBoundFirst_swap (ξ : ℂ) (hξ : ‖ξ‖ < 1) (x : ℤ × ℤ) :
    (∫ p₁ : ℝ in -Real.pi..Real.pi, ∫ p₂ : ℝ in -Real.pi..Real.pi,
        KinfIntegrand ξ x (p₁, p₂)) =
      ∫ t : ℝ in -Real.pi..Real.pi, ∫ u : ℝ in -Real.pi..Real.pi,
        KinfIntegrand ξ x (u, t) := by
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hint : Integrable (fun p : ℝ × ℝ => KinfIntegrand ξ x p)
      ((volume.restrict (Set.Ioc (-Real.pi) Real.pi)).prod
        (volume.restrict (Set.Ioc (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact (KinfIntegrand_integrableOn ξ hξ x).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  simp_rw [intervalIntegral.integral_of_le hπ]
  exact integral_integral_swap (f := fun p₁ p₂ => KinfIntegrand ξ x (p₁, p₂)) hint

/-- The signed shift `η = sgn(x₁) κ/10000` has modulus `contourWidth ξ` and satisfies
`η x₁ = κ |x₁| / 10000`. -/
private theorem KinfBoundFirst_shift_sign (ξ : ℂ) (x : ℤ × ℤ) :
    ∃ η : ℝ, |η| ≤ contourWidth ξ ∧
      η * (x.1 : ℝ) = kappa ξ * |(x.1 : ℝ)| / 10000 := by
  have hk : 0 ≤ kappa ξ := Real.sqrt_nonneg _
  by_cases h : 0 ≤ x.1
  · refine ⟨kappa ξ / 10000, ?_, ?_⟩
    · unfold contourWidth
      rw [abs_of_nonneg (by positivity)]
    · have hx : (0 : ℝ) ≤ (x.1 : ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg hx]
      ring
  · refine ⟨-(kappa ξ / 10000), ?_, ?_⟩
    · unfold contourWidth
      rw [abs_neg, abs_of_nonneg (by positivity)]
    · have hx : (x.1 : ℝ) < 0 := by exact_mod_cast not_le.1 h
      rw [abs_of_neg hx]
      ring

theorem norm_Kinf_le_first :
    ∀ ξ : ℂ, ‖ξ‖ < 1 → ∀ x : ℤ × ℤ,
      ‖Kinf ξ x‖ ≤ 180 * Real.log (2 + (kappa ξ)⁻¹) *
        Real.exp (-(kappa ξ * |(x.1 : ℝ)|) / 10000) := by
  intro ξ hξ x
  have hκ : 0 < kappa ξ := kappa_pos hξ
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hπpos : 0 < Real.pi := Real.pi_pos
  obtain ⟨η, hηw, hηx⟩ := KinfBoundFirst_shift_sign ξ x
  set E : ℝ := Real.exp (-(kappa ξ * |(x.1 : ℝ)|) / 10000) with hE
  have hE0 : 0 < E := Real.exp_pos _
  -- pointwise bound on the shifted integrand
  have hpt : ∀ u t : ℝ, |u| ≤ Real.pi → |t| ≤ Real.pi →
      ‖contourIntegrand ξ x t ((u : ℂ) + (η : ℂ) * Complex.I)‖ ≤
        E * (45 * Real.pi ^ 2 / 2) * ((kappa ξ) ^ 2 + t ^ 2 + u ^ 2)⁻¹ := by
    intro u t hu ht
    have hD := norm_Dfirst_shift_ge ξ hξ u t η hu ht hηw
    have hpos : 0 < (2 / (45 * Real.pi ^ 2)) * ((kappa ξ) ^ 2 + u ^ 2 + t ^ 2) := by
      positivity
    have hnum : ‖Complex.exp (Complex.I * (((u : ℂ) + (η : ℂ) * Complex.I) * (x.1 : ℂ) +
        (t : ℂ) * (x.2 : ℂ)))‖ = E := by
      rw [Complex.norm_exp]
      have hre : (Complex.I * (((u : ℂ) + (η : ℂ) * Complex.I) * (x.1 : ℂ) +
          (t : ℂ) * (x.2 : ℂ))).re = -(η * (x.1 : ℝ)) := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre, hE, hηx]
      congr 1
      ring
    unfold contourIntegrand
    rw [norm_div, hnum]
    calc E / ‖Dfirst ξ ((u : ℂ) + (η : ℂ) * Complex.I) t‖
        ≤ E / ((2 / (45 * Real.pi ^ 2)) * ((kappa ξ) ^ 2 + u ^ 2 + t ^ 2)) :=
          div_le_div_of_nonneg_left hE0.le hpos hD
      _ = E * (45 * Real.pi ^ 2 / 2) * ((kappa ξ) ^ 2 + t ^ 2 + u ^ 2)⁻¹ := by
          have h1 : (kappa ξ) ^ 2 + u ^ 2 + t ^ 2 ≠ 0 := by positivity
          have h2 : (kappa ξ) ^ 2 + t ^ 2 + u ^ 2 ≠ 0 := by positivity
          have h3 : Real.pi ≠ 0 := hπpos.ne'
          field_simp
          ring
  -- the inner integral, for fixed `t`
  have hinner : ∀ t : ℝ, |t| ≤ Real.pi →
      ‖∫ u : ℝ in -Real.pi..Real.pi,
          contourIntegrand ξ x t ((u : ℂ) + (η : ℂ) * Complex.I)‖ ≤
        E * (45 * Real.pi ^ 2 / 2) * LogIntegral.slice (kappa ξ) t := by
    intro t ht
    have hcont : Continuous fun u : ℝ =>
        E * (45 * Real.pi ^ 2 / 2) * ((kappa ξ) ^ 2 + t ^ 2 + u ^ 2)⁻¹ := by
      have hn : ∀ u : ℝ, (kappa ξ) ^ 2 + t ^ 2 + u ^ 2 ≠ 0 := by
        intro u
        exact ne_of_gt (by positivity)
      exact (by fun_prop : Continuous fun u : ℝ =>
        E * (45 * Real.pi ^ 2 / 2) * ((kappa ξ) ^ 2 + t ^ 2 + u ^ 2)⁻¹)
    have h := intervalIntegral.norm_integral_le_of_norm_le hπ
      (Filter.Eventually.of_forall fun u hu =>
        hpt u t (abs_le.mpr ⟨hu.1.le, hu.2⟩) ht) (hcont.intervalIntegrable (μ := volume) _ _)
    refine h.trans (le_of_eq ?_)
    unfold LogIntegral.slice
    rw [intervalIntegral.integral_const_mul]
  -- the outer integral
  have hcontS : Continuous fun t : ℝ =>
      E * (45 * Real.pi ^ 2 / 2) * LogIntegral.slice (kappa ξ) t :=
    continuous_const.mul (LogIntegral.slice_continuous (kappa ξ) hκ)
  have houter : ‖∫ t : ℝ in -Real.pi..Real.pi, ∫ u : ℝ in -Real.pi..Real.pi,
        contourIntegrand ξ x t ((u : ℂ) + (η : ℂ) * Complex.I)‖ ≤
      E * (45 * Real.pi ^ 2 / 2) * (32 * Real.log (2 + (kappa ξ)⁻¹)) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le hπ
      (Filter.Eventually.of_forall fun t ht =>
        hinner t (abs_le.mpr ⟨ht.1.le, ht.2⟩)) (hcontS.intervalIntegrable (μ := volume) _ _)
    refine h.trans ?_
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (LogIntegral.log_integral_le (kappa ξ) hκ)
      (by positivity)
  -- assemble
  have hshift : (∫ t : ℝ in -Real.pi..Real.pi, ∫ u : ℝ in -Real.pi..Real.pi,
        KinfIntegrand ξ x (u, t)) =
      ∫ t : ℝ in -Real.pi..Real.pi, ∫ u : ℝ in -Real.pi..Real.pi,
        contourIntegrand ξ x t ((u : ℂ) + (η : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hπ] at ht
    exact contour_integral_shift_first ξ hξ x t η
      (abs_le.mpr ⟨ht.1, ht.2⟩) hηw
  have hc : ‖((2 * (Real.pi : ℂ)) ^ 2)⁻¹‖ = ((2 * Real.pi) ^ 2)⁻¹ := by
    have h2 : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [h2, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  unfold Kinf
  rw [KinfBoundFirst_swap ξ hξ x, hshift, norm_mul, hc]
  refine le_trans (mul_le_mul_of_nonneg_left houter (by positivity)) (le_of_eq ?_)
  have h3 : Real.pi ≠ 0 := hπpos.ne'
  field_simp
  ring

end RBM

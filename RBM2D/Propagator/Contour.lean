/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.ContinuumSymbol
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Contour shift for the infinite-volume kernel

We move one complex momentum coordinate at a time. The key estimate controls
the perturbation of the continuous symbol on a strip of width proportional to
`κ = |1-ξ|^{1/2}`. The horizontal contour shift then yields exponential decay
in the chosen coordinate.
-/

namespace RBM

open Real MeasureTheory intervalIntegral Complex
open scoped Interval

/-- A quadratic bound for `cosh η - 1` when `|η| ≤ 1`. -/
theorem cosh_sub_one_le_sq {η : ℝ} (hη : |η| ≤ 1) :
    Real.cosh η - 1 ≤ η ^ 2 := by
  have hηsq : η ^ 2 ≤ 1 := by
    nlinarith [sq_abs η, abs_nonneg η]
  have hu : |η ^ 2 / 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have he := Real.abs_exp_sub_one_le hu
  have hnonneg : 0 ≤ Real.exp (η ^ 2 / 2) - 1 := by
    have hx : 0 ≤ η ^ 2 / 2 := by positivity
    linarith [Real.add_one_le_exp (η ^ 2 / 2)]
  rw [abs_of_nonneg hnonneg, abs_of_nonneg (by positivity : 0 ≤ η ^ 2 / 2)] at he
  have hc := Real.cosh_le_exp_half_sq η
  linarith

/-- A linear bound for `sinh η` on the unit interval. -/
theorem abs_sinh_le_two_mul_abs {η : ℝ} (hη : |η| ≤ 1) :
    |Real.sinh η| ≤ 2 * |η| := by
  have hc := cosh_sub_one_le_sq hη
  have hc0 := Real.one_le_cosh η
  have hηsq : η ^ 2 ≤ 1 := by
    nlinarith [sq_abs η, abs_nonneg η]
  have hcsq : (Real.cosh η) ^ 2 ≤ (1 + η ^ 2) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith : 0 ≤ 1 + η ^ 2 - Real.cosh η))
      (by linarith : 0 ≤ 1 + η ^ 2 + Real.cosh η)]
  have hsh := Real.cosh_sq η
  have hη4 : (η ^ 2) ^ 2 ≤ η ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg η) (sub_nonneg.mpr hηsq)]
  have hbound : (Real.sinh η) ^ 2 ≤ (2 * |η|) ^ 2 := by
    nlinarith [sq_abs η]
  exact abs_le_of_sq_le_sq hbound (by positivity)

/-- The cosine perturbation has one factor of momentum in its linear term. -/
theorem norm_cos_shift_sub_cos_le (u η : ℝ) (hη : |η| ≤ 1) :
    ‖Complex.cos ((u : ℂ) + (η : ℂ) * Complex.I) - (Real.cos u : ℂ)‖ ≤
      η ^ 2 + 2 * |u| * |η| := by
  have hid : Complex.cos ((u : ℂ) + (η : ℂ) * Complex.I) - (Real.cos u : ℂ) =
      ((Real.cos u * (Real.cosh η - 1) : ℝ) : ℂ) -
        ((Real.sin u * Real.sinh η : ℝ) : ℂ) * Complex.I := by
    rw [Complex.cos_add_mul_I]
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    push_cast
    ring
  have hc0 : 0 ≤ Real.cosh η - 1 := sub_nonneg.mpr (Real.one_le_cosh η)
  have hc := cosh_sub_one_le_sq hη
  have hs := abs_sinh_le_two_mul_abs hη
  have hsin : |Real.sin u| ≤ |u| := Real.abs_sin_le_abs
  have hcos := Real.abs_cos_le_one u
  calc
    ‖Complex.cos ((u : ℂ) + (η : ℂ) * Complex.I) - (Real.cos u : ℂ)‖
        = ‖((Real.cos u * (Real.cosh η - 1) : ℝ) : ℂ) -
            ((Real.sin u * Real.sinh η : ℝ) : ℂ) * Complex.I‖ := by rw [hid]
    _ ≤ ‖((Real.cos u * (Real.cosh η - 1) : ℝ) : ℂ)‖ +
          ‖((Real.sin u * Real.sinh η : ℝ) : ℂ) * Complex.I‖ := norm_sub_le _ _
    _ = |Real.cos u| * (Real.cosh η - 1) +
          |Real.sin u| * |Real.sinh η| := by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              Complex.norm_I, mul_one, abs_of_nonneg hc0]
    _ ≤ η ^ 2 + 2 * |u| * |η| := by
      have h₁ : |Real.cos u| * (Real.cosh η - 1) ≤ Real.cosh η - 1 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hcos) hc0]
      have h₂ : |Real.sin u| * |Real.sinh η| ≤ |u| * (2 * |η|) := by
        exact mul_le_mul hsin hs (abs_nonneg _) (abs_nonneg _)
      nlinarith

/-- The continuous denominator with only the first momentum complexified. -/
noncomputable def Dfirst (ξ z : ℂ) (t : ℝ) : ℂ :=
  1 - ξ * ((1 + 2 * Complex.cos z + 2 * Complex.cos (t : ℂ)) / 5)

theorem Dfirst_real_eq_Dcont (ξ : ℂ) (u t : ℝ) :
    Dfirst ξ (u : ℂ) t = Dcont ξ (u, t) := by
  unfold Dfirst Dcont Scont ScontReal
  simp only [← Complex.ofReal_cos]
  push_cast
  ring

/-- The perturbed denominator differs by a single cosine difference. -/
theorem Dfirst_shift_sub_Dcont (ξ : ℂ) (u t η : ℝ) :
    Dfirst ξ ((u : ℂ) + (η : ℂ) * Complex.I) t - Dcont ξ (u, t) =
      -(2 / 5 : ℂ) * ξ *
        (Complex.cos ((u : ℂ) + (η : ℂ) * Complex.I) - (Real.cos u : ℂ)) := by
  rw [← Dfirst_real_eq_Dcont]
  unfold Dfirst
  simp only [← Complex.ofReal_cos]
  ring

theorem norm_Dfirst_shift_sub_Dcont_le (ξ : ℂ) (hξ : ‖ξ‖ < 1)
    (u t η : ℝ) (hη : |η| ≤ 1) :
    ‖Dfirst ξ ((u : ℂ) + (η : ℂ) * Complex.I) t - Dcont ξ (u, t)‖ ≤
      η ^ 2 + 2 * |u| * |η| := by
  rw [Dfirst_shift_sub_Dcont]
  have hcos := norm_cos_shift_sub_cos_le u η hη
  have hcos0 : 0 ≤ ‖Complex.cos ((u : ℂ) + (η : ℂ) * Complex.I) -
      (Real.cos u : ℂ)‖ := norm_nonneg _
  have hfactor : ‖(-(2 / 5 : ℂ)) * ξ‖ ≤ 1 := by
    rw [norm_mul]
    have hnorm : ‖(-(2 / 5 : ℂ))‖ = (2 / 5 : ℝ) := by norm_num
    rw [hnorm]
    nlinarith [norm_nonneg ξ]
  calc
    ‖(-(2 / 5 : ℂ)) * ξ *
        (Complex.cos ((u : ℂ) + (η : ℂ) * Complex.I) - (Real.cos u : ℂ))‖
        = ‖(-(2 / 5 : ℂ)) * ξ‖ *
          ‖Complex.cos ((u : ℂ) + (η : ℂ) * Complex.I) - (Real.cos u : ℂ)‖ := by
            rw [norm_mul]
    _ ≤ 1 * ‖Complex.cos ((u : ℂ) + (η : ℂ) * Complex.I) -
          (Real.cos u : ℂ)‖ := mul_le_mul_of_nonneg_right hfactor hcos0
    _ ≤ η ^ 2 + 2 * |u| * |η| := by simpa using hcos

/-- A fixed, explicit fraction of `κ` stays in the zero-free strip. -/
noncomputable def contourWidth (ξ : ℂ) : ℝ := kappa ξ / 10000

theorem contourWidth_pos (ξ : ℂ) (hξ : ‖ξ‖ < 1) :
    0 < contourWidth ξ := by
  unfold contourWidth
  exact div_pos (kappa_pos hξ) (by norm_num)

/-- `(eq_shifted_lower)` for a shift of the first momentum coordinate.
The small numerical width leaves generous room for the perturbation estimate. -/
theorem norm_Dfirst_shift_ge (ξ : ℂ) (hξ : ‖ξ‖ < 1)
    (u t η : ℝ) (hu : |u| ≤ Real.pi) (ht : |t| ≤ Real.pi)
    (hη : |η| ≤ contourWidth ξ) :
    (2 / (45 * Real.pi ^ 2)) * ((kappa ξ) ^ 2 + u ^ 2 + t ^ 2) ≤
      ‖Dfirst ξ ((u : ℂ) + (η : ℂ) * Complex.I) t‖ := by
  have hk : 0 < kappa ξ := kappa_pos hξ
  have hk2 : (kappa ξ) ^ 2 < 2 := by
    rw [kappa_sq]
    exact norm_one_sub_lt_two hξ
  have hk_lt : kappa ξ < 2 := by nlinarith [sq_nonneg (kappa ξ - 2)]
  have hη1 : |η| ≤ 1 := by
    unfold contourWidth at hη
    linarith
  have hηsq : η ^ 2 ≤ (kappa ξ / 10000) ^ 2 := by
    rw [← sq_abs η]
    exact (sq_le_sq₀ (abs_nonneg η) (by positivity)).2 hη
  have hcross : 2 * |u| * |η| ≤ 2 * |u| * (kappa ξ / 10000) := by
    exact mul_le_mul_of_nonneg_left hη (by positivity)
  have hamgm : 2 * |u| * kappa ξ ≤ u ^ 2 + (kappa ξ) ^ 2 := by
    nlinarith [sq_nonneg (|u| - kappa ξ), sq_abs u]
  have hpert : η ^ 2 + 2 * |u| * |η| ≤
      ((kappa ξ) ^ 2 + u ^ 2 + t ^ 2) / 5000 := by
    nlinarith [sq_nonneg t]
  have hπsq : Real.pi ^ 2 ≤ 16 := by
    nlinarith [Real.pi_le_four, Real.pi_pos]
  have hc : (1 / 1000 : ℝ) ≤ 4 / (45 * Real.pi ^ 2) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 45 * Real.pi ^ 2)).2
    nlinarith
  have hsum : 0 ≤ (kappa ξ) ^ 2 + u ^ 2 + t ^ 2 := by positivity
  have hpert' : η ^ 2 + 2 * |u| * |η| ≤
      (2 / (45 * Real.pi ^ 2)) * ((kappa ξ) ^ 2 + u ^ 2 + t ^ 2) := by
    have hc' : (1 / 5000 : ℝ) ≤ 2 / (45 * Real.pi ^ 2) := by
      have hh := mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have hh' : (1 / 2000 : ℝ) ≤ 2 / (45 * Real.pi ^ 2) := by
        convert hh using 1 <;> ring
      linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hc') hsum]
  have hreal := norm_Dcont_ge_pnorm2 ξ hξ (u, t) hu ht
  have hdiff := norm_Dfirst_shift_sub_Dcont_le ξ hξ u t η hη1
  have htri : ‖Dcont ξ (u, t)‖ ≤
      ‖Dfirst ξ ((u : ℂ) + (η : ℂ) * Complex.I) t‖ +
      ‖Dfirst ξ ((u : ℂ) + (η : ℂ) * Complex.I) t - Dcont ξ (u, t)‖ := by
    calc
      ‖Dcont ξ (u, t)‖ =
          ‖Dfirst ξ ((u : ℂ) + (η : ℂ) * Complex.I) t -
            (Dfirst ξ ((u : ℂ) + (η : ℂ) * Complex.I) t - Dcont ξ (u, t))‖ := by
              congr 1
              ring
      _ ≤ _ := norm_sub_le _ _
  dsimp [pnorm2] at hreal
  have halg : (2 / (45 * Real.pi ^ 2)) *
        ((kappa ξ) ^ 2 + u ^ 2 + t ^ 2) +
      (2 / (45 * Real.pi ^ 2)) * ((kappa ξ) ^ 2 + u ^ 2 + t ^ 2) =
      (4 / (45 * Real.pi ^ 2)) * ((kappa ξ) ^ 2 + (u ^ 2 + t ^ 2)) := by ring
  linarith

theorem Dfirst_shift_ne_zero (ξ : ℂ) (hξ : ‖ξ‖ < 1)
    (u t η : ℝ) (hu : |u| ≤ Real.pi) (ht : |t| ≤ Real.pi)
    (hη : |η| ≤ contourWidth ξ) :
    Dfirst ξ ((u : ℂ) + (η : ℂ) * Complex.I) t ≠ 0 := by
  have h := norm_Dfirst_shift_ge ξ hξ u t η hu ht hη
  have hk := kappa_pos hξ
  intro hz
  rw [hz, norm_zero] at h
  have hp : (0 : ℝ) < (2 / (45 * Real.pi ^ 2)) *
      ((kappa ξ) ^ 2 + u ^ 2 + t ^ 2) := by positivity
  linarith

theorem Dfirst_ne_zero_of_re_im (ξ : ℂ) (hξ : ‖ξ‖ < 1)
    (t : ℝ) (z : ℂ) (hzre : |z.re| ≤ Real.pi) (ht : |t| ≤ Real.pi)
    (hzim : |z.im| ≤ contourWidth ξ) : Dfirst ξ z t ≠ 0 := by
  rw [← Complex.re_add_im z]
  exact Dfirst_shift_ne_zero ξ hξ z.re t z.im hzre ht hzim

theorem abs_le_of_mem_uIcc_zero {η y : ℝ} (hy : y ∈ Set.uIcc 0 η) :
    |y| ≤ |η| := by
  rcases le_total 0 η with hη | hη
  · rw [Set.uIcc_of_le hη] at hy
    rw [abs_of_nonneg hy.1, abs_of_nonneg hη]
    exact hy.2
  · rw [Set.uIcc_of_ge hη] at hy
    rw [abs_of_nonpos hy.2, abs_of_nonpos hη]
    linarith [hy.1]

/-- The rectangle used to move the first Fourier momentum. -/
def contourRect (η : ℝ) : Set ℂ :=
  Set.uIcc (-Real.pi) Real.pi ×ℂ Set.uIcc 0 η

/-- A one-variable contour shift when the two vertical boundary values coincide. -/
theorem integral_shift_of_vertical_periodic (f : ℂ → ℂ) (η : ℝ)
    (hdiff : DifferentiableOn ℂ f (contourRect η))
    (hperiod : ∀ y ∈ Set.uIcc 0 η,
      f ((Real.pi : ℂ) + (y : ℂ) * Complex.I) =
        f ((-Real.pi : ℂ) + (y : ℂ) * Complex.I)) :
    (∫ u : ℝ in -Real.pi..Real.pi, f (u : ℂ)) =
      ∫ u : ℝ in -Real.pi..Real.pi,
        f ((u : ℂ) + (η : ℂ) * Complex.I) := by
  have hrect : DifferentiableOn ℂ f
      ([[((-Real.pi : ℝ) : ℂ).re, ((Real.pi : ℝ) : ℂ).re +
          ((η : ℂ) * Complex.I).re]] ×ℂ
        [[((-Real.pi : ℝ) : ℂ).im, ((Real.pi : ℝ) : ℂ).im +
          ((η : ℂ) * Complex.I).im]]) := by
    simpa [contourRect] using hdiff
  have hC := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((-Real.pi : ℝ) : ℂ) (((Real.pi : ℝ) : ℂ) + (η : ℂ) * Complex.I) hrect
  have hv :
      (∫ y : ℝ in 0..η, f ((Real.pi : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ y : ℝ in 0..η, f ((-Real.pi : ℂ) + (y : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact hperiod y hy
  simp only [ofReal_re, ofReal_im, add_re, add_im, mul_I_re, mul_I_im,
    zero_add, neg_zero, add_zero] at hC
  rw [hv] at hC
  apply sub_eq_zero.mp
  simpa only [ofReal_zero, zero_mul, add_zero, ← ofReal_neg,
    add_sub_cancel_right] using hC

/-- The one-complex-variable Fourier integrand, with the second momentum fixed real. -/
noncomputable def contourIntegrand (ξ : ℂ) (x : ℤ × ℤ) (t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (z * (x.1 : ℂ) + (t : ℂ) * (x.2 : ℂ))) /
    Dfirst ξ z t

theorem contourIntegrand_real (ξ : ℂ) (x : ℤ × ℤ) (t u : ℝ) :
    contourIntegrand ξ x t (u : ℂ) = KinfIntegrand ξ x (u, t) := by
  rw [contourIntegrand, KinfIntegrand, Dfirst_real_eq_Dcont]
  congr 1
  unfold continuumNumerator continuumPhase
  congr 1
  push_cast
  ring

theorem contourIntegrand_periodic (ξ : ℂ) (x : ℤ × ℤ) (t : ℝ) (z : ℂ) :
    contourIntegrand ξ x t (z + 2 * (Real.pi : ℂ)) =
      contourIntegrand ξ x t z := by
  have hden : Dfirst ξ (z + 2 * (Real.pi : ℂ)) t = Dfirst ξ z t := by
    unfold Dfirst
    rw [Complex.cos_add_two_pi]
  have hnum :
      Complex.exp (Complex.I *
          ((z + 2 * (Real.pi : ℂ)) * (x.1 : ℂ) + (t : ℂ) * (x.2 : ℂ))) =
        Complex.exp (Complex.I *
          (z * (x.1 : ℂ) + (t : ℂ) * (x.2 : ℂ))) := by
    calc
      Complex.exp (Complex.I *
          ((z + 2 * (Real.pi : ℂ)) * (x.1 : ℂ) + (t : ℂ) * (x.2 : ℂ))) =
        Complex.exp (Complex.I *
            (z * (x.1 : ℂ) + (t : ℂ) * (x.2 : ℂ)) +
          (x.1 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
            congr 1
            ring
      _ = Complex.exp (Complex.I *
          (z * (x.1 : ℂ) + (t : ℂ) * (x.2 : ℂ))) *
          Complex.exp ((x.1 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :=
            Complex.exp_add _ _
      _ = _ := by rw [Complex.exp_int_mul_two_pi_mul_I]; ring
  unfold contourIntegrand
  rw [hnum, hden]

theorem contourIntegrand_vertical_periodic (ξ : ℂ) (x : ℤ × ℤ)
    (t y : ℝ) :
    contourIntegrand ξ x t ((Real.pi : ℂ) + (y : ℂ) * Complex.I) =
      contourIntegrand ξ x t ((-Real.pi : ℂ) + (y : ℂ) * Complex.I) := by
  have hz : (Real.pi : ℂ) + (y : ℂ) * Complex.I =
      ((-Real.pi : ℂ) + (y : ℂ) * Complex.I) + 2 * (Real.pi : ℂ) := by ring
  rw [hz, contourIntegrand_periodic]

theorem contourIntegrand_differentiableOn (ξ : ℂ) (hξ : ‖ξ‖ < 1)
    (x : ℤ × ℤ) (t η : ℝ) (ht : |t| ≤ Real.pi)
    (hη : |η| ≤ contourWidth ξ) :
    DifferentiableOn ℂ (contourIntegrand ξ x t) (contourRect η) := by
  have hnum : Differentiable ℂ
      (fun z : ℂ => Complex.exp (Complex.I *
        (z * (x.1 : ℂ) + (t : ℂ) * (x.2 : ℂ)))) := by
    fun_prop
  have hden : Differentiable ℂ (fun z : ℂ => Dfirst ξ z t) := by
    unfold Dfirst
    fun_prop
  have hnonzero : ∀ z ∈ contourRect η, Dfirst ξ z t ≠ 0 := by
    intro z hz
    have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
    have hz' : z.re ∈ Set.uIcc (-Real.pi) Real.pi ∧
        z.im ∈ Set.uIcc 0 η := by
      change z ∈ Set.uIcc (-Real.pi) Real.pi ×ℂ Set.uIcc 0 η at hz
      exact Complex.mem_reProdIm.mp hz
    have hre : |z.re| ≤ Real.pi := by
      have hr : z.re ∈ Set.Icc (-Real.pi) Real.pi := by
        simpa only [Set.uIcc_of_le hπ] using hz'.1
      exact abs_le.mpr ⟨by linarith [hr.1], hr.2⟩
    have him : |z.im| ≤ contourWidth ξ :=
      (abs_le_of_mem_uIcc_zero hz'.2).trans hη
    exact Dfirst_ne_zero_of_re_im ξ hξ t z hre ht him
  unfold contourIntegrand
  exact hnum.differentiableOn.div hden.differentiableOn hnonzero

/-- The first-coordinate contour shift, including the cancellation of vertical sides. -/
theorem contour_integral_shift_first (ξ : ℂ) (hξ : ‖ξ‖ < 1)
    (x : ℤ × ℤ) (t η : ℝ) (ht : |t| ≤ Real.pi)
    (hη : |η| ≤ contourWidth ξ) :
    (∫ u : ℝ in -Real.pi..Real.pi, KinfIntegrand ξ x (u, t)) =
      ∫ u : ℝ in -Real.pi..Real.pi,
        contourIntegrand ξ x t ((u : ℂ) + (η : ℂ) * Complex.I) := by
  have h := integral_shift_of_vertical_periodic (contourIntegrand ξ x t) η
    (contourIntegrand_differentiableOn ξ hξ x t η ht hη)
    (fun y _ => contourIntegrand_vertical_periodic ξ x t y)
  simpa only [contourIntegrand_real] using h

end RBM

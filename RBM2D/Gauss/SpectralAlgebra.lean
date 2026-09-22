/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.SpectralWindow

/-!
# Algebra of the explicit bulk spectral value

These identities concern the explicit `spectralM E`. They do not assert its
identification with a boundary limit of the semicircle Stieltjes transform.
-/

namespace RBM.Gauss

open Complex

/-- The real square root in the explicit bulk value has the expected square. -/
theorem spectralM_sqrt_sq {E : ℝ} (hE : |E| ≤ 2) :
    Real.sqrt (4 - E ^ 2) ^ 2 = 4 - E ^ 2 := by
  refine Real.sq_sqrt ?_
  have habs := abs_le.mp hE
  nlinarith

/-- The explicit bulk value solves the semicircle quadratic equation. -/
theorem spectralM_mul {E : ℝ} (hE : |E| ≤ 2) :
    spectralM E * (spectralM E + E) = -1 := by
  have hs : ((Real.sqrt (4 - E ^ 2) : ℝ) : ℂ) ^ 2 = 4 - (E : ℂ) ^ 2 := by
    exact_mod_cast spectralM_sqrt_sq hE
  have hI : I ^ 2 = -1 := I_sq
  simp only [spectralM]
  linear_combination ((Real.sqrt (4 - E ^ 2) : ℂ) ^ 2 / 4) * hI -
    (1 / 4 : ℂ) * hs

/-- Equivalent monic quadratic equation `m² + E m + 1 = 0`. -/
theorem spectralM_quadratic {E : ℝ} (hE : |E| ≤ 2) :
    spectralM E ^ 2 + E * spectralM E + 1 = 0 := by
  have h := spectralM_mul hE
  linear_combination h

/-- The explicit bulk value lies on the unit circle. -/
theorem norm_spectralM {E : ℝ} (hE : |E| ≤ 2) : ‖spectralM E‖ = 1 := by
  have h2 : ‖spectralM E‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hre : (spectralM E).re = -E / 2 := by simp [spectralM]
    rw [hre, spectralM_im]
    have hs := spectralM_sqrt_sq hE
    nlinarith
  have hnonneg := norm_nonneg (spectralM E)
  nlinarith

/-- A non-real, unit-modulus instance at the band center. -/
example : spectralM 0 = Complex.I ∧ ‖spectralM 0‖ = 1 := by
  constructor
  · have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    simp [spectralM, hsqrt]
  · exact norm_spectralM (by norm_num : |(0 : ℝ)| ≤ 2)

end RBM.Gauss

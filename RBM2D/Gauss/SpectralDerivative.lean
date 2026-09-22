/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.SpectralAlgebra

/-!
# Derivatives of the spectral path

These are the deterministic derivatives of the paper's affine spectral path.
They do not assert a Green flow or generator identity.
-/

namespace RBM.Gauss

/-- The spectral path has constant complex derivative `-m^(E)`. -/
theorem hasDerivAt_spectralZ (E u : ℝ) :
    HasDerivAt (spectralZ E) (-(spectralM E)) u := by
  have h : HasDerivAt (fun v : ℝ => v • (-(spectralM E) : ℂ))
      (-(spectralM E)) u := by
    simpa using (hasDerivAt_id u).smul_const (-(spectralM E) : ℂ)
  have hsum := h.const_add ((E : ℂ) + spectralM E)
  have hfun : spectralZ E =
      fun v : ℝ => ((E : ℂ) + spectralM E) + v • (-(spectralM E) : ℂ) := by
    funext v
    simp only [spectralZ, Complex.real_smul]
    ring
  rw [hfun]
  exact hsum

/-- The imaginary gap has derivative `-Im m^(E)`. -/
theorem hasDerivAt_spectralZ_im (E u : ℝ) :
    HasDerivAt (fun v : ℝ => (spectralZ E v).im) (-(spectralM E).im) u := by
  simpa only [spectralZ_im, id_eq, neg_one_mul] using
    (((hasDerivAt_id u).const_sub 1).mul_const (spectralM E).im)

/-- At the band center, the imaginary gap falls at unit speed. -/
example (u : ℝ) :
    HasDerivAt (fun v : ℝ => (spectralZ 0 v).im) (-1) u := by
  have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  have hm : (spectralM 0).im = 1 := by
    rw [spectralM_im]
    norm_num [hsqrt]
  simpa [hm] using hasDerivAt_spectralZ_im 0 u

end RBM.Gauss

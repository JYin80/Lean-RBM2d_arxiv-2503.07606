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

end RBM.Gauss

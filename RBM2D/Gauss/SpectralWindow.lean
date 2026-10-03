/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopEnvelope

/-!
# The spectral path on a compact time window

The paper defines `z_u^(E) = E + (1-u)m^(E)`, where the upper-half-plane boundary
value of the semicircle transform is `m^(E) = (-E + i√(4-E²))/2` in the bulk.
The gap below is uniform for `u ∈ [s,t]` whenever `t < 1`.
-/

namespace RBM.Gauss

open Complex

/-- The bulk boundary value `m^(E)` of the semicircle Stieltjes transform. -/
noncomputable def spectralM (E : ℝ) : ℂ :=
  (-E + Real.sqrt (4 - E ^ 2) * I) / 2

theorem spectralM_im (E : ℝ) : (spectralM E).im = Real.sqrt (4 - E ^ 2) / 2 := by
  simp [spectralM]

theorem spectralM_im_pos {E : ℝ} (hE : |E| < 2) : 0 < (spectralM E).im := by
  rw [spectralM_im]
  have habs := abs_lt.mp hE
  have hsq : 0 < 4 - E ^ 2 := by nlinarith
  positivity

/-- The paper's time-dependent spectral parameter `z_u^(E)`. -/
noncomputable def spectralZ (E u : ℝ) : ℂ := E + (1 - u) * spectralM E

theorem spectralZ_im (E u : ℝ) : (spectralZ E u).im = (1 - u) * (spectralM E).im := by
  simp [spectralZ]

theorem continuous_spectralZ (E : ℝ) : Continuous (spectralZ E) := by
  unfold spectralZ
  fun_prop

/-- A uniform non-real gap on `[s,t]`, with the minimum attained at `t`. -/
theorem spectralZ_im_gap {E s t : ℝ} (hE : |E| < 2) (ht : t < 1)
    {u : ℝ} (hu : u ∈ Set.Icc s t) :
    (1 - t) * (spectralM E).im ≤ |(spectralZ E u).im| := by
  rw [spectralZ_im, abs_of_pos (mul_pos (by linarith [hu.2]) (spectralM_im_pos hE))]
  exact mul_le_mul_of_nonneg_right (by linarith [hu.2]) (spectralM_im_pos hE).le

end RBM.Gauss

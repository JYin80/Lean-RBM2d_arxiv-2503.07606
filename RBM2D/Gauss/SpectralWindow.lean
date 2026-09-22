/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopMomentCont

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

/-- The gap remains valid under the paper's bulk condition `|E| ≤ 2-κ`. -/
theorem spectralZ_window_gap_of_bulk {E κ s t : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (ht : t < 1) :
    0 < (1 - t) * (spectralM E).im ∧
      ∀ u ∈ Set.Icc s t,
        (1 - t) * (spectralM E).im ≤ |(spectralZ E u).im| := by
  have hE' : |E| < 2 := by linarith
  constructor
  · exact mul_pos (by linarith) (spectralM_im_pos hE')
  · intro u hu
    exact spectralZ_im_gap hE' ht hu

/-- The actual finite Gaussian loop moment has a continuous time dependence along
the paper's bulk spectral path, on every window ending before `u=1`. -/
theorem continuousOn_integral_norm_gloop_pow_spectralZ
    (L W : ℕ) [NeZero L] [NeZero W]
    {E κ s t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hst : s ≤ t) (ht : t < 1)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) (q : ℕ) :
    ContinuousOn
      (fun u : ℝ => ∫ ω : Ω L W,
        ‖gloop L W (HflowBlock L W u ω) (spectralZ E u) I‖ ^ q ∂(P L W))
      (Set.Icc s t) := by
  obtain ⟨hη, hgap⟩ := spectralZ_window_gap_of_bulk hκ hE ht
  exact continuousOn_integral_norm_gloop_pow L W hst hη
    (continuous_spectralZ E) hgap I hwf q

/-- The spectral path is genuinely time-dependent, even at the center of the bulk. -/
example : spectralZ 0 0 ≠ spectralZ 0 (1 / 2) := by
  simp [spectralZ, spectralM]

end RBM.Gauss

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopSampleCont
import RBM2D.Gauss.LoopEnvelope
import RBM2D.Gauss.MomentTimeCont

/-!
# Time continuity of a finite Gaussian loop moment

On a compact time window, a uniform spectral gap gives a deterministic bound for every
sample. Samplewise loop continuity and fixed-time measurability then allow dominated
convergence. The spectral parameter only needs to stay non-real on the stated window.
-/

namespace RBM.Gauss

open MeasureTheory

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Samplewise loop continuity on a window whose spectral path stays off the real axis.
Clamping the spectral path to the window lets us reuse the global path theorem. -/
theorem continuousOn_gloop_HflowBlock_window {s t : ℝ} (hst : s ≤ t)
    (ω : Ω L W) {z : ℝ → ℂ} (hzcont : Continuous z)
    (hzim : ∀ u ∈ Set.Icc s t, (z u).im ≠ 0)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    ContinuousOn (fun u : ℝ => gloop L W (HflowBlock L W u ω) (z u) I)
      (Set.Icc s t) := by
  let clamp : ℝ → ℝ := fun u => max s (min t u)
  have hclamp_cont : Continuous clamp :=
    continuous_const.max (continuous_const.min continuous_id)
  have hclamp_mem : ∀ u, clamp u ∈ Set.Icc s t := by
    intro u
    exact ⟨le_max_left _ _, max_le hst (min_le_left _ _)⟩
  have hclamp_eq : ∀ u ∈ Set.Icc s t, clamp u = u := by
    intro u hu
    simp [clamp, min_eq_right hu.2, max_eq_right hu.1]
  have hglobal := continuous_gloop_Hflow_time L W ω
    (z := fun u => z (clamp u)) (hzcont.comp hclamp_cont)
    (fun u => hzim (clamp u) (hclamp_mem u)) I hwf
  exact hglobal.continuousOn.congr (fun u hu => by
    change gloop L W (HflowBlock L W u ω) (z u) I =
      gloop L W (HflowBlock L W u ω) (z (clamp u)) I
    rw [hclamp_eq u hu])

/-- The `q`-th absolute moment of a finite resolvent loop is continuous in time. The
uniform whole-space envelope is explicit and applies to all Gaussian samples. -/
theorem continuousOn_integral_norm_gloop_pow {s t η : ℝ} (hst : s ≤ t)
    (hη : 0 < η) {z : ℝ → ℂ} (hzcont : Continuous z)
    (hzlow : ∀ u ∈ Set.Icc s t, η ≤ |(z u).im|)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) (q : ℕ) :
    ContinuousOn
      (fun u : ℝ => ∫ ω : Ω L W,
        ‖gloop L W (HflowBlock L W u ω) (z u) I‖ ^ q ∂(P L W))
      (Set.Icc s t) := by
  let C : ℝ := (((L * W) ^ 2 : ℕ) : ℝ) *
    (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ I.a.length
  have hzim : ∀ u ∈ Set.Icc s t, (z u).im ≠ 0 := by
    intro u hu
    exact abs_pos.mp (hη.trans_le (hzlow u hu))
  have hmeas : ∀ u ∈ Set.Icc s t,
      AEStronglyMeasurable
        (fun ω : Ω L W => ‖gloop L W (HflowBlock L W u ω) (z u) I‖) (P L W) := by
    intro u hu
    exact ((measurable_gloop_HflowBlock_sample L W u (hzim u hu) I hwf).norm).aestronglyMeasurable
  have hbd : ∀ u ∈ Set.Icc s t, ∀ ω : Ω L W,
      |‖gloop L W (HflowBlock L W u ω) (z u) I‖| ≤ C := by
    intro u hu ω
    rw [abs_of_nonneg (norm_nonneg _)]
    exact norm_gloop_HflowBlock_le_crude_on_Icc L W hη hzlow I hwf u hu ω
  have hcont : ∀ ω : Ω L W,
      ContinuousOn (fun u : ℝ => ‖gloop L W (HflowBlock L W u ω) (z u) I‖)
        (Set.Icc s t) := by
    intro ω
    exact (continuousOn_gloop_HflowBlock_window L W hst ω hzcont hzim I hwf).norm
  have h := continuousOn_integral_abs_pow_of_envelope (P := P L W)
    (S := Set.Icc s t)
    (f := fun u ω => ‖gloop L W (HflowBlock L W u ω) (z u) I‖)
    (C := C) q hmeas hbd hcont
  simpa only [abs_of_nonneg (norm_nonneg _)] using h

end RBM.Gauss

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.LoopHierarchyLengthEnvelopeSmall

/-!
# Monotonicity of the explicit length-only hierarchy envelope

For positive spectral gaps, every resolvent power and hence the crude finite
hierarchy envelope decreases as the gap grows. This elementary order fact
justifies using the smallest spectral gap on a time window.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The explicit `n`-edge resolvent envelope is nonnegative. -/
theorem cutResolventEnvelope_nonneg {η : ℝ} (hη : 0 < η) (n : ℕ) :
    0 ≤ cutResolventEnvelope L W η n := by
  unfold cutResolventEnvelope
  positivity

/-- Increasing a positive spectral gap decreases each resolvent power. -/
theorem cutResolventEnvelope_antitone_gap
    {η₁ η₂ : ℝ} (hη₁ : 0 < η₁) (hgap : η₁ ≤ η₂) (n : ℕ) :
    cutResolventEnvelope L W η₂ n ≤
      cutResolventEnvelope L W η₁ n := by
  have hinv : η₂⁻¹ ≤ η₁⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hη₁ hgap
  unfold cutResolventEnvelope
  gcongr
  exact mul_nonneg (inv_nonneg.mpr (le_trans hη₁.le hgap)) (sq_nonneg _)

/-- The complete length-only envelope is nonnegative for every edge count. -/
theorem loopHierarchyLengthEnvelope_nonneg {η : ℝ} (hη : 0 < η) (E : ℝ) (n : ℕ) :
    0 ≤ loopHierarchyLengthEnvelope L W η E n := by
  unfold loopHierarchyLengthEnvelope cutResolventEnvelope
  positivity

/-- The complete length-only envelope is antitone in a positive spectral
gap. The pair-cut `n+2` power is included exactly. -/
theorem loopHierarchyLengthEnvelope_antitone_gap
    {η₁ η₂ : ℝ} (hη₁ : 0 < η₁) (hgap : η₁ ≤ η₂)
    (E : ℝ) (n : ℕ) :
    loopHierarchyLengthEnvelope L W η₂ E n ≤
      loopHierarchyLengthEnvelope L W η₁ E n := by
  unfold loopHierarchyLengthEnvelope
  gcongr
  all_goals first
    | exact cutResolventEnvelope_nonneg L W (lt_of_lt_of_le hη₁ hgap) _
    | exact cutResolventEnvelope_nonneg L W hη₁ _
    | exact cutResolventEnvelope_antitone_gap L W hη₁ hgap _

/-- On a compact spectral-path window, the right endpoint has the smallest
positive gap and therefore gives the largest length-only envelope. -/
theorem loopHierarchyLengthEnvelope_on_window_le_minGap
    {E a b v : ℝ} (hE : |E| < 2) (hb : b < 1)
    (hv : v ∈ Set.Icc a b) (n : ℕ) :
    loopHierarchyLengthEnvelope L W
        ((1 - v) * (spectralM E).im) E n ≤
      loopHierarchyLengthEnvelope L W
        ((1 - b) * (spectralM E).im) E n := by
  have hm : 0 < (spectralM E).im := spectralM_im_pos hE
  have hmin : 0 < (1 - b) * (spectralM E).im :=
    mul_pos (by linarith) hm
  have hgap : (1 - b) * (spectralM E).im ≤
      (1 - v) * (spectralM E).im :=
    mul_le_mul_of_nonneg_right (by linarith [hv.2]) hm.le
  exact loopHierarchyLengthEnvelope_antitone_gap L W hmin hgap E n

/-- The finite-time increment estimate stated with the explicit loop-length
envelope at the minimum gap of the spectral path. -/
theorem norm_expected_gloop_increment_le_length_minGap
    (hL : 3 ≤ L) (I : LoopIdx (Z2 L)) (hwf : I.WF)
    {E a b : ℝ} (hE : |E| < 2) (ha : 0 ≤ a) (hab : a < b)
    (hb : b < 1) :
    ‖(∫ ω : Ω L W,
        gloop L W (HflowBlock L W b ω) (spectralZ E b) I ∂(P L W)) -
      (∫ ω : Ω L W,
        gloop L W (HflowBlock L W a ω) (spectralZ E a) I ∂(P L W))‖ ≤
      loopHierarchyLengthEnvelope L W
        ((1 - b) * (spectralM E).im) E I.length * (b - a) := by
  simpa only [loopHierarchyUniformEnvelope_eq_lengthEnvelope L W I hwf] using
    norm_expected_gloop_increment_le_pathGap L W hL I hwf hE ha hab hb

end RBM.Gauss

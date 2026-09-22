/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.LoopHierarchyRHSBound

/-!
# A finite derivative envelope for the expected loop

The exact hierarchy ODE turns the cut right-hand-side bound into a bound on
the actual time derivative of the finite Gaussian loop expectation. The
ordered-pair sum keeps each pair's genuine left/right loop lengths.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The actual expected-loop time derivative obeys the complete finite cut
envelope at any positive spectral gap. -/
theorem norm_deriv_expected_gloop_le
    (hL : 3 ≤ L) (I : LoopIdx (Z2 L)) (hwf : I.WF)
    {E u η : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (hη : 0 < η) (hz : η ≤ |(spectralZ E u).im|) :
    ‖deriv (fun v : ℝ => ∫ ω : Ω L W,
      gloop L W (HflowBlock L W v ω) (spectralZ E v) I ∂(P L W)) u‖ ≤
      (W : ℝ) ^ 2 *
        ((I.length : ℝ) *
          ((Fintype.card (Z2 L) : ℝ) *
            (cutResolventEnvelope L W η (I.length + 1) *
              cutResolventEnvelope L W η 1))) +
      (W : ℝ) ^ 2 *
        (((pairSplits (I.σ.zip I.a)).map fun p =>
          (Fintype.card (Z2 L) : ℝ) *
            (cutResolventEnvelope L W η
              (p.before.length + p.after.length + 2) *
              cutResolventEnvelope L W η (p.middle.length + 2))).sum) +
      (I.length : ℝ) *
        (‖spectralM E‖ * (W : ℝ) ^ 2 *
          ((Fintype.card (Z2 L) : ℝ) *
            cutResolventEnvelope L W η (I.length + 1))) := by
  rw [deriv_expected_gloop_eq_hierarchyCuts L W hE hu hu1 I hwf]
  exact norm_expectedLoopCutRHS_le L W hL I hwf E u hη hz

/-- The spectral path has the exact positive pointwise gap
`(1-u) Im m(E)` throughout `u<1` in the bulk. -/
theorem spectralZ_positive_point_gap
    {E u : ℝ} (hE : |E| < 2) (hu1 : u < 1) :
    0 < (1 - u) * (spectralM E).im ∧
      (1 - u) * (spectralM E).im = |(spectralZ E u).im| := by
  have hη : 0 < (1 - u) * (spectralM E).im :=
    mul_pos (by linarith) (spectralM_im_pos hE)
  constructor
  · exact hη
  · rw [spectralZ_im, abs_of_pos hη]

/-- The derivative envelope with the actual, automatically positive gap of
the paper's spectral path. -/
theorem norm_deriv_expected_gloop_le_pathGap
    (hL : 3 ≤ L) (I : LoopIdx (Z2 L)) (hwf : I.WF)
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1) :
    let η : ℝ := (1 - u) * (spectralM E).im
    ‖deriv (fun v : ℝ => ∫ ω : Ω L W,
      gloop L W (HflowBlock L W v ω) (spectralZ E v) I ∂(P L W)) u‖ ≤
      (W : ℝ) ^ 2 *
        ((I.length : ℝ) *
          ((Fintype.card (Z2 L) : ℝ) *
            (cutResolventEnvelope L W η (I.length + 1) *
              cutResolventEnvelope L W η 1))) +
      (W : ℝ) ^ 2 *
        (((pairSplits (I.σ.zip I.a)).map fun p =>
          (Fintype.card (Z2 L) : ℝ) *
            (cutResolventEnvelope L W η
              (p.before.length + p.after.length + 2) *
              cutResolventEnvelope L W η (p.middle.length + 2))).sum) +
      (I.length : ℝ) *
        (‖spectralM E‖ * (W : ℝ) ^ 2 *
          ((Fintype.card (Z2 L) : ℝ) *
            cutResolventEnvelope L W η (I.length + 1))) := by
  have hgap := spectralZ_positive_point_gap hE hu1
  exact norm_deriv_expected_gloop_le L W hL I hwf hE hu hu1
    hgap.1 hgap.2.le

end RBM.Gauss

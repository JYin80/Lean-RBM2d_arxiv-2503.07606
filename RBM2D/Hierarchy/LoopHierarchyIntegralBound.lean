/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.LoopHierarchyDerivativeBound
import RBM2D.Hierarchy.LoopHierarchyIntegralZero

/-!
# Finite-time increment bound for the expected loop

The endpoint Duhamel identity and a uniform spectral gap on `[a,b]` give
an explicit finite-time bound. The pair-cut term retains its finite sum of
position-dependent resolvent powers. This is not a closed moment estimate.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The explicit time-independent envelope for the finite expected hierarchy
on a window with spectral gap at least `η`. Pair-cut powers remain attached to
their actual split positions. -/
noncomputable def loopHierarchyUniformEnvelope (η : ℝ) (E : ℝ)
    (I : LoopIdx (Z2 L)) : ℝ :=
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
        cutResolventEnvelope L W η (I.length + 1)))

/-- On a compact time interval inside `[0,1)`, the expected loop increment
is at most elapsed time times the explicit uniform hierarchy envelope. -/
theorem norm_expected_gloop_increment_le
    (hL : 3 ≤ L) (I : LoopIdx (Z2 L)) (hwf : I.WF)
    {E a b η : ℝ} (hE : |E| < 2) (ha : 0 ≤ a) (hab : a < b)
    (hb : b < 1) (hη : 0 < η)
    (hz : ∀ u ∈ Set.Icc a b, η ≤ |(spectralZ E u).im|) :
    ‖(∫ ω : Ω L W,
        gloop L W (HflowBlock L W b ω) (spectralZ E b) I ∂(P L W)) -
      (∫ ω : Ω L W,
        gloop L W (HflowBlock L W a ω) (spectralZ E a) I ∂(P L W))‖ ≤
      loopHierarchyUniformEnvelope L W η E I * (b - a) := by
  rw [expected_gloop_hierarchy_integral_of_nonneg L W hE ha hab hb I hwf]
  change ‖∫ u in a..b, expectedLoopCutRHS L W E u I‖ ≤ _
  have hbound : ∀ u ∈ Set.uIoc a b,
      ‖expectedLoopCutRHS L W E u I‖ ≤
        loopHierarchyUniformEnvelope L W η E I := by
    intro u hu
    have hu : u ∈ Set.Icc a b := by
      rw [Set.uIoc_of_le hab.le] at hu
      exact ⟨hu.1.le, hu.2⟩
    exact norm_expectedLoopCutRHS_le L W hL I hwf E u hη (hz u hu)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa [abs_of_pos (sub_pos.mpr hab)] using h

/-- The paper's spectral path supplies a uniform gap on `[a,b]`, namely
`(1-b) Im m(E)`. -/
theorem norm_expected_gloop_increment_le_pathGap
    (hL : 3 ≤ L) (I : LoopIdx (Z2 L)) (hwf : I.WF)
    {E a b : ℝ} (hE : |E| < 2) (ha : 0 ≤ a) (hab : a < b)
    (hb : b < 1) :
    ‖(∫ ω : Ω L W,
        gloop L W (HflowBlock L W b ω) (spectralZ E b) I ∂(P L W)) -
      (∫ ω : Ω L W,
        gloop L W (HflowBlock L W a ω) (spectralZ E a) I ∂(P L W))‖ ≤
      loopHierarchyUniformEnvelope L W
        ((1 - b) * (spectralM E).im) E I * (b - a) := by
  have hη : 0 < (1 - b) * (spectralM E).im :=
    mul_pos (by linarith) (spectralM_im_pos hE)
  exact norm_expected_gloop_increment_le L W hL I hwf hE ha hab hb hη
    (fun u hu => spectralZ_im_gap hE hb hu)

end RBM.Gauss

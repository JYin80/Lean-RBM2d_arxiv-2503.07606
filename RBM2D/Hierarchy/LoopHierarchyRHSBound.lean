/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.LoopHierarchySpectralCutBounds

/-!
# A finite envelope for the expected loop hierarchy right-hand side

This is a direct triangle-inequality bound for the exact finite generator.
The pair-cut contribution remains a sum indexed by the actual pair splits,
with their individual resolvent powers. It is not a closed moment estimate.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

private theorem norm_list_double_sum_le
    {α β γ : Type*} [Fintype β] [Fintype γ]
    (l : List α) (f : α → β → γ → ℂ) :
    ‖(l.map fun x => ∑ y : β, ∑ z : γ, f x y z).sum‖ ≤
      (l.map fun x => ∑ y : β, ∑ z : γ, ‖f x y z‖).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      have hterm : ‖∑ y : β, ∑ z : γ, f x y z‖ ≤
          ∑ y : β, ∑ z : γ, ‖f x y z‖ := by
        calc
          _ ≤ ∑ y : β, ‖∑ z : γ, f x y z‖ := norm_sum_le _ _
          _ ≤ ∑ y : β, ∑ z : γ, ‖f x y z‖ := by
            apply Finset.sum_le_sum
            intro y hy
            exact norm_sum_le _ _
      exact (norm_add_le _ _).trans (add_le_add hterm ih)

/-- The complete same-edge expected cut family is bounded by the explicit
`n`-position, one-free-block envelope. -/
theorem norm_expectedSameEdgeCuts_le
    (hL : 3 ≤ L) (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (E u : ℝ) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |(spectralZ E u).im|) :
    ‖expectedSameEdgeCuts L W E u I‖ ≤
      (I.length : ℝ) *
        ((Fintype.card (Z2 L) : ℝ) *
          (cutResolventEnvelope L W η (I.length + 1) *
            cutResolventEnvelope L W η 1)) := by
  unfold expectedSameEdgeCuts
  exact (norm_list_double_sum_le _ _).trans
    (sum_all_sameEdgeCutIntegrand_norm_le L W hL I hwf u hη hz)

/-- The complete distinct-edge expected cut family is bounded by a finite
sum retaining each pair's actual left and right loop lengths. -/
theorem norm_expectedPairCuts_le
    (hL : 3 ≤ L) (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (E u : ℝ) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |(spectralZ E u).im|) :
    ‖expectedPairCuts L W E u I‖ ≤
      ((pairSplits (I.σ.zip I.a)).map fun p =>
        (Fintype.card (Z2 L) : ℝ) *
          (cutResolventEnvelope L W η
            (p.before.length + p.after.length + 2) *
            cutResolventEnvelope L W η (p.middle.length + 2))).sum := by
  unfold expectedPairCuts
  exact (norm_list_double_sum_le _ _).trans
    (sum_all_pairCutIntegrand_norm_le L W hL I hwf u hη hz)

/-- One explicit bound for the full expected finite-loop hierarchy right-hand
side. No comparison of the different pair-cut powers is made. -/
theorem norm_expectedLoopCutRHS_le
    (hL : 3 ≤ L) (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (E u : ℝ) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |(spectralZ E u).im|) :
    ‖expectedLoopCutRHS L W E u I‖ ≤
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
  have hsame := norm_expectedSameEdgeCuts_le L W hL I hwf E u hη hz
  have hpair := norm_expectedPairCuts_le L W hL I hwf E u hη hz
  have hspec := norm_expectedSpectralCuts_le L W I hwf E u hη hz
  unfold expectedLoopCutRHS
  calc
    ‖(W : ℂ) ^ 2 * expectedSameEdgeCuts L W E u I +
        (W : ℂ) ^ 2 * expectedPairCuts L W E u I +
        expectedSpectralCuts L W E u I‖ ≤
      ‖(W : ℂ) ^ 2 * expectedSameEdgeCuts L W E u I‖ +
      ‖(W : ℂ) ^ 2 * expectedPairCuts L W E u I‖ +
      ‖expectedSpectralCuts L W E u I‖ := by
        exact (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
    _ = (W : ℝ) ^ 2 * ‖expectedSameEdgeCuts L W E u I‖ +
        (W : ℝ) ^ 2 * ‖expectedPairCuts L W E u I‖ +
        ‖expectedSpectralCuts L W E u I‖ := by
          simp [norm_pow]
    _ ≤ _ := by gcongr

end RBM.Gauss

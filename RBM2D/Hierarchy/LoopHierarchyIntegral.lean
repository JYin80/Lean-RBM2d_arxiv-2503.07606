/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.LoopHierarchyGenerator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Finite-time form of the expected loop hierarchy

The fundamental theorem of calculus applies to the finite expected hierarchy
on any compact interval strictly inside `(0,1)`, provided its explicit cut
right-hand side is interval integrable. Continuity of that right-hand side is
a sufficient hypothesis.
-/

namespace RBM.Gauss

open MeasureTheory

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The explicit right-hand side of the finite expected loop hierarchy. -/
noncomputable def expectedLoopCutRHS (E u : ℝ) (I : LoopIdx (Z2 L)) : ℂ :=
  (W : ℂ) ^ 2 * expectedSameEdgeCuts L W E u I +
  (W : ℂ) ^ 2 * expectedPairCuts L W E u I +
  expectedSpectralCuts L W E u I

/-- The integrated finite expected loop hierarchy, under the exact interval
integrability condition needed by the fundamental theorem of calculus. -/
theorem expected_gloop_hierarchy_integral
    {E a b : ℝ} (hE : |E| < 2) (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (hint : IntervalIntegrable (fun u : ℝ => expectedLoopCutRHS L W E u I)
      volume a b) :
    (∫ ω : Ω L W,
      gloop L W (HflowBlock L W b ω) (spectralZ E b) I ∂(P L W)) -
    (∫ ω : Ω L W,
      gloop L W (HflowBlock L W a ω) (spectralZ E a) I ∂(P L W)) =
    ∫ u in a..b,
      (W : ℂ) ^ 2 * expectedSameEdgeCuts L W E u I +
      (W : ℂ) ^ 2 * expectedPairCuts L W E u I +
      expectedSpectralCuts L W E u I := by
  let F : ℝ → ℂ := fun v => ∫ ω : Ω L W,
    gloop L W (HflowBlock L W v ω) (spectralZ E v) I ∂(P L W)
  let G : ℝ → ℂ := fun v => expectedLoopCutRHS L W E v I
  have hderiv : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ F x := by
    intro x hx
    rw [Set.uIcc_of_le hab.le] at hx
    exact (hasDerivAt_integral_gloop_HflowBlock_spectralZ L W hE
      (lt_of_lt_of_le ha hx.1) (lt_of_le_of_lt hx.2 hb) I hwf).differentiableAt
  have heq : Set.EqOn (deriv F) G (Set.uIcc a b) := by
    intro x hx
    rw [Set.uIcc_of_le hab.le] at hx
    simpa [F, G, expectedLoopCutRHS] using
      deriv_expected_gloop_eq_hierarchyCuts L W hE
        (lt_of_lt_of_le ha hx.1) (lt_of_le_of_lt hx.2 hb) I hwf
  have hsubset : Set.uIoo a b ⊆ Set.uIcc a b := by
    rw [Set.uIoo_of_le hab.le, Set.uIcc_of_le hab.le]
    exact Set.Ioo_subset_Icc_self
  have hderivInt : IntervalIntegrable (deriv F) volume a b :=
    (intervalIntegrable_congr_uIoo (heq.mono hsubset)).mpr hint
  have hFTC := intervalIntegral.integral_deriv_eq_sub hderiv hderivInt
  rw [intervalIntegral.integral_congr heq] at hFTC
  simpa [F, G, expectedLoopCutRHS] using hFTC.symm

/-- Continuity of the explicit cut right-hand side suffices for the integrated
finite expected hierarchy on a compact interior time interval. -/
theorem expected_gloop_hierarchy_integral_of_continuousOn
    {E a b : ℝ} (hE : |E| < 2) (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (hcont : ContinuousOn (fun u : ℝ => expectedLoopCutRHS L W E u I)
      (Set.Icc a b)) :
    (∫ ω : Ω L W,
      gloop L W (HflowBlock L W b ω) (spectralZ E b) I ∂(P L W)) -
    (∫ ω : Ω L W,
      gloop L W (HflowBlock L W a ω) (spectralZ E a) I ∂(P L W)) =
    ∫ u in a..b,
      (W : ℂ) ^ 2 * expectedSameEdgeCuts L W E u I +
      (W : ℂ) ^ 2 * expectedPairCuts L W E u I +
      expectedSpectralCuts L W E u I := by
  exact expected_gloop_hierarchy_integral L W hE ha hab hb I hwf
    ((by simpa only [Set.uIcc_of_le hab.le] using hcont :
      ContinuousOn (fun u : ℝ => expectedLoopCutRHS L W E u I)
        (Set.uIcc a b)).intervalIntegrable)

end RBM.Gauss

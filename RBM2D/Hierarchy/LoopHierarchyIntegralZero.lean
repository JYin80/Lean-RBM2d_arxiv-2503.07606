/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.LoopHierarchyCutContinuity

/-!
# Finite-time loop hierarchy from the zero endpoint

The expected loop and the three explicit cut families are continuous on a
closed window `[a,b] ⊆ [0,1)`. The generator equation is needed only on its
interior. The endpoint form of the fundamental theorem of calculus therefore
allows `a = 0`, where the original interior derivative theorem does not apply.
-/

namespace RBM.Gauss

open MeasureTheory

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The finite expected loop is continuous even at time zero, as long as the
entire window stays below the singular time `u = 1`. -/
theorem continuousOn_expected_gloop_spectralZ
    {E a b : ℝ} (hE : |E| < 2) (hab : a ≤ b) (hb : b < 1)
    (I : LoopIdx (Z2 L)) :
    ContinuousOn (fun u : ℝ => ∫ ω : Ω L W,
      gloop L W (HflowBlock L W u ω) (spectralZ E u) I ∂(P L W))
      (Set.Icc a b) :=
  continuousOn_integral_gloop_spectralZ L W hE hab hb I

/-- Endpoint form of the integrated expected finite-loop hierarchy. In
particular, `a = 0` is allowed and the initial expectation is exact. -/
theorem expected_gloop_hierarchy_integral_of_nonneg
    {E a b : ℝ} (hE : |E| < 2) (ha : 0 ≤ a) (hab : a < b) (hb : b < 1)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    (∫ ω : Ω L W,
      gloop L W (HflowBlock L W b ω) (spectralZ E b) I ∂(P L W)) -
    (∫ ω : Ω L W,
      gloop L W (HflowBlock L W a ω) (spectralZ E a) I ∂(P L W)) =
    ∫ u in a..b,
      (W : ℂ) ^ 2 * expectedSameEdgeCuts L W E u I +
      (W : ℂ) ^ 2 * expectedPairCuts L W E u I +
      expectedSpectralCuts L W E u I := by
  let F : ℝ → ℂ := fun u => ∫ ω : Ω L W,
    gloop L W (HflowBlock L W u ω) (spectralZ E u) I ∂(P L W)
  let G : ℝ → ℂ := fun u => expectedLoopCutRHS L W E u I
  have hFcont : ContinuousOn F (Set.uIcc a b) := by
    simpa only [F, Set.uIcc_of_le hab.le] using
      continuousOn_expected_gloop_spectralZ L W hE hab.le hb I
  have hGcont : ContinuousOn G (Set.uIcc a b) := by
    simpa only [G, Set.uIcc_of_le hab.le] using
      continuousOn_expectedLoopCutRHS L W hE hab.le hb I
  have hderiv : ∀ x ∈ Set.uIoo a b, DifferentiableAt ℝ F x := by
    intro x hx
    rw [Set.uIoo_of_le hab.le] at hx
    exact (hasDerivAt_integral_gloop_HflowBlock_spectralZ L W hE
      (lt_of_le_of_lt ha hx.1) (hx.2.trans hb) I hwf).differentiableAt
  have heq : Set.EqOn (deriv F) G (Set.uIoo a b) := by
    intro x hx
    rw [Set.uIoo_of_le hab.le] at hx
    simpa [F, G, expectedLoopCutRHS] using
      deriv_expected_gloop_eq_hierarchyCuts L W hE
        (lt_of_le_of_lt ha hx.1) (hx.2.trans hb) I hwf
  have hGint : IntervalIntegrable G volume a b := hGcont.intervalIntegrable
  have hderivInt : IntervalIntegrable (deriv F) volume a b :=
    (intervalIntegrable_congr_uIoo heq).mpr hGint
  have hFTC := intervalIntegral.integral_deriv_eq_sub_uIoo hFcont hderiv hderivInt
  rw [intervalIntegral.integral_congr_uIoo heq] at hFTC
  simpa [F, G, expectedLoopCutRHS] using hFTC.symm

/-- The Duhamel identity with its exact time-zero expected loop. -/
theorem expected_gloop_hierarchy_integral_zero
    {E b : ℝ} (hE : |E| < 2) (hb0 : 0 < b) (hb1 : b < 1)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    (∫ ω : Ω L W,
      gloop L W (HflowBlock L W b ω) (spectralZ E b) I ∂(P L W)) -
    (∫ ω : Ω L W,
      gloop L W (HflowBlock L W 0 ω) (spectralZ E 0) I ∂(P L W)) =
    ∫ u in (0 : ℝ)..b,
      (W : ℂ) ^ 2 * expectedSameEdgeCuts L W E u I +
      (W : ℂ) ^ 2 * expectedPairCuts L W E u I +
      expectedSpectralCuts L W E u I := by
  exact expected_gloop_hierarchy_integral_of_nonneg L W hE le_rfl hb0 hb1 I hwf

end RBM.Gauss

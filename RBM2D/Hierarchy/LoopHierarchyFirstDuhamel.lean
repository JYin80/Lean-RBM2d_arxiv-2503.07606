/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.LoopHierarchyIntegralZero
import RBM2D.Gauss.LoopInitialValueEmpty

/-!
# First Picard step of the finite expected loop hierarchy

The exact scalar initial condition and the finite-time hierarchy combine into
one Duhamel identity. This step makes no claim about a convergent tree
expansion or later estimates.
-/

namespace RBM.Gauss

open MeasureTheory

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The first exact Duhamel step: the expected loop at time `b` equals its
explicit deterministic scalar initial value plus the integral of the three
actual cut families. -/
theorem expected_gloop_eq_firstDuhamel
    {E b : ℝ} (hE : |E| < 2) (hb0 : 0 < b) (hb1 : b < 1)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    (∫ ω : Ω L W,
      gloop L W (HflowBlock L W b ω) (spectralZ E b) I ∂(P L W)) =
    totalInitialLoopScalar L W E I +
      ∫ u in (0 : ℝ)..b,
        (W : ℂ) ^ 2 * expectedSameEdgeCuts L W E u I +
        (W : ℂ) ^ 2 * expectedPairCuts L W E u I +
        expectedSpectralCuts L W E u I := by
  have h := expected_gloop_hierarchy_integral_zero L W hE hb0 hb1 I hwf
  rw [integral_gloop_HflowBlock_zero L W E I,
    initialLoopValue_eq_total L W hE I hwf] at h
  calc
    _ = totalInitialLoopScalar L W E I +
          ((∫ ω : Ω L W,
            gloop L W (HflowBlock L W b ω) (spectralZ E b) I ∂(P L W)) -
            totalInitialLoopScalar L W E I) := by ring
    _ = _ := by rw [h]

/-- In the empty-word case all three cut families vanish, so the expected
loop remains the full matrix dimension. -/
theorem expected_gloop_empty_eq_dimension
    {E b : ℝ} (hE : |E| < 2) (hb0 : 0 < b) (hb1 : b < 1) :
    (∫ ω : Ω L W,
      gloop L W (HflowBlock L W b ω) (spectralZ E b)
        (⟨[], []⟩ : LoopIdx (Z2 L)) ∂(P L W)) =
      (((L * W) ^ 2 : ℕ) : ℂ) := by
  have h := expected_gloop_eq_firstDuhamel L W hE hb0 hb1
    (⟨[], []⟩ : LoopIdx (Z2 L)) (by simp [LoopIdx.WF])
  simpa [totalInitialLoopScalar, expectedSameEdgeCuts, expectedPairCuts,
    expectedSpectralCuts, edgeSplits, pairSplits, spectralEdgeSplits] using h

end RBM.Gauss

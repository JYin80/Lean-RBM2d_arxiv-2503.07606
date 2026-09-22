/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.LoopHierarchyFirstDuhamel

/-!
# The one-edge finite expected loop hierarchy

A one-edge loop has one same-edge cut and one spectral-drift cut, but no
distinct-edge contraction. This gives a small exact base case for later
Picard iteration.
-/

namespace RBM.Gauss

open MeasureTheory

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- A one-edge loop has no ordered pair of distinct edges. -/
@[simp] theorem expectedPairCuts_one_edge (E u : ℝ) (σ : Bool) (a : Z2 L) :
    expectedPairCuts L W E u ⟨[σ], [a]⟩ = 0 := by
  simp [expectedPairCuts, pairSplits, edgeSplits]

/-- The same-edge cut family of a one-edge loop has exactly one edge split. -/
theorem expectedSameEdgeCuts_one_edge (E u : ℝ) (σ : Bool) (a : Z2 L) :
    expectedSameEdgeCuts L W E u ⟨[σ], [a]⟩ =
      ∑ p : Z2 L, ∑ q : Z2 L,
        ∫ ω : Ω L W,
          sameEdgeCutIntegrand L W u ω (spectralZ E u)
            ⟨[], (σ, a), []⟩ p q ∂(P L W) := by
  simp [expectedSameEdgeCuts, edgeSplits]

/-- The spectral-drift family of a one-edge loop has exactly one edge split. -/
theorem expectedSpectralCuts_one_edge (E u : ℝ) (σ : Bool) (a : Z2 L) :
    expectedSpectralCuts L W E u ⟨[σ], [a]⟩ =
      -(spectralMSign E σ * (W : ℂ) ^ 2) *
        ∑ q : Z2 L, ∫ ω : Ω L W,
          gloop L W (HflowBlock L W u ω) (spectralZ E u)
            ((⟨[σ], [a]⟩ : LoopIdx (Z2 L)).cutGlue 1 q) ∂(P L W) := by
  simp [expectedSpectralCuts, spectralEdgeSplits]

/-- Reduced one-edge expected hierarchy ODE; the distinct-edge pair family
vanishes identically. -/
theorem deriv_expected_gloop_one_edge
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (σ : Bool) (a : Z2 L) :
    deriv (fun v : ℝ => ∫ ω : Ω L W,
      gloop L W (HflowBlock L W v ω) (spectralZ E v)
        ⟨[σ], [a]⟩ ∂(P L W)) u =
      (W : ℂ) ^ 2 * expectedSameEdgeCuts L W E u ⟨[σ], [a]⟩ +
        expectedSpectralCuts L W E u ⟨[σ], [a]⟩ := by
  simpa [expectedPairCuts_one_edge] using
    deriv_expected_gloop_eq_hierarchyCuts L W hE hu hu1
      ⟨[σ], [a]⟩ (by simp [LoopIdx.WF])

/-- Fully enumerated one-edge generator, showing both surviving block sums. -/
theorem deriv_expected_gloop_one_edge_explicit
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (σ : Bool) (a : Z2 L) :
    deriv (fun v : ℝ => ∫ ω : Ω L W,
      gloop L W (HflowBlock L W v ω) (spectralZ E v)
        ⟨[σ], [a]⟩ ∂(P L W)) u =
      (W : ℂ) ^ 2 *
        (∑ p : Z2 L, ∑ q : Z2 L,
          ∫ ω : Ω L W,
            sameEdgeCutIntegrand L W u ω (spectralZ E u)
              ⟨[], (σ, a), []⟩ p q ∂(P L W)) -
      (spectralMSign E σ * (W : ℂ) ^ 2) *
        (∑ q : Z2 L, ∫ ω : Ω L W,
          gloop L W (HflowBlock L W u ω) (spectralZ E u)
            ((⟨[σ], [a]⟩ : LoopIdx (Z2 L)).cutGlue 1 q) ∂(P L W)) := by
  rw [deriv_expected_gloop_one_edge L W hE hu hu1 σ a,
    expectedSameEdgeCuts_one_edge, expectedSpectralCuts_one_edge]
  ring

/-- The first exact Duhamel step for a one-edge loop. Its initial condition
is the signed scalar Green value, and there is no pair-cut term. -/
theorem expected_gloop_one_edge_firstDuhamel
    {E b : ℝ} (hE : |E| < 2) (hb0 : 0 < b) (hb1 : b < 1)
    (σ : Bool) (a : Z2 L) :
    (∫ ω : Ω L W,
      gloop L W (HflowBlock L W b ω) (spectralZ E b)
        ⟨[σ], [a]⟩ ∂(P L W)) =
      initialGreenScalar E σ +
        ∫ u in (0 : ℝ)..b,
          (W : ℂ) ^ 2 * expectedSameEdgeCuts L W E u ⟨[σ], [a]⟩ +
          expectedSpectralCuts L W E u ⟨[σ], [a]⟩ := by
  have h := expected_gloop_eq_firstDuhamel L W hE hb0 hb1
    ⟨[σ], [a]⟩ (by simp [LoopIdx.WF])
  have hinit : totalInitialLoopScalar L W E ⟨[σ], [a]⟩ =
      initialGreenScalar E σ := by
    rw [← initialLoopValue_eq_total L W hE ⟨[σ], [a]⟩ (by simp [LoopIdx.WF])]
    exact initialLoopValue_one_edge L W hE σ a
  simpa [hinit, expectedPairCuts_one_edge] using h

end RBM.Gauss

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.LoopHierarchyOneEdge

/-!
# The two-edge finite expected loop hierarchy

For two edges, there are two same-edge cuts and exactly one ordered
distinct-edge pair. The expected cut products remain genuine expectations;
no factorization of a Gaussian expectation is asserted.
-/

namespace RBM.Gauss

open MeasureTheory

variable (L W : ℕ) [NeZero L] [NeZero W]

omit [NeZero L] in
/-- The sole ordered pair split of a two-edge loop is its first and second
edge, with all three surrounding segments empty. -/
theorem pairSplits_two_edges (σ₁ σ₂ : Bool) (a₁ a₂ : Z2 L) :
    pairSplits ([(σ₁, a₁), (σ₂, a₂)] : List (Bool × Z2 L)) =
      [⟨[], (σ₁, a₁), [], (σ₂, a₂), []⟩] := by
  simp [pairSplits, edgeSplits]

/-- The two-edge pair-cut family is precisely one block double sum. -/
theorem expectedPairCuts_two_edges (E u : ℝ)
    (σ₁ σ₂ : Bool) (a₁ a₂ : Z2 L) :
    expectedPairCuts L W E u ⟨[σ₁, σ₂], [a₁, a₂]⟩ =
      ∑ p : Z2 L, ∑ q : Z2 L,
        ∫ ω : Ω L W,
          pairCutIntegrand L W u ω (spectralZ E u)
            ⟨[], (σ₁, a₁), [], (σ₂, a₂), []⟩ p q ∂(P L W) := by
  simp [expectedPairCuts, pairSplits_two_edges]

/-- The two same-edge positions are enumerated in their original order. -/
theorem expectedSameEdgeCuts_two_edges (E u : ℝ)
    (σ₁ σ₂ : Bool) (a₁ a₂ : Z2 L) :
    expectedSameEdgeCuts L W E u ⟨[σ₁, σ₂], [a₁, a₂]⟩ =
      (∑ p : Z2 L, ∑ q : Z2 L,
        ∫ ω : Ω L W,
          sameEdgeCutIntegrand L W u ω (spectralZ E u)
            ⟨[], (σ₁, a₁), [(σ₂, a₂)]⟩ p q ∂(P L W)) +
      (∑ p : Z2 L, ∑ q : Z2 L,
        ∫ ω : Ω L W,
          sameEdgeCutIntegrand L W u ω (spectralZ E u)
            ⟨[(σ₁, a₁)], (σ₂, a₂), []⟩ p q ∂(P L W)) := by
  simp [expectedSameEdgeCuts, edgeSplits]

/-- The spectral drift has one term at each of the two edge positions. -/
theorem expectedSpectralCuts_two_edges (E u : ℝ)
    (σ₁ σ₂ : Bool) (a₁ a₂ : Z2 L) :
    expectedSpectralCuts L W E u ⟨[σ₁, σ₂], [a₁, a₂]⟩ =
      -(spectralMSign E σ₁ * (W : ℂ) ^ 2) *
        (∑ q : Z2 L, ∫ ω : Ω L W,
          gloop L W (HflowBlock L W u ω) (spectralZ E u)
            ((⟨[σ₁, σ₂], [a₁, a₂]⟩ : LoopIdx (Z2 L)).cutGlue 1 q)
              ∂(P L W)) +
      -(spectralMSign E σ₂ * (W : ℂ) ^ 2) *
        (∑ q : Z2 L, ∫ ω : Ω L W,
          gloop L W (HflowBlock L W u ω) (spectralZ E u)
            ((⟨[σ₁, σ₂], [a₁, a₂]⟩ : LoopIdx (Z2 L)).cutGlue 2 q)
              ∂(P L W)) := by
  simp [expectedSpectralCuts, spectralEdgeSplits]

/-- The finite expected hierarchy at two edges retains all three cut
families, including the unique distinct-edge contraction. -/
theorem deriv_expected_gloop_two_edges
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (σ₁ σ₂ : Bool) (a₁ a₂ : Z2 L) :
    deriv (fun v : ℝ => ∫ ω : Ω L W,
      gloop L W (HflowBlock L W v ω) (spectralZ E v)
        ⟨[σ₁, σ₂], [a₁, a₂]⟩ ∂(P L W)) u =
      (W : ℂ) ^ 2 * expectedSameEdgeCuts L W E u ⟨[σ₁, σ₂], [a₁, a₂]⟩ +
      (W : ℂ) ^ 2 * expectedPairCuts L W E u ⟨[σ₁, σ₂], [a₁, a₂]⟩ +
      expectedSpectralCuts L W E u ⟨[σ₁, σ₂], [a₁, a₂]⟩ := by
  exact deriv_expected_gloop_eq_hierarchyCuts L W hE hu hu1
    ⟨[σ₁, σ₂], [a₁, a₂]⟩ (by simp [LoopIdx.WF])

/-- Exact first Duhamel step at two edges. The initial scalar contains the
block-label equality indicator and `W⁻²` projector normalization. -/
theorem expected_gloop_two_edges_firstDuhamel
    {E b : ℝ} (hE : |E| < 2) (hb0 : 0 < b) (hb1 : b < 1)
    (σ₁ σ₂ : Bool) (a₁ a₂ : Z2 L) :
    (∫ ω : Ω L W,
      gloop L W (HflowBlock L W b ω) (spectralZ E b)
        ⟨[σ₁, σ₂], [a₁, a₂]⟩ ∂(P L W)) =
      initialGreenScalar E σ₁ * initialGreenScalar E σ₂ *
        (if a₁ = a₂ then (W : ℂ)⁻¹ ^ 2 else 0) +
      ∫ u in (0 : ℝ)..b,
        (W : ℂ) ^ 2 * expectedSameEdgeCuts L W E u
          ⟨[σ₁, σ₂], [a₁, a₂]⟩ +
        (W : ℂ) ^ 2 * expectedPairCuts L W E u
          ⟨[σ₁, σ₂], [a₁, a₂]⟩ +
        expectedSpectralCuts L W E u ⟨[σ₁, σ₂], [a₁, a₂]⟩ := by
  have h := expected_gloop_eq_firstDuhamel L W hE hb0 hb1
    ⟨[σ₁, σ₂], [a₁, a₂]⟩ (by simp [LoopIdx.WF])
  have hinit : totalInitialLoopScalar L W E ⟨[σ₁, σ₂], [a₁, a₂]⟩ =
      initialGreenScalar E σ₁ * initialGreenScalar E σ₂ *
        (if a₁ = a₂ then (W : ℂ)⁻¹ ^ 2 else 0) := by
    rw [← initialLoopValue_eq_total L W hE
      ⟨[σ₁, σ₂], [a₁, a₂]⟩ (by simp [LoopIdx.WF])]
    exact initialLoopValue_two_edges L W hE σ₁ σ₂ a₁ a₂
  simpa only [hinit] using h

end RBM.Gauss

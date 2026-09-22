/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.LoopHierarchyEnvelopeLabelSum

/-!
# One-edge and two-edge finite hierarchy envelopes

The first two lengths expose the crude finite-size powers explicitly. These
are evaluations of the already proved deterministic envelope, not moment
closure estimates.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

omit [NeZero W] in
/-- The block torus has `L²` labels. -/
theorem card_Z2_eq_sq : (Fintype.card (Z2 L) : ℝ) = (L : ℝ) ^ 2 := by
  simp [Z2, Fintype.card_prod, pow_two]

omit [NeZero W] in
/-- At length one there is one same-edge cut, no pair cut, and one spectral
cut. -/
theorem loopHierarchyLengthEnvelope_one (η E : ℝ) :
    loopHierarchyLengthEnvelope L W η E 1 =
      (W : ℝ) ^ 2 * ((L : ℝ) ^ 2 *
        cutResolventEnvelope L W η 2 * cutResolventEnvelope L W η 1) +
      ‖spectralM E‖ * (W : ℝ) ^ 2 * (L : ℝ) ^ 2 *
        cutResolventEnvelope L W η 2 := by
  simp [loopHierarchyLengthEnvelope]
  ring

omit [NeZero W] in
/-- At length two there are two same-edge cuts, one pair cut, and two
spectral cuts. -/
theorem loopHierarchyLengthEnvelope_two (η E : ℝ) :
    loopHierarchyLengthEnvelope L W η E 2 =
      2 * (W : ℝ) ^ 2 * (L : ℝ) ^ 2 *
        cutResolventEnvelope L W η 3 * cutResolventEnvelope L W η 1 +
      (W : ℝ) ^ 2 * (L : ℝ) ^ 2 *
        cutResolventEnvelope L W η 4 * cutResolventEnvelope L W η 0 +
      2 * ‖spectralM E‖ * (W : ℝ) ^ 2 * (L : ℝ) ^ 2 *
        cutResolventEnvelope L W η 3 := by
  simp [loopHierarchyLengthEnvelope]
  ring

/-- Label-summed one-edge finite-time bound with all combinatorial
coefficients evaluated. -/
theorem sum_norm_expected_gloop_one_edge_le
    (hL : 3 ≤ L) (σ : Bool)
    {E u η : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hη : 0 < η)
    (hz : ∀ v ∈ Set.Icc 0 u, η ≤ |(spectralZ E v).im|) :
    (∑ f : Fin 1 → Z2 L,
      ‖∫ ω : Ω L W,
        gloop L W (HflowBlock L W u ω) (spectralZ E u)
          ⟨[σ], List.ofFn f⟩ ∂(P L W)‖) ≤
      (L : ℝ) ^ 2 +
      (L : ℝ) ^ 2 *
        ((W : ℝ) ^ 2 * ((L : ℝ) ^ 2 *
          cutResolventEnvelope L W η 2 * cutResolventEnvelope L W η 1) +
         ‖spectralM E‖ * (W : ℝ) ^ 2 * (L : ℝ) ^ 2 *
          cutResolventEnvelope L W η 2) * u := by
  have h := sum_norm_expected_gloop_ofFn_le_lengthEnvelope
    L W hL (n := 1) (by omega) [σ] rfl hE hu0 hu1 hη hz
  simpa [loopHierarchyLengthEnvelope_one, card_Z2_eq_sq, pow_two] using h

/-- Label-summed two-edge finite-time bound with its exact initial
`W⁻²` factor and its single pair-cut contribution. -/
theorem sum_norm_expected_gloop_two_edges_le
    (hL : 3 ≤ L) (σ₁ σ₂ : Bool)
    {E u η : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hη : 0 < η)
    (hz : ∀ v ∈ Set.Icc 0 u, η ≤ |(spectralZ E v).im|) :
    (∑ f : Fin 2 → Z2 L,
      ‖∫ ω : Ω L W,
        gloop L W (HflowBlock L W u ω) (spectralZ E u)
          ⟨[σ₁, σ₂], List.ofFn f⟩ ∂(P L W)‖) ≤
      (L : ℝ) ^ 2 * ((W : ℝ)⁻¹) ^ 2 +
      (L : ℝ) ^ 4 *
        (2 * (W : ℝ) ^ 2 * (L : ℝ) ^ 2 *
           cutResolventEnvelope L W η 3 * cutResolventEnvelope L W η 1 +
         (W : ℝ) ^ 2 * (L : ℝ) ^ 2 *
           cutResolventEnvelope L W η 4 * cutResolventEnvelope L W η 0 +
         2 * ‖spectralM E‖ * (W : ℝ) ^ 2 * (L : ℝ) ^ 2 *
           cutResolventEnvelope L W η 3) * u := by
  have h := sum_norm_expected_gloop_ofFn_le_lengthEnvelope
    L W hL (n := 2) (by omega) [σ₁, σ₂] rfl hE hu0 hu1 hη hz
  rw [loopHierarchyLengthEnvelope_two] at h
  convert h using 1
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.cast_pow,
    card_Z2_eq_sq]
  ring

end RBM.Gauss

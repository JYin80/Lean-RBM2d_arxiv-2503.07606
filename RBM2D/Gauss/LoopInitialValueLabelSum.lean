/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopInitialValueBound

/-!
# Summing initial-loop magnitudes over block labels

The two-edge case already exhibits the exact counting mechanism: only equal
labels survive, and each of the `L²` blocks contributes `W⁻²`.
-/

namespace RBM.Gauss

open Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

omit [NeZero W] in
/-- There are `L²` block labels on the two-dimensional torus. -/
theorem card_Z2 : Fintype.card (Z2 L) = L ^ 2 := by
  simp [Z2, pow_two]

/-- The two-edge magnitude is supported precisely on equal block labels. -/
theorem norm_initialLoopValue_two_edges {E : ℝ} (hE : |E| < 2)
    (σ₁ σ₂ : Bool) (a b : Z2 L) :
    ‖initialLoopValue L W E ⟨[σ₁, σ₂], [a, b]⟩‖ =
      if a = b then ((W : ℝ)⁻¹) ^ 2 else 0 := by
  rw [initialLoopValue_two_edges L W hE σ₁ σ₂ a b]
  by_cases hab : a = b <;>
    simp [hab, norm_initialGreenScalar hE, norm_inv]

/-- Summing over both block labels leaves exactly one contribution per block. -/
theorem sum_norm_initialLoopValue_two_edges {E : ℝ} (hE : |E| < 2)
    (σ₁ σ₂ : Bool) :
    ∑ a : Z2 L, ∑ b : Z2 L,
      ‖initialLoopValue L W E ⟨[σ₁, σ₂], [a, b]⟩‖ =
        (L ^ 2 : ℕ) * ((W : ℝ)⁻¹) ^ 2 := by
  simp_rw [norm_initialLoopValue_two_edges L W hE σ₁ σ₂]
  simp [card_Z2 L]

/-- A concrete sum: four blocks, one surviving label pair per block. -/
example : ∑ a : Z2 2, ∑ b : Z2 2,
    ‖initialLoopValue 2 1 0 ⟨[true, false], [a, b]⟩‖ = 4 := by
  simpa using sum_norm_initialLoopValue_two_edges 2 1
    (by norm_num : |(0 : ℝ)| < 2) true false

end RBM.Gauss

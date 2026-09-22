/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopInitialValueConstantCount

/-!
# Three-edge initial-loop label sum

Only the constant triples of block labels survive. There are exactly `L²`
such triples, each of magnitude `W⁻⁴`.
-/

namespace RBM.Gauss

open Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Exact three-edge magnitude, with both adjacent equality indicators. -/
theorem norm_initialLoopValue_three_edges {E : ℝ} (hE : |E| < 2)
    (σ₁ σ₂ σ₃ : Bool) (a b c : Z2 L) :
    ‖initialLoopValue L W E ⟨[σ₁, σ₂, σ₃], [a, b, c]⟩‖ =
      if a = b ∧ b = c then ((W : ℝ)⁻¹) ^ 4 else 0 := by
  by_cases hab : a = b <;> by_cases hbc : b = c
  · subst b
    subst c
    simpa using norm_initialLoopValue_all_same L W hE
      ⟨[σ₁, σ₂, σ₃], [a, a, a]⟩ (by rfl) a [a, a] rfl (by simp)
  · have hm : AdjacentMismatch L [a, b, c] := by simp [AdjacentMismatch, hbc]
    rw [initialLoopValue_zero_of_adjacentMismatch L W hE
      ⟨[σ₁, σ₂, σ₃], [a, b, c]⟩ (by rfl) a [b, c] rfl hm]
    simp [hab, hbc]
  · have hm : AdjacentMismatch L [a, b, c] := by simp [AdjacentMismatch, hab]
    rw [initialLoopValue_zero_of_adjacentMismatch L W hE
      ⟨[σ₁, σ₂, σ₃], [a, b, c]⟩ (by rfl) a [b, c] rfl hm]
    simp [hab]
  · have hm : AdjacentMismatch L [a, b, c] := by simp [AdjacentMismatch, hab]
    rw [initialLoopValue_zero_of_adjacentMismatch L W hE
      ⟨[σ₁, σ₂, σ₃], [a, b, c]⟩ (by rfl) a [b, c] rfl hm]
    simp [hab]

/-- Summing all three labels leaves one constant triple per block. -/
theorem sum_norm_initialLoopValue_three_edges {E : ℝ} (hE : |E| < 2)
    (σ₁ σ₂ σ₃ : Bool) :
    ∑ a : Z2 L, ∑ b : Z2 L, ∑ c : Z2 L,
      ‖initialLoopValue L W E ⟨[σ₁, σ₂, σ₃], [a, b, c]⟩‖ =
        (L ^ 2 : ℕ) * ((W : ℝ)⁻¹) ^ 4 := by
  simp_rw [norm_initialLoopValue_three_edges L W hE σ₁ σ₂ σ₃]
  have hinner (a b : Z2 L) :
      (∑ c : Z2 L,
        if a = b ∧ b = c then ((W : ℝ)⁻¹) ^ 4 else 0) =
      if a = b then ((W : ℝ)⁻¹) ^ 4 else 0 := by
    by_cases hab : a = b <;> simp [hab]
  simp_rw [hinner]
  simp [card_Z2 L]

/-- Concrete `2 × 2` block torus and unit block width: four surviving triples. -/
example : ∑ a : Z2 2, ∑ b : Z2 2, ∑ c : Z2 2,
    ‖initialLoopValue 2 1 0 ⟨[true, false, true], [a, b, c]⟩‖ = 4 := by
  simpa using sum_norm_initialLoopValue_three_edges 2 1
    (by norm_num : |(0 : ℝ)| < 2) true false true

end RBM.Gauss

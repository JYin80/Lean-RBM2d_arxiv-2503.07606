/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopInitialValueProjectionWords

/-!
# Total scalar initial-loop formula

The empty word has the trace of the identity matrix. Nonempty words use the
adjacent block-label indicators from the projector-word formula.
-/

namespace RBM.Gauss

open Matrix

variable (L W : ℕ) [NeZero L] [NeZero W]

omit [NeZero W] in
/-- The empty loop has the full matrix dimension as its initial value. -/
theorem initialLoopValue_empty (E : ℝ) :
    initialLoopValue L W E (⟨[], []⟩ : LoopIdx (Z2 L)) =
      (((L * W) ^ 2 : ℕ) : ℂ) := by
  rw [initialLoopValue_eq_trace_product]
  simp
  ring

/-- Closed initial value for every well-formed finite loop. -/
noncomputable def totalInitialLoopScalar (E : ℝ) (I : LoopIdx (Z2 L)) : ℂ :=
  match I.a with
  | [] => (((L * W) ^ 2 : ℕ) : ℂ)
  | a :: as =>
      ((I.σ.zip I.a).map fun p => initialGreenScalar E p.1).prod *
        adjacentBlockWeight L W (a :: as)

/-- The empty and nonempty formulas combine without an exceptional loop case. -/
theorem initialLoopValue_eq_total {E : ℝ} (hE : |E| < 2)
    (I : LoopIdx (Z2 L)) (hI : I.WF) :
    initialLoopValue L W E I = totalInitialLoopScalar L W E I := by
  cases I with
  | mk σ a =>
      cases a with
      | nil =>
          have hσ : σ = [] :=
            List.eq_nil_of_length_eq_zero (by simpa [LoopIdx.WF] using hI)
          subst σ
          exact initialLoopValue_empty L W E
      | cons a as =>
          exact initialLoopValue_nonempty L W hE ⟨σ, a :: as⟩ hI a as rfl

/-- Concrete normalization check: the empty `3 × 2` block matrix has
`(3·2)² = 36` diagonal entries. -/
example : initialLoopValue 3 2 0 (⟨[], []⟩ : LoopIdx (Z2 3)) = 36 := by
  simpa using initialLoopValue_empty 3 2 0

end RBM.Gauss

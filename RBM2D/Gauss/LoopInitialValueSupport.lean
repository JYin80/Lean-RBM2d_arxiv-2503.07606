/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopInitialValueProjectionWords

/-!
# Support and normalization of the initial-loop value

Adjacent unequal block labels annihilate the initial loop. If every label
equals the first, the normalized projector word contributes `W⁻²` for each
edge after the first.
-/

namespace RBM.Gauss

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- A finite block-label word contains an unequal adjacent pair. -/
def AdjacentMismatch : List (Z2 L) → Prop
  | [] => False
  | [_] => False
  | a :: b :: as => a ≠ b ∨ AdjacentMismatch (b :: as)

omit [NeZero L] [NeZero W] in
theorem adjacentBlockWeight_zero_of_mismatch (as : List (Z2 L))
    (hm : AdjacentMismatch L as) : adjacentBlockWeight L W as = 0 := by
  induction as with
  | nil => simp [AdjacentMismatch] at hm
  | cons a as ih =>
      cases as with
      | nil => simp [AdjacentMismatch] at hm
      | cons b bs =>
          change a ≠ b ∨ AdjacentMismatch L (b :: bs) at hm
          rcases hm with hab | htail
          · simp [adjacentBlockWeight, hab]
          · have ht := ih htail
            simp [adjacentBlockWeight, ht]

omit [NeZero L] [NeZero W] in
/-- When all labels agree, each additional projector supplies one `W⁻²`. -/
theorem adjacentBlockWeight_all_same (a : Z2 L) (as : List (Z2 L))
    (hsame : ∀ b ∈ as, b = a) :
    adjacentBlockWeight L W (a :: as) =
      ((W : ℂ)⁻¹ ^ 2) ^ as.length := by
  induction as generalizing a with
  | nil => simp [adjacentBlockWeight]
  | cons b bs ih =>
      have hab : b = a := hsame b (by simp)
      subst b
      have hbs : ∀ c ∈ bs, c = a := by
        intro c hc
        exact hsame c (by simp [hc])
      simp only [adjacentBlockWeight, List.length_cons, pow_succ]
      rw [ih a hbs]
      simp only [ite_true]
      ring

end RBM.Gauss

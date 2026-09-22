/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopInitialValueLabelSum

/-!
# Counting constant block-label assignments

For a nonempty finite edge set, a constant assignment is uniquely determined
by its value at the first edge. Thus there are exactly `L²` such assignments.
-/

namespace RBM.Gauss

open Finset

variable (L : ℕ) [NeZero L]

/-- Constant assignments of block labels to `n` edge positions. -/
noncomputable def constantBlockAssignments (n : ℕ) :
    Finset (Fin n → Z2 L) :=
  Finset.univ.image (fun a : Z2 L => fun _ : Fin n => a)

omit [NeZero L] in
/-- For `n > 0`, two constant assignments agree only when their labels agree. -/
theorem constantBlockAssignment_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (fun a : Z2 L => fun _ : Fin n => a) := by
  intro a b hab
  exact congrFun hab ⟨0, hn⟩

/-- The constant assignments are in bijection with the `L²` block labels. -/
theorem card_constantBlockAssignments {n : ℕ} (hn : 0 < n) :
    (constantBlockAssignments L n).card = L ^ 2 := by
  classical
  unfold constantBlockAssignments
  rw [Finset.card_image_of_injective Finset.univ
    (constantBlockAssignment_injective L hn)]
  simpa using card_Z2 L

/-- A concrete two-edge count on a `3 × 3` block torus. -/
example : (constantBlockAssignments 3 2).card = 9 := by
  simpa using card_constantBlockAssignments 3 (by norm_num : 0 < 2)

end RBM.Gauss

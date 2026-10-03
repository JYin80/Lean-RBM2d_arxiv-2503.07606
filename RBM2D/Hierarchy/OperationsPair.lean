/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.Operations

/-!
# Two-edge cut-and-glue on loop indices

These are the index operations in the left and right cases of `Def:oper_loop`.
Positions are one-based, with `1 ≤ k < l ≤ I.length`. The left loop contains
the original final block label; the right loop contains the intervening labels.
The definitions are purely combinatorial. Matrix-word and generator identities
are separate statements.
-/

namespace RBM.LoopIdx

variable {α : Type*}

/-- Close the chain containing the final block label after cutting edges `k,l`. -/
def cutGlueL (k l : ℕ) (b : α) (I : LoopIdx α) : LoopIdx α where
  σ := I.σ.take k ++ I.σ.drop (l - 1)
  a := I.a.take (k - 1) ++ b :: I.a.drop (l - 1)

/-- Close the chain between edges `k,l` after cutting them. -/
def cutGlueR (k l : ℕ) (b : α) (I : LoopIdx α) : LoopIdx α where
  σ := (I.σ.drop (k - 1)).take (l - k + 1)
  a := (I.a.drop (k - 1)).take (l - k) ++ [b]

/-- The left resulting loop has length `k+n-l+1`. -/
theorem length_cutGlueL (I : LoopIdx α) (b : α) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) :
    (I.cutGlueL k l b).length = k + I.length - l + 1 := by
  simp only [length, cutGlueL, List.length_append, List.length_take,
    List.length_cons, List.length_drop] at hl ⊢
  omega

/-- The right resulting loop has length `l-k+1`. -/
theorem length_cutGlueR (I : LoopIdx α) (b : α) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) :
    (I.cutGlueR k l b).length = l - k + 1 := by
  simp only [length, cutGlueR, List.length_append, List.length_take,
    List.length_drop, List.length_singleton] at hl ⊢
  omega

/-- Cutting two edges and adding a new block to each component adds two edges. -/
theorem length_cutGlueL_add_length_cutGlueR (I : LoopIdx α) (b : α)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) :
    (I.cutGlueL k l b).length + (I.cutGlueR k l b).length = I.length + 2 := by
  rw [length_cutGlueL I b hk hkl hl, length_cutGlueR I b hk hkl hl]
  omega

/-- A valid left cut preserves matching sign and block-label lengths. -/
theorem WF.cutGlueL {I : LoopIdx α} (hI : I.WF) (b : α)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) :
    (I.cutGlueL k l b).WF := by
  simp only [WF, length, LoopIdx.cutGlueL, List.length_append,
    List.length_take, List.length_cons, List.length_drop] at hI hl ⊢
  omega

/-- A valid right cut preserves matching sign and block-label lengths. -/
theorem WF.cutGlueR {I : LoopIdx α} (hI : I.WF) (b : α)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) :
    (I.cutGlueR k l b).WF := by
  simp only [WF, length, LoopIdx.cutGlueR, List.length_append,
    List.length_take, List.length_drop, List.length_singleton] at hI hl ⊢
  omega

end RBM.LoopIdx

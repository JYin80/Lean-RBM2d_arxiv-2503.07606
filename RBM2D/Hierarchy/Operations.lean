/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.Loops

/-!
# Single-edge cut-and-glue on loop indices

This is the first operation of `Def:oper_loop`. Cutting the `k`-th Green edge
inserts one block observable `E_b` and duplicates that edge's sign. The
matrix-word theorem below verifies this meaning at the first edge.
-/

namespace RBM

open Matrix

namespace LoopIdx

variable {α : Type*}

/-- The paper's single-edge cut-and-glue operation `G_k^(b)`, with one-based
edge position `k`. The statement about length and well-formedness below uses
`1 ≤ k ≤ I.length`. -/
def cutGlue (k : ℕ) (b : α) (I : LoopIdx α) : LoopIdx α where
  σ := I.σ.take k ++ I.σ.drop (k - 1)
  a := I.a.take (k - 1) ++ b :: I.a.drop (k - 1)

/-- The inserted block precedes the original first block when `k=1`. -/
theorem cutGlue_first (s : Bool) (a b : α) (σ : List Bool) (as : List α) :
    cutGlue 1 b (⟨s :: σ, a :: as⟩ : LoopIdx α) =
      ⟨s :: s :: σ, b :: a :: as⟩ := by
  simp [cutGlue]

/-- A cut at a general one-based position can be read from a matching prefix:
the chosen sign is duplicated and the new block goes immediately before the
old block on that edge. -/
theorem cutGlue_split (σ₁ σ₂ : List Bool) (a₁ a₂ : List α)
    (s : Bool) (a b : α) (h₁ : σ₁.length = a₁.length) :
    cutGlue (σ₁.length + 1) b
      (⟨σ₁ ++ s :: σ₂, a₁ ++ a :: a₂⟩ : LoopIdx α) =
      ⟨σ₁ ++ s :: s :: σ₂, a₁ ++ b :: a :: a₂⟩ := by
  simp [cutGlue, List.take_append, h₁]

/-- The operation adds exactly one Green edge. -/
theorem length_cutGlue (I : LoopIdx α) (b : α) {k : ℕ}
    (hk : k ≤ I.length) :
    (I.cutGlue k b).length = I.length + 1 := by
  simp only [length, cutGlue, List.length_append, List.length_take,
    List.length_cons, List.length_drop] at hk ⊢
  omega

/-- A valid one-based cut preserves the matching of signs and block labels. -/
theorem WF.cutGlue {I : LoopIdx α} (hI : I.WF) (b : α) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ I.length) :
    (I.cutGlue k b).WF := by
  simp only [WF, length, LoopIdx.cutGlue, List.length_append,
    List.length_take, List.length_cons, List.length_drop] at hI hk ⊢
  omega

end LoopIdx

section MatrixWord

variable (L W : ℕ) [NeZero L]

/-- At the first edge, the index operation realizes the literal replacement
`G_s E_a ↦ G_s E_b G_s E_a` inside the loop's matrix word. -/
theorem gloopProd_cutGlue_first
    (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (s : Bool) (a b : Z2 L) (σ : List Bool) (as : List (Z2 L)) :
    gloopProd L W H z
      ((⟨s :: σ, a :: as⟩ : LoopIdx (Z2 L)).cutGlue 1 b) =
      Gsig H z s * Eblk L W b *
        (Gsig H z s * Eblk L W a * gloopProd L W H z ⟨σ, as⟩) := by
  rw [LoopIdx.cutGlue_first]
  simp only [gloopProd_cons]

/-- At any edge selected by a matching prefix, the matrix word has the
literal local replacement `G_s E_a ↦ G_s E_b G_s E_a`. -/
theorem gloopProd_cutGlue_split
    (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Z2 L))
    (s : Bool) (a b : Z2 L) (h₁ : σ₁.length = a₁.length) :
    gloopProd L W H z
      ((⟨σ₁ ++ s :: σ₂, a₁ ++ a :: a₂⟩ : LoopIdx (Z2 L)).cutGlue
        (σ₁.length + 1) b) =
      gloopProd L W H z ⟨σ₁, a₁⟩ *
        (Gsig H z s * Eblk L W b *
          (Gsig H z s * Eblk L W a * gloopProd L W H z ⟨σ₂, a₂⟩)) := by
  rw [LoopIdx.cutGlue_split σ₁ σ₂ a₁ a₂ s a b h₁]
  rw [gloopProd_append h₁]
  simp only [gloopProd_cons]

end MatrixWord

end RBM

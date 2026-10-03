/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.OperationsPair

/-!
# Matrix words after a two-edge cut

The loop is supplied as three matching list segments, with distinguished
edges `s` and `t`. This makes the two cut-and-glue matrix words explicit.
-/

namespace RBM

open Matrix

namespace LoopIdx

variable {α : Type*}

/-- Index list of the chain containing the final label after a two-edge cut. -/
theorem cutGlueL_split (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List α)
    (s t : Bool) (a c b : α) (h₁ : σ₁.length = a₁.length)
    (h₂ : σ₂.length = a₂.length) :
    cutGlueL (σ₁.length + 1) (σ₁.length + σ₂.length + 2) b
      (⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
        a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx α) =
      ⟨σ₁ ++ [s, t] ++ σ₃, a₁ ++ [b, c] ++ a₃⟩ := by
  have htakeσ : (σ₁ ++ s :: σ₂ ++ t :: σ₃).take (σ₁.length + 1) = σ₁ ++ [s] := by
    simp [List.take_append]
  have htakea : (a₁ ++ a :: a₂ ++ c :: a₃).take σ₁.length = a₁ := by
    rw [h₁]
    simp
  have hdropσ : (σ₁ ++ s :: σ₂ ++ t :: σ₃).drop
      (σ₁.length + σ₂.length + 1) = t :: σ₃ := by
    calc
      _ = ((σ₁ ++ s :: σ₂) ++ t :: σ₃).drop (σ₁ ++ s :: σ₂).length := by
        congr 1; simp [List.length_append, Nat.add_assoc]
      _ = t :: σ₃ := List.drop_append_length
  have hdropa : (a₁ ++ a :: a₂ ++ c :: a₃).drop
      (σ₁.length + σ₂.length + 1) = c :: a₃ := by
    calc
      _ = ((a₁ ++ a :: a₂) ++ c :: a₃).drop (a₁ ++ a :: a₂).length := by
        congr 1; simp [h₁, h₂, List.length_append, Nat.add_assoc]
      _ = c :: a₃ := List.drop_append_length
  apply LoopIdx.ext
  · change (σ₁ ++ s :: σ₂ ++ t :: σ₃).take (σ₁.length + 1) ++
        (σ₁ ++ s :: σ₂ ++ t :: σ₃).drop (σ₁.length + σ₂.length + 1) = _
    rw [htakeσ, hdropσ]
    simp
  · change (a₁ ++ a :: a₂ ++ c :: a₃).take σ₁.length ++ b ::
        (a₁ ++ a :: a₂ ++ c :: a₃).drop (σ₁.length + σ₂.length + 1) = _
    rw [htakea, hdropa]
    simp

/-- Index list of the intervening chain after a two-edge cut. -/
theorem cutGlueR_split (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List α)
    (s t : Bool) (a c b : α) (h₁ : σ₁.length = a₁.length)
    (h₂ : σ₂.length = a₂.length) :
    cutGlueR (σ₁.length + 1) (σ₁.length + σ₂.length + 2) b
      (⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
        a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx α) =
      ⟨s :: σ₂ ++ [t], a :: a₂ ++ [b]⟩ := by
  simp [cutGlueR, h₁, h₂, List.take_append,
    show a₁.length + a₂.length + 1 - a₁.length = a₂.length + 1 by omega]

end LoopIdx

section PairWords

variable (L W : ℕ) [NeZero L]
variable (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)

/-- Matrix word for the left chain after a two-edge cut. The original middle
segment disappears; the inserted block `b` joins edges `s` and `t`. -/
theorem gloopProd_cutGlueL_split
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Z2 L))
    (s t : Bool) (a c b : Z2 L) (h₁ : σ₁.length = a₁.length)
    (h₂ : σ₂.length = a₂.length) :
    gloopProd L W H z
      ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
          a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueL
        (σ₁.length + 1) (σ₁.length + σ₂.length + 2) b) =
      gloopProd L W H z ⟨σ₁, a₁⟩ *
        (Gsig H z s * Eblk L W b *
          (Gsig H z t * Eblk L W c * gloopProd L W H z ⟨σ₃, a₃⟩)) := by
  rw [LoopIdx.cutGlueL_split σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c b h₁ h₂]
  simp only [List.append_assoc]
  rw [gloopProd_append h₁]
  rfl

/-- Matrix word for the right chain after a two-edge cut. -/
theorem gloopProd_cutGlueR_split
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Z2 L))
    (s t : Bool) (a c b : Z2 L) (h₁ : σ₁.length = a₁.length)
    (h₂ : σ₂.length = a₂.length) :
    gloopProd L W H z
      ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
          a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueR
        (σ₁.length + 1) (σ₁.length + σ₂.length + 2) b) =
      Gsig H z s * Eblk L W a *
        (gloopProd L W H z ⟨σ₂, a₂⟩ * (Gsig H z t * Eblk L W b)) := by
  rw [LoopIdx.cutGlueR_split σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c b h₁ h₂]
  change Gsig H z s * Eblk L W a *
      gloopProd L W H z ⟨σ₂ ++ [t], a₂ ++ [b]⟩ = _
  rw [gloopProd_append h₂]
  simp [gloopProd]

/-- The corresponding left cut-and-glue loop is the trace of its explicit
matrix word. -/
theorem gloop_cutGlueL_split
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Z2 L))
    (s t : Bool) (a c b : Z2 L) (h₁ : σ₁.length = a₁.length)
    (h₂ : σ₂.length = a₂.length) :
    gloop L W H z
      ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
          a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueL
        (σ₁.length + 1) (σ₁.length + σ₂.length + 2) b) =
      Matrix.trace (gloopProd L W H z ⟨σ₁, a₁⟩ *
        (Gsig H z s * Eblk L W b *
          (Gsig H z t * Eblk L W c * gloopProd L W H z ⟨σ₃, a₃⟩))) := by
  rw [gloop, gloopProd_cutGlueL_split L W H z σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c b h₁ h₂]

/-- The corresponding right cut-and-glue loop is the trace of its explicit
matrix word. -/
theorem gloop_cutGlueR_split
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Z2 L))
    (s t : Bool) (a c b : Z2 L) (h₁ : σ₁.length = a₁.length)
    (h₂ : σ₂.length = a₂.length) :
    gloop L W H z
      ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
          a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueR
        (σ₁.length + 1) (σ₁.length + σ₂.length + 2) b) =
      Matrix.trace (Gsig H z s * Eblk L W a *
        (gloopProd L W H z ⟨σ₂, a₂⟩ * (Gsig H z t * Eblk L W b))) := by
  rw [gloop, gloopProd_cutGlueR_split L W H z σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c b h₁ h₂]

end PairWords

end RBM

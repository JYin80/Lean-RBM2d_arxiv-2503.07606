/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionUnused

/-!
# Two cut chains as the left and right G-loops

At two distinguished Green edges, the trace contraction has the form
`trace (A B C B)`. The matrices `A` and `C` below are the two open chains.
Inserting a normalized block projector into either chain closes it into the
corresponding cut-and-glue loop.
-/

namespace RBM

open Matrix

variable (L W : ℕ) [NeZero L]
variable (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)

/-- The open chain containing the original final block label, ordered for
the cyclic trace contraction. -/
noncomputable def cutLeftChain
    (σ₁ σ₃ : List Bool) (a₁ a₃ : List (Z2 L))
    (s t : Bool) (c : Z2 L) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  (Gsig H z t * Eblk L W c * gloopProd L W H z ⟨σ₃, a₃⟩) *
    gloopProd L W H z ⟨σ₁, a₁⟩ * Gsig H z s

/-- The open chain between the two distinguished Green edges. -/
noncomputable def cutRightChain
    (σ₂ : List Bool) (a₂ : List (Z2 L))
    (s t : Bool) (a : Z2 L) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  Gsig H z s * Eblk L W a * gloopProd L W H z ⟨σ₂, a₂⟩ * Gsig H z t

/-- Closing the first chain with `E_b` gives the left cut-and-glue loop. -/
theorem trace_cutLeftChain_Eblk
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Z2 L))
    (s t : Bool) (a c b : Z2 L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    Matrix.trace (cutLeftChain L W H z σ₁ σ₃ a₁ a₃ s t c * Eblk L W b) =
      gloop L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueL
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) b) := by
  rw [gloop_cutGlueL_split L W H z σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c b h₁ h₂]
  unfold cutLeftChain
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- Closing the second chain with `E_b` gives the right cut-and-glue loop. -/
theorem trace_cutRightChain_Eblk
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Z2 L))
    (s t : Bool) (a c b : Z2 L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    Matrix.trace (cutRightChain L W H z σ₂ a₂ s t a * Eblk L W b) =
      gloop L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueR
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) b) := by
  rw [gloop_cutGlueR_split L W H z σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c b h₁ h₂]
  simp only [cutRightChain, Matrix.mul_assoc]

/-- Pulling a block matrix back to the physical lattice and relabeling it
again recovers the original matrix. -/
theorem blockRelabel_submatrix_split [NeZero W]
    (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    Gauss.blockRelabel L W (M.submatrix (split L W) (split L W)) = M := by
  ext u v
  obtain ⟨i, rfl⟩ := (split_bijective L W).2 u
  obtain ⟨j, rfl⟩ := (split_bijective L W).2 v
  rw [Gauss.blockRelabel_apply_split]
  rfl

/-- The full Gaussian coordinate contraction of the two open chains is the
block-weighted product of their cut-and-glue loop traces. This is a fixed
matrix identity, independent of any loop derivative or expected generator. -/
theorem sum_coordinate_cutChains [NeZero W]
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Z2 L))
    (s t : Bool) (a c : Z2 L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    let A := (cutLeftChain L W H z σ₁ σ₃ a₁ a₃ s t c).submatrix
      (split L W) (split L W)
    let C := (cutRightChain L W H z σ₂ a₂ s t a).submatrix
      (split L W) (split L W)
    ∑ γ : Gauss.Coord L W,
        (((Gauss.gvar L W γ : ℝ) : ℂ) *
          Matrix.trace (A * Gauss.coordinateMatrix L W γ * C *
            Gauss.coordinateMatrix L W γ)) =
      (W : ℂ) ^ 2 * ∑ u : Z2 L, ∑ v : Z2 L,
        gloop L W H z
          ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
              a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueL
            (σ₁.length + 1) (σ₁.length + σ₂.length + 2) u) *
          SB L u v *
        gloop L W H z
          ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
              a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueR
            (σ₁.length + 1) (σ₁.length + σ₂.length + 2) v) := by
  dsimp only
  rw [Gauss.sum_allCoords_trace_blocks]
  rw [blockRelabel_submatrix_split, blockRelabel_submatrix_split]
  congr 1
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [trace_cutLeftChain_Eblk L W H z σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c u h₁ h₂,
    trace_cutRightChain_Eblk L W H z σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c v h₁ h₂]

end RBM

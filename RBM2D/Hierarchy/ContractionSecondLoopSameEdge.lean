/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionSecondLoop

/-!
# A single-edge term of the second loop derivative
-/

namespace RBM

open Matrix

variable (L W : ℕ) [NeZero L] [NeZero W]

private theorem trace_blockRelabel_sameEdge
    (M : Matrix (Gauss.Idx L W) (Gauss.Idx L W) ℂ) :
    Matrix.trace (Gauss.blockRelabel L W M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag, Gauss.blockRelabel]
  exact (Equiv.sum_comp (splitEquiv L W).symm (fun i => M i i))

private theorem blockRelabel_mul_sameEdge
    (M N : Matrix (Gauss.Idx L W) (Gauss.Idx L W) ℂ) :
    Gauss.blockRelabel L W (M * N) =
      Gauss.blockRelabel L W M * Gauss.blockRelabel L W N := by
  exact (Matrix.submatrix_mul_equiv M N
    (splitEquiv L W).symm (splitEquiv L W).symm (splitEquiv L W).symm).symm

private theorem trace_coordinateBlock_pair_sameEdge
    (A C : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (γ : Gauss.Coord L W) :
    Matrix.trace (A * Gauss.coordinateBlock L W γ * C *
      Gauss.coordinateBlock L W γ) =
    Matrix.trace (A.submatrix (split L W) (split L W) *
      Gauss.coordinateMatrix L W γ * C.submatrix (split L W) (split L W) *
      Gauss.coordinateMatrix L W γ) := by
  let P := A.submatrix (split L W) (split L W)
  let Q := C.submatrix (split L W) (split L W)
  have hA : Gauss.blockRelabel L W P = A := blockRelabel_submatrix_split L W A
  have hC : Gauss.blockRelabel L W Q = C := blockRelabel_submatrix_split L W C
  change Matrix.trace (A * Gauss.blockRelabel L W (Gauss.coordinateMatrix L W γ) *
    C * Gauss.blockRelabel L W (Gauss.coordinateMatrix L W γ)) =
    Matrix.trace (P * Gauss.coordinateMatrix L W γ * Q * Gauss.coordinateMatrix L W γ)
  rw [← hA, ← hC, ← blockRelabel_mul_sameEdge L W,
    ← blockRelabel_mul_sameEdge L W, ← blockRelabel_mul_sameEdge L W]
  exact trace_blockRelabel_sameEdge L W _

/-- Coordinate contraction in block notation, with the physical-site
Gaussian covariance and its exact `W²` normalization. -/
theorem sum_coordinateBlock_trace_pair
    (A C : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    ∑ γ : Gauss.Coord L W,
      (((Gauss.gvar L W γ : ℝ) : ℂ) *
        Matrix.trace (A * Gauss.coordinateBlock L W γ * C *
          Gauss.coordinateBlock L W γ)) =
    (W : ℂ) ^ 2 * ∑ p : Z2 L, ∑ q : Z2 L,
      Matrix.trace (A * Eblk L W p) * SB L p q *
        Matrix.trace (C * Eblk L W q) := by
  simp_rw [trace_coordinateBlock_pair_sameEdge L W]
  rw [Gauss.sum_allCoords_trace_blocks]
  rw [blockRelabel_submatrix_split, blockRelabel_submatrix_split]

end RBM

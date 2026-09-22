/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionSum

/-!
# Unused Gaussian coordinates have zero matrix direction

The finite product includes lower-triangular and imaginary diagonal noise
coordinates. `Xentry` never reads them, so their `coordinateMatrix` is zero.
-/

namespace RBM.Gauss

open Matrix Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The imaginary diagonal coordinate is unused by the Hermitian model. -/
theorem coordinateMatrix_diag_imag_zero (i : Idx L W) :
    coordinateMatrix L W (i, i, false) = 0 := by
  ext k l
  change Xentry L W (Pi.single (i, i, false) (1 : ℝ)) k l = 0
  unfold Xentry
  split_ifs with hkl hlk
  · have hn : (k, l, false) ≠ (i, i, false) := by
      intro he
      have hk : k = i := congrArg Prod.fst he
      have hl : l = i := congrArg (fun p => p.2.1) he
      exact (lt_irrefl _) (hk.symm ▸ hl.symm ▸ hkl)
    simp [Pi.single_eq_of_ne hn]
  · have hn : (l, k, false) ≠ (i, i, false) := by
      intro he
      have hl : l = i := congrArg Prod.fst he
      have hk : k = i := congrArg (fun p => p.2.1) he
      exact (lt_irrefl _) (hl.symm ▸ hk.symm ▸ hlk)
    simp [Pi.single_eq_of_ne hn]
  · simp

/-- A lower-triangular coordinate is unused: the model always reads the
oppositely ordered coordinate of the Hermitian pair. -/
theorem coordinateMatrix_lower_zero {i j : Idx L W}
    (hji : idxKey L W j < idxKey L W i) (b : Bool) :
    coordinateMatrix L W (i, j, b) = 0 := by
  ext k l
  change Xentry L W (Pi.single (i, j, b) (1 : ℝ)) k l = 0
  unfold Xentry
  split_ifs with hkl hlk
  · have hn (t : Bool) : (k, l, t) ≠ (i, j, b) := by
      intro he
      have hk : k = i := congrArg Prod.fst he
      have hl : l = j := congrArg (fun p => p.2.1) he
      have hij : idxKey L W i < idxKey L W j := hk.symm ▸ hl.symm ▸ hkl
      exact (not_lt_of_ge (le_of_lt hji)) hij
    simp [Pi.single_eq_of_ne (hn true), Pi.single_eq_of_ne (hn false)]
  · have hn (t : Bool) : (l, k, t) ≠ (i, j, b) := by
      intro he
      have hl : l = i := congrArg Prod.fst he
      have hk : k = j := congrArg (fun p => p.2.1) he
      have hij : idxKey L W i < idxKey L W j := hl.symm ▸ hk.symm ▸ hlk
      exact (not_lt_of_ge (le_of_lt hji)) hij
    simp [Pi.single_eq_of_ne (hn true), Pi.single_eq_of_ne (hn false)]
  · have hn : (k, l, true) ≠ (i, j, b) := by
      intro he
      have hk : k = i := congrArg Prod.fst he
      have hl : l = j := congrArg (fun p => p.2.1) he
      have h : idxKey L W l < idxKey L W k := hl ▸ hk ▸ hji
      exact hlk h
    simp [Pi.single_eq_of_ne hn]

/-- Every product coordinate omitted from `usedCoords` has zero derivative
direction in `Xmat`. -/
theorem coordinateMatrix_zero_of_not_mem_usedCoords
    (c : Coord L W) (hc : c ∉ usedCoords L W) :
    coordinateMatrix L W c = 0 := by
  rcases c with ⟨i, j, b⟩
  have hnot : ¬(idxKey L W i < idxKey L W j ∨
      (i = j ∧ b = true)) := by
    simpa [usedCoords] using hc
  rcases idxKey_lt_or_eq_or_lt L W i j with h | h | h
  · exact False.elim (hnot (Or.inl h))
  · subst j
    cases b with
    | false => exact coordinateMatrix_diag_imag_zero L W i
    | true => exact False.elim (hnot (Or.inr ⟨rfl, rfl⟩))
  · exact coordinateMatrix_lower_zero L W h b

/-- The full finite product coordinate contraction equals the contraction
over the coordinates read by `Xmat`; every omitted summand vanishes. -/
theorem sum_allCoords_trace_eq_usedCoords
    (A C : Matrix (Idx L W) (Idx L W) ℂ) :
    ∑ c : Coord L W,
        (((gvar L W c : ℝ) : ℂ) *
          Matrix.trace (A * coordinateMatrix L W c * C * coordinateMatrix L W c)) =
      ∑ c ∈ usedCoords L W,
        (((gvar L W c : ℝ) : ℂ) *
          Matrix.trace (A * coordinateMatrix L W c * C * coordinateMatrix L W c)) := by
  classical
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro c _ hc
  rw [coordinateMatrix_zero_of_not_mem_usedCoords L W c hc]
  simp

/-- Full product-coordinate contraction in the two-dimensional block
variables. The remaining generator proof must identify its derivative terms
with this matrix trace pattern. -/
theorem sum_allCoords_trace_blocks
    (A C : Matrix (Idx L W) (Idx L W) ℂ) :
    ∑ c : Coord L W,
        (((gvar L W c : ℝ) : ℂ) *
          Matrix.trace (A * coordinateMatrix L W c * C * coordinateMatrix L W c)) =
      (W : ℂ) ^ 2 * ∑ a : Z2 L, ∑ b : Z2 L,
        Matrix.trace (blockRelabel L W A * Eblk L W a) * SB L a b *
          Matrix.trace (blockRelabel L W C * Eblk L W b) := by
  rw [sum_allCoords_trace_eq_usedCoords, sum_usedCoords_trace_blocks]

end RBM.Gauss

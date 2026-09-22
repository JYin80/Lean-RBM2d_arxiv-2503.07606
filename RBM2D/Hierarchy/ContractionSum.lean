/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionDirections

/-!
# Sum of the Gaussian coordinate contractions

The pairwise real, imaginary, and diagonal contractions are summed over the
coordinates actually used by the finite Hermitian Gaussian model.
-/

namespace RBM

open Matrix Finset

/-- An upper-triangular sum, with its transposed term, plus the diagonal is
the full ordered-pair sum. The key is injective, so its order chooses exactly
one orientation of every distinct pair. -/
private theorem sum_orderedPairs_from_upper
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (key : ι → ℕ) (hkey : Function.Injective key)
    (S : ι → ι → ℂ) (hS : ∀ i j, S i j = S j i)
    (f : ι → ι → ℂ) :
    ∑ i : ι, ∑ j : ι,
      (if key i < key j then S i j * (f i j + f j i)
       else if i = j then S i i * f i i else 0) =
      ∑ i : ι, ∑ j : ι, S i j * f i j := by
  classical
  have point (i j : ι) : S i j * f i j =
      (if key i < key j then S i j * f i j else 0) +
      (if i = j then S i i * f i i else 0) +
      (if key j < key i then S i j * f i j else 0) := by
    rcases lt_trichotomy (key i) (key j) with h | h | h
    · have hij : i ≠ j := by
        intro he
        subst j
        exact (lt_irrefl _) h
      simp [h, hij, not_lt_of_ge (le_of_lt h)]
    · have hij : i = j := hkey h
      subst j
      simp
    · have hij : i ≠ j := by
        intro he
        subst j
        exact (lt_irrefl _) h
      simp [h, hij, not_lt_of_ge (le_of_lt h)]
  have hswap :
      (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f j i else 0) =
      (∑ i : ι, ∑ j : ι, if key j < key i then S i j * f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hS]
  calc
    (∑ i : ι, ∑ j : ι,
      (if key i < key j then S i j * (f i j + f j i)
       else if i = j then S i i * f i i else 0)) =
        (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f i j else 0) +
        (∑ i : ι, ∑ j : ι, if i = j then S i i * f i i else 0) +
        (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f j i else 0) := by
          simp_rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          by_cases hij : key i < key j
          · have hne : i ≠ j := by
              intro he
              subst j
              exact (lt_irrefl _) hij
            simp [hij, hne, mul_add]
          · simp [hij]
    _ = (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f i j else 0) +
        (∑ i : ι, ∑ j : ι, if i = j then S i i * f i i else 0) +
        (∑ i : ι, ∑ j : ι, if key j < key i then S i j * f i j else 0) := by
          rw [hswap]
    _ = ∑ i : ι, ∑ j : ι, S i j * f i j := by
          symm
          calc
            (∑ i : ι, ∑ j : ι, S i j * f i j) =
                ∑ i : ι, ∑ j : ι,
                  ((if key i < key j then S i j * f i j else 0) +
                   (if i = j then S i i * f i i else 0) +
                   (if key j < key i then S i j * f i j else 0)) := by
                    refine Finset.sum_congr rfl fun i _ =>
                      Finset.sum_congr rfl fun j _ => point i j
            _ = _ := by simp only [Finset.sum_add_distrib]

namespace Gauss

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Exactly the independent coordinates read by `Xentry`: both tags for each
oriented off-diagonal pair, and the real tag on the diagonal. -/
noncomputable def usedCoords : Finset (Coord L W) := by
  classical
  exact Finset.univ.filter fun c =>
    idxKey L W c.1 < idxKey L W c.2.1 ∨
      (c.1 = c.2.1 ∧ c.2.2 = true)

/-- Summing the actual coordinate trace contractions gives the complete
ordered-pair diagonal contraction with the paper's site covariance. -/
theorem sum_usedCoords_trace
    (A C : Matrix (Idx L W) (Idx L W) ℂ) :
    ∑ c ∈ usedCoords L W,
        (((gvar L W c : ℝ) : ℂ) *
          Matrix.trace (A * coordinateMatrix L W c * C * coordinateMatrix L W c)) =
      ∑ i : Idx L W, ∑ j : Idx L W,
        Spaper L W i j * (A i i * C j j) := by
  classical
  have splitCoord (f : Coord L W → ℂ) :
      ∑ c : Coord L W, f c =
        ∑ i : Idx L W, ∑ j : Idx L W, ∑ b : Bool, f (i, j, b) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    exact Fintype.sum_prod_type (fun jb : Idx L W × Bool => f (i, jb))
  unfold usedCoords
  rw [Finset.sum_filter, splitCoord]
  calc
    (∑ i : Idx L W, ∑ j : Idx L W, ∑ b : Bool,
      if idxKey L W i < idxKey L W j ∨ (i = j ∧ b = true) then
        (((gvar L W (i, j, b) : ℝ) : ℂ) *
          Matrix.trace (A * coordinateMatrix L W (i, j, b) * C *
            coordinateMatrix L W (i, j, b))) else 0) =
      ∑ i : Idx L W, ∑ j : Idx L W,
        (if idxKey L W i < idxKey L W j then
          Spaper L W i j * (A i i * C j j + A j j * C i i)
         else if i = j then Spaper L W i i * (A i i * C i i) else 0) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rcases idxKey_lt_or_eq_or_lt L W i j with h | h | h
        · have hne : i ≠ j := by
            intro he
            subst j
            exact (lt_irrefl _) h
          simp only [h, true_or, ite_true, Fintype.sum_bool]
          simp [weighted_trace_coordinate_offDiag L W A C h]
        · subst j
          simp only [lt_irrefl, false_or, true_and,
            Fintype.sum_bool, ite_true, ite_false]
          simpa using weighted_trace_coordinate_diag L W A C i
        · have hne : i ≠ j := by
            intro he
            subst j
            exact (lt_irrefl _) h
          have hrev : ¬ idxKey L W i < idxKey L W j := not_lt_of_ge (le_of_lt h)
          simp [hrev, hne]
    _ = ∑ i : Idx L W, ∑ j : Idx L W,
          Spaper L W i j * (A i i * C j j) := by
        apply sum_orderedPairs_from_upper (idxKey L W) (idxKey_injective L W)
          (Spaper L W) _ (fun i j => A i i * C j j)
        intro i j
        have h := congrFun (congrFun (Spaper_transpose L W) j) i
        simpa only [Matrix.transpose_apply, Matrix.of_apply] using h

/-- Relabel a physical-site matrix by the block/offset equivalence. -/
noncomputable def blockRelabel
    (A : Matrix (Idx L W) (Idx L W) ℂ) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  A.submatrix (splitEquiv L W).symm (splitEquiv L W).symm

theorem blockRelabel_apply_split
    (A : Matrix (Idx L W) (Idx L W) ℂ) (i j : Idx L W) :
    blockRelabel L W A (split L W i) (split L W j) = A i j := by
  change A ((splitEquiv L W).symm ((splitEquiv L W) i))
    ((splitEquiv L W).symm ((splitEquiv L W) j)) = A i j
  simp

/-- The physical-site diagonal contraction is the same sum in block/offset
coordinates. -/
theorem sum_Spaper_diag_mul_relabel
    (A C : Matrix (Idx L W) (Idx L W) ℂ) :
    (∑ i : Idx L W, ∑ j : Idx L W,
      Spaper L W i j * (A i i * C j j)) =
      ∑ u : BlockIndex L W, ∑ v : BlockIndex L W,
        Svar L W u v *
          (blockRelabel L W A u u * blockRelabel L W C v v) := by
  let e := splitEquiv L W
  calc
    (∑ i : Idx L W, ∑ j : Idx L W,
      Spaper L W i j * (A i i * C j j)) =
        ∑ i : Idx L W, ∑ v : BlockIndex L W,
          Svar L W (e i) v *
            (blockRelabel L W A (e i) (e i) * blockRelabel L W C v v) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              exact Fintype.sum_equiv e _ _ (fun j => by
                change Svar L W (e i) (e j) * (A i i * C j j) =
                  Svar L W (e i) (e j) *
                    (blockRelabel L W A (e i) (e i) *
                      blockRelabel L W C (e j) (e j))
                rw [← blockRelabel_apply_split L W A i i,
                  ← blockRelabel_apply_split L W C j j]
                rfl)
    _ = ∑ u : BlockIndex L W, ∑ v : BlockIndex L W,
          Svar L W u v *
            (blockRelabel L W A u u * blockRelabel L W C v v) := by
              exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- Full coordinate contraction in the paper's block variables, with the
dimension-correct `W²` coefficient. This is a matrix identity for arbitrary
`A,C`; it does not assert a generator or loop derivative identity. -/
theorem sum_usedCoords_trace_blocks
    (A C : Matrix (Idx L W) (Idx L W) ℂ) :
    ∑ c ∈ usedCoords L W,
        (((gvar L W c : ℝ) : ℂ) *
          Matrix.trace (A * coordinateMatrix L W c * C * coordinateMatrix L W c)) =
      (W : ℂ) ^ 2 * ∑ a : Z2 L, ∑ b : Z2 L,
        Matrix.trace (blockRelabel L W A * Eblk L W a) * SB L a b *
          Matrix.trace (blockRelabel L W C * Eblk L W b) := by
  rw [sum_usedCoords_trace, sum_Spaper_diag_mul_relabel]
  exact sum_Svar_diag_mul L W (blockRelabel L W A) (blockRelabel L W C)

end Gauss

end RBM

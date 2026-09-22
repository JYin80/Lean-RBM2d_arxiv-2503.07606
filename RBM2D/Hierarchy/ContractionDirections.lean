/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionBasic
import RBM2D.Gauss.Model

/-!
# Hermitian coordinate directions in the loop contraction

The directions here are the actual coordinate matrices of the finite product
Gaussian model. An oriented off-diagonal pair has independent real and
imaginary coordinates, each of variance `svar/2`; the diagonal has one used
real coordinate of variance `svar`. Their trace contractions leave precisely
the diagonal-entry terms needed by the block collapse theorem.
-/

namespace RBM.Gauss

open Matrix

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The real coordinate matrix for an oriented off-diagonal pair. -/
theorem coordinateMatrix_real_eq {i j : Idx L W}
    (hij : idxKey L W i < idxKey L W j) :
    coordinateMatrix L W (i, j, true) =
      Matrix.single i j 1 + Matrix.single j i 1 := by
  ext k l
  by_cases h₁ : k = i ∧ l = j
  · rcases h₁ with ⟨rfl, rfl⟩
    have hne : k ≠ l := by
      intro he
      subst l
      exact (lt_irrefl _) hij
    simp [coordinateMatrix_apply, Xentry, hij, hne]
  · by_cases h₂ : k = j ∧ l = i
    · rcases h₂ with ⟨rfl, rfl⟩
      have hne : k ≠ l := by
        intro he
        subst l
        exact (lt_irrefl _) hij
      have hrev : ¬ idxKey L W k < idxKey L W l := not_lt_of_ge (le_of_lt hij)
      simp [coordinateMatrix_apply, Xentry, hij, hrev, hne]
    · have hn₁ : (k, l, true) ≠ (i, j, true) := by
        intro he
        exact h₁ ⟨congrArg Prod.fst he, congrArg (fun p => p.2.1) he⟩
      have hn₂ : (l, k, true) ≠ (i, j, true) := by
        intro he
        exact h₂ ⟨congrArg (fun p => p.2.1) he, congrArg Prod.fst he⟩
      have hr₁ : ¬(i = k ∧ j = l) := by
        rintro ⟨rfl, rfl⟩
        exact h₁ ⟨rfl, rfl⟩
      have hr₂ : ¬(j = k ∧ i = l) := by
        rintro ⟨rfl, rfl⟩
        exact h₂ ⟨rfl, rfl⟩
      simp [coordinateMatrix_apply, Xentry, hr₁, hr₂, hn₁, hn₂]

/-- The imaginary coordinate matrix for an oriented off-diagonal pair. -/
theorem coordinateMatrix_imag_eq {i j : Idx L W}
    (hij : idxKey L W i < idxKey L W j) :
    coordinateMatrix L W (i, j, false) =
      Matrix.single i j Complex.I + Matrix.single j i (-Complex.I) := by
  ext k l
  by_cases h₁ : k = i ∧ l = j
  · rcases h₁ with ⟨rfl, rfl⟩
    have hne : k ≠ l := by
      intro he
      subst l
      exact (lt_irrefl _) hij
    simp [coordinateMatrix_apply, Xentry, hij, hne]
  · by_cases h₂ : k = j ∧ l = i
    · rcases h₂ with ⟨rfl, rfl⟩
      have hne : k ≠ l := by
        intro he
        subst l
        exact (lt_irrefl _) hij
      have hrev : ¬ idxKey L W k < idxKey L W l := not_lt_of_ge (le_of_lt hij)
      simp [coordinateMatrix_apply, Xentry, hij, hrev, hne]
    · have hn₁ : (k, l, false) ≠ (i, j, false) := by
        intro he
        exact h₁ ⟨congrArg Prod.fst he, congrArg (fun p => p.2.1) he⟩
      have hn₂ : (l, k, false) ≠ (i, j, false) := by
        intro he
        exact h₂ ⟨congrArg (fun p => p.2.1) he, congrArg Prod.fst he⟩
      have hr₁ : ¬(i = k ∧ j = l) := by
        rintro ⟨rfl, rfl⟩
        exact h₁ ⟨rfl, rfl⟩
      have hr₂ : ¬(j = k ∧ i = l) := by
        rintro ⟨rfl, rfl⟩
        exact h₂ ⟨rfl, rfl⟩
      simp [coordinateMatrix_apply, Xentry, hr₁, hr₂, hn₁, hn₂]

/-- Only the real diagonal coordinate acts on a diagonal matrix entry. -/
theorem coordinateMatrix_diag_eq (i : Idx L W) :
    coordinateMatrix L W (i, i, true) = Matrix.single i i 1 := by
  ext k l
  by_cases h : k = i ∧ l = i
  · rcases h with ⟨rfl, rfl⟩
    simp [coordinateMatrix_apply, Xentry]
  · have hn₁ : (k, l, true) ≠ (i, i, true) := by
      intro he
      exact h ⟨congrArg Prod.fst he, congrArg (fun p => p.2.1) he⟩
    have hn₂ : (l, k, true) ≠ (i, i, true) := by
      intro he
      exact h ⟨congrArg (fun p => p.2.1) he, congrArg Prod.fst he⟩
    have hr : ¬(i = k ∧ i = l) := by
      rintro ⟨rfl, rfl⟩
      exact h ⟨rfl, rfl⟩
    simp [coordinateMatrix_apply, Xentry, hr, hn₁, hn₂]

/-- The real coordinate contributes four elementary trace contractions. -/
theorem trace_coordinate_real (A C : Matrix (Idx L W) (Idx L W) ℂ)
    {i j : Idx L W} (hij : idxKey L W i < idxKey L W j) :
    Matrix.trace (A * coordinateMatrix L W (i, j, true) * C *
        coordinateMatrix L W (i, j, true)) =
      A j i * C j i + A i i * C j j + A j j * C i i + A i j * C i j := by
  rw [coordinateMatrix_real_eq L W hij]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add,
    trace_mul_single_mul_single]
  ring

/-- The imaginary coordinate cancels the same-orientation terms. -/
theorem trace_coordinate_imag (A C : Matrix (Idx L W) (Idx L W) ℂ)
    {i j : Idx L W} (hij : idxKey L W i < idxKey L W j) :
    Matrix.trace (A * coordinateMatrix L W (i, j, false) * C *
        coordinateMatrix L W (i, j, false)) =
      -(A j i * C j i) + A i i * C j j + A j j * C i i - A i j * C i j := by
  rw [coordinateMatrix_imag_eq L W hij]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add,
    trace_mul_single_mul_single]
  linear_combination
    (A j i * C j i - A i i * C j j - A j j * C i i + A i j * C i j) *
      Complex.I_mul_I

/-- The diagonal real coordinate contributes one diagonal product. -/
theorem trace_coordinate_diag (A C : Matrix (Idx L W) (Idx L W) ℂ)
    (i : Idx L W) :
    Matrix.trace (A * coordinateMatrix L W (i, i, true) * C *
        coordinateMatrix L W (i, i, true)) = A i i * C i i := by
  rw [coordinateMatrix_diag_eq L W i, trace_mul_single_mul_single]
  norm_num

/-- The two independent off-diagonal Gaussian coordinates have variance
`Spaper_ij/2` each. Their weighted trace contractions leave the two diagonal
products, with exactly one factor of the site variance `Spaper_ij`. -/
theorem weighted_trace_coordinate_offDiag
    (A C : Matrix (Idx L W) (Idx L W) ℂ)
    {i j : Idx L W} (hij : idxKey L W i < idxKey L W j) :
    (((gvar L W (i, j, true) : ℝ) : ℂ) *
        Matrix.trace (A * coordinateMatrix L W (i, j, true) * C *
          coordinateMatrix L W (i, j, true))) +
      (((gvar L W (i, j, false) : ℝ) : ℂ) *
        Matrix.trace (A * coordinateMatrix L W (i, j, false) * C *
          coordinateMatrix L W (i, j, false))) =
      Spaper L W i j * (A i i * C j j + A j j * C i i) := by
  have hne : i ≠ j := by
    intro he
    subst j
    exact (lt_irrefl _) hij
  have hv (b : Bool) : (((gvar L W (i, j, b) : ℝ) : ℂ)) =
      (svar L W i j : ℂ) / 2 := by
    have hr := gvar_offDiag L W i j b hne
    exact_mod_cast hr
  rw [trace_coordinate_real L W A C hij,
    trace_coordinate_imag L W A C hij, hv true, hv false,
    ← svar_cast_eq_Spaper L W i j]
  ring

/-- The same contraction with its two-dimensional block normalization shown
explicitly: each physical-site variance is `SB_ab W⁻²`. -/
theorem weighted_trace_coordinate_offDiag_blocks
    (A C : Matrix (Idx L W) (Idx L W) ℂ)
    {i j : Idx L W} (hij : idxKey L W i < idxKey L W j) :
    (((gvar L W (i, j, true) : ℝ) : ℂ) *
        Matrix.trace (A * coordinateMatrix L W (i, j, true) * C *
          coordinateMatrix L W (i, j, true))) +
      (((gvar L W (i, j, false) : ℝ) : ℂ) *
        Matrix.trace (A * coordinateMatrix L W (i, j, false) * C *
          coordinateMatrix L W (i, j, false))) =
      (SB L (split L W i).1 (split L W j).1 * (W : ℂ)⁻¹ ^ 2) *
        (A i i * C j j + A j j * C i i) := by
  rw [weighted_trace_coordinate_offDiag L W A C hij]
  rw [Spaper_eq]
  rfl

/-- The single used diagonal Gaussian coordinate has the full site variance. -/
theorem weighted_trace_coordinate_diag
    (A C : Matrix (Idx L W) (Idx L W) ℂ) (i : Idx L W) :
    (((gvar L W (i, i, true) : ℝ) : ℂ) *
      Matrix.trace (A * coordinateMatrix L W (i, i, true) * C *
        coordinateMatrix L W (i, i, true))) =
      Spaper L W i i * (A i i * C i i) := by
  rw [trace_coordinate_diag L W A C i, gvar_diag,
    ← svar_cast_eq_Spaper L W i i]

end RBM.Gauss

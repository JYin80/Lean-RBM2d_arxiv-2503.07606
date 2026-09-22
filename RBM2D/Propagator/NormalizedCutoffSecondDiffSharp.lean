/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedCutoffAffineRemainder

/-!
# Sharp normalized-cutoff second differences

The second difference has a quadratic affine contribution and an explicit
first-order defect at a fold of the cycle distance. Away from folds the
defect vanishes. This does not include the dyadic shell summation.
-/

namespace RBM

/-- First-coordinate three-point cutoff bound, with the antipodal fold
defect kept explicit. -/
theorem abs_normalizedDyadicCutoff_second_diff_e1_sharp_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q r : Z2 L) (j : ℕ)
    (ρ : ℝ) (hq : q = p + (1, 0)) (hr : r = q + (1, 0))
    (hρ : 0 < ρ) (hmiddle : ρ ≤ normalizedFrequency L q) :
    |normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| ≤
      420 * (2 : ℝ) ^ j *
        (|pstarFoldDefect L p.1| / (2 * Real.pi)) +
      (420 * (2 : ℝ) ^ j / ρ +
        2100 * ((2 : ℝ) ^ j) ^ 2) * (1 / (L : ℝ)) ^ 2 := by
  have hfold := abs_normalizedDyadicCutoff_second_diff_e1_fold_le
    L p q r j hq hr
  have haff := abs_affine_cutoff_remainder_e1_quadratic_le
    L hL p q j ρ hq hρ hmiddle
  exact hfold.trans (add_le_add_right haff _)

/-- The symmetric second-coordinate estimate. -/
theorem abs_normalizedDyadicCutoff_second_diff_e2_sharp_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q r : Z2 L) (j : ℕ)
    (ρ : ℝ) (hq : q = p + (0, 1)) (hr : r = q + (0, 1))
    (hρ : 0 < ρ) (hmiddle : ρ ≤ normalizedFrequency L q) :
    |normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| ≤
      420 * (2 : ℝ) ^ j *
        (|pstarFoldDefect L p.2| / (2 * Real.pi)) +
      (420 * (2 : ℝ) ^ j / ρ +
        2100 * ((2 : ℝ) ^ j) ^ 2) * (1 / (L : ℝ)) ^ 2 := by
  have hfold := abs_normalizedDyadicCutoff_second_diff_e2_fold_le
    L p q r j hq hr
  have haff := abs_affine_cutoff_remainder_e2_quadratic_le
    L hL p q j ρ hq hρ hmiddle
  exact hfold.trans (add_le_add_right haff _)

/-- Without a first-coordinate fold, only the quadratic term remains. -/
theorem abs_normalizedDyadicCutoff_second_diff_e1_noFold_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q r : Z2 L) (j : ℕ)
    (ρ : ℝ) (hq : q = p + (1, 0)) (hr : r = q + (1, 0))
    (hρ : 0 < ρ) (hmiddle : ρ ≤ normalizedFrequency L q)
    (hnoFold : noFoldTwo L p.1) :
    |normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| ≤
      (420 * (2 : ℝ) ^ j / ρ +
        2100 * ((2 : ℝ) ^ j) ^ 2) * (1 / (L : ℝ)) ^ 2 := by
  have h := abs_normalizedDyadicCutoff_second_diff_e1_sharp_le
    L hL p q r j ρ hq hr hρ hmiddle
  rw [pstarFoldDefect_eq_zero_of_noFoldTwo L p.1 hnoFold] at h
  simpa using h

/-- Without a second-coordinate fold, only the quadratic term remains. -/
theorem abs_normalizedDyadicCutoff_second_diff_e2_noFold_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q r : Z2 L) (j : ℕ)
    (ρ : ℝ) (hq : q = p + (0, 1)) (hr : r = q + (0, 1))
    (hρ : 0 < ρ) (hmiddle : ρ ≤ normalizedFrequency L q)
    (hnoFold : noFoldTwo L p.2) :
    |normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| ≤
      (420 * (2 : ℝ) ^ j / ρ +
        2100 * ((2 : ℝ) ^ j) ^ 2) * (1 / (L : ℝ)) ^ 2 := by
  have h := abs_normalizedDyadicCutoff_second_diff_e2_sharp_le
    L hL p q r j ρ hq hr hρ hmiddle
  rw [pstarFoldDefect_eq_zero_of_noFoldTwo L p.2 hnoFold] at h
  simpa using h

/-- A nonzero lattice path meets both the positive-radius and no-fold
hypotheses. -/
example :
    |normalizedDyadicCutoff 8 2 ((3, 0) : Z2 8) -
        2 * normalizedDyadicCutoff 8 2 ((2, 0) : Z2 8) +
        normalizedDyadicCutoff 8 2 ((1, 0) : Z2 8)| ≤
      (420 * (2 : ℝ) ^ 2 / (1 / 4 : ℝ) +
        2100 * ((2 : ℝ) ^ 2) ^ 2) * (1 / (8 : ℝ)) ^ 2 := by
  have hz : zdist 8 (2 : ZMod 8) = 2 := by decide
  have hrad : pstar2 8 ((2, 0) : Z2 8) = (Real.pi / 2) ^ 2 := by
    simp only [pstar2, pstar, hz, zdist_zero, Nat.cast_ofNat,
      Nat.cast_zero, mul_zero, zero_div]
    ring
  have hν : normalizedFrequency 8 ((2, 0) : Z2 8) = 1 / 4 := by
    rw [normalizedFrequency, hrad, Real.sqrt_sq_eq_abs,
      abs_of_pos (by positivity : 0 < Real.pi / 2)]
    field_simp [Real.pi_ne_zero]
    ring
  apply abs_normalizedDyadicCutoff_second_diff_e1_noFold_le
    8 (by norm_num) ((1, 0) : Z2 8) ((2, 0) : Z2 8)
    ((3, 0) : Z2 8) 2 (1 / 4 : ℝ)
  · rfl
  · rfl
  · norm_num
  · rw [hν]
  · left
    decide

end RBM

#print axioms RBM.abs_normalizedDyadicCutoff_second_diff_e1_sharp_le
#print axioms RBM.abs_normalizedDyadicCutoff_second_diff_e2_sharp_le
#print axioms RBM.abs_normalizedDyadicCutoff_second_diff_e1_noFold_le
#print axioms RBM.abs_normalizedDyadicCutoff_second_diff_e2_noFold_le
